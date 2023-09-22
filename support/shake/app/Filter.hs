{-# LANGUAGE LambdaCase, BlockArguments #-}
{-# HLINT ignore "Avoid lambda" #-}
module Filter
  -- ( Filtering(runFilter)
  -- -- * Managing non-determinism
  -- -- , pick, choose, (>>.), (>.), cut
  -- )
  where

-- We need Agda in this executable for other reasons so we may as well
-- abuse it to avoid reimplementing concatMapM :)
import Agda.Utils.Monad (concatMapM)

import Control.Applicative
import Control.Monad.Trans
import Control.Monad.State
import Control.Category
import Control.Arrow
import Control.Monad
import Control.Lens.Internal.Setter
import Control.Lens

import Data.Foldable
import Data.Monoid
import Data.Maybe

import Text.Show.Pretty

import Prelude hiding (id, (.))
import Data.String

-- | A @'Filter' m a b@ is a non-deterministic computation from values
-- in @a@ to values in @b@, producing effects in @m@. Note that
-- @'Filter' m ≃ 'Kleisli' (ListT m)@, so it fails to be a lawful
-- @'ArrowApply'@ for the same reason that @ListT@ fails to be a monad
-- in general.
newtype Filter m a b = Filter { runFilter_ :: a -> Choose m b }
  deriving (Functor)

newtype Choose m b = Choose { getChoices :: forall r. m r -> (b -> m r -> m r) -> m r }
  deriving (Functor)

runFilter :: Monad m => Filter m a b -> a -> m [b]
runFilter (Filter f) x = choiceList (f x)

choiceList :: Monad m => Choose m b -> m [b]
choiceList (Choose k) = k (pure []) (fmap . (:))

instance Applicative (Choose m) where
  pure x = Choose \nil cons -> cons x nil
  Choose k1 <*> Choose k2 = Choose \nil cons -> k1 nil \f' ret -> k2 nil \x' ret -> cons (f' x') ret

instance Monad (Choose m) where
  Choose k1 >>= f = Choose \nil cons -> k1 nil \x ret -> getChoices (f x) ret cons

instance Alternative (Choose m) where
  empty = Choose const
  Choose k1 <|> Choose k2 = Choose \nil cons -> k1 (k2 nil cons) cons

instance Semigroup (Choose m a) where
  (<>) = (<|>)

instance Monoid (Choose m a) where
  mempty = empty

instance MonadTrans Choose where
  lift k = Choose \nil cons -> k >>= flip cons nil

-- instance (Monad m, Foldable m) => Foldable (Choose m) where
--   foldr f z (Choose k) =
--     let it = k (pure z) (\x xs -> f x <$> xs)
--     in _
-- instance Monad m => Traversable (Choose m) where
--   traverse f (Choose k) = _

traverse' :: (a -> Choose m b) -> Choose m a -> Choose m b
traverse' f (Choose k) = Choose \nil cons -> k nil \x xs -> getChoices (f x) xs cons

sequence' :: Monad m => Choose m b -> Choose m [b]
sequence' m = lift (choiceList m)

filterC :: (a -> Bool) -> Choose m a -> Choose m a
filterC p (Choose k) = Choose \nil cons -> k nil \x xs -> if p x
  then cons x xs
  else xs

fromList :: forall m a. Monad m => [m a] -> Choose m a
fromList xs = Choose (go xs) where
  go :: [m a] -> forall r. m r -> (a -> m r -> m r) -> m r
  go [] nil cons = nil
  go (x:xs) nil cons = x >>= \y -> cons y (go xs nil cons)

instance Category (Filter m) where
  id = Filter pure
  Filter f . Filter g = Filter $ traverse' f . g

instance Arrow (Filter m) where
  arr f = Filter (pure . f)

  first  (Filter f) = Filter \(a, b) -> (,b) <$> f a
  second (Filter f) = Filter \(a, b) -> (a,) <$> f b

  Filter f *** Filter g = Filter \(a, b) -> liftA2 (,) (f a) (g b)

  Filter f &&& Filter g = Filter \x -> liftA2 (,) (f x) (g x)

instance ArrowChoice (Filter m) where
  left (Filter f) = Filter \case
    Left a  -> Left <$> f a
    Right x -> pure $ Right x

  right (Filter f) = Filter \case
    Right a -> Right <$> f a
    Left x  -> pure $ Left x

  Filter f +++ Filter g = Filter \case
    Left a  -> Left  <$> f a
    Right b -> Right <$> g b

  Filter f ||| Filter g = Filter \case
    Left a  -> f a
    Right b -> g b

instance ArrowZero (Filter m) where
  zeroArrow = Filter $ const empty

-- | The @'ArrowPlus' ('Filter' m)@ instance collects the results of
-- both filters.
instance Monad m => ArrowPlus (Filter m) where
  Filter f <+> Filter g = Filter \x -> f x <|> g x

instance Applicative (Filter m a) where
  pure = Filter . pure . pure
  Filter f <*> Filter g = Filter \x -> f x <*> g x

-- | The @'Alternative' ('Filter' m)@ instance performs a “cut search”,
-- where @f <|> g@ will only try @g@ if @f@ produces nothing at all.
instance Alternative (Filter m a) where
  empty = Filter $ const empty

  Filter f <|> Filter g = Filter \x -> Choose \nil cons ->
    getChoices (f x) (getChoices (g x) nil cons) (\x _ -> cons x nil)

instance Monad m => ArrowApply (Filter m) where
  app = Filter \(Filter f, y) -> f y

-- | Non-determnistically explore the values accessed by a @'Fold'@ over the input.
pick :: Applicative m => Fold s a -> Filter m s a
pick l = Filter $ getConst . l (Const . pure)

-- | Choose from a 'Foldable' container, e.g. a list.
explore :: (Applicative m, Alternative f, Foldable f) => Filter m (f a) a
explore = pick (folding id)

nondet :: Monad m => (a -> [b]) -> Filter m a b
nondet f = Filter (fromList . map pure . f)

pures :: Monad m => [b] -> Filter m a b
pures = Filter . const . fromList . map pure

isF :: Applicative m => (a -> Maybe b) -> Filter m a b
isF = Filter . (maybe empty pure .)

-- | @f >>. g@ post-composes @f@ with a function that can 'see' all of
-- @f@'s non-determinstic choices, and may also deliver values
-- nondeterministically.
(>>.) :: Filter m b c -> (Choose m c -> Choose m d) -> Filter m b d
Filter f >>. k = Filter (k . f)

-- | Execute a non-deterministic sub-filter and collect all of its
-- possible results.
collect :: forall m a b. Monad m => Filter m a b -> Filter m a [b]
collect f = f >>. (pure <=< lift . choiceList)

foldF :: forall m a b. (Monad m, Monoid b) => Filter m a b -> Filter m a b
foldF f = f >>. (pure . fold <=< lift . choiceList)

tryF :: forall m a. Filter m a a -> Filter m a a
tryF f = f <|> arr id

-- | Restrict a 'Filter' so that it may return at most one result.
cut :: Filter m a b -> Filter m a b
cut f = f >>. chop

chop :: Choose m b -> Choose m b
chop (Choose k) = Choose \nil cons -> k nil \x _ -> cons x nil

-- | @'guardF' p@ is a filter which only allows through the values for
-- which @p@ is true. Note that @p@ is @'cut'@ so that @'guardF'@ always
-- returns at most one value.
guardF :: Monad m => Filter m a Bool -> Filter m a a
guardF p = (p &&& id) >>. (chop . fmap snd . filterC fst)

broadcast :: Monad m => [Filter m a x] -> Filter m a [x]
broadcast = collect . foldr (<+>) empty

-- | A version of 'guardF' which takes a pure predicate.
filterF :: Monad m => (a -> Bool) -> Filter m a a
filterF = guardF . arr

-- | Given a 'Traversal', lift a @'Filter' m a b@ so that it works over
-- every @a@-valued field in the input.
overF :: forall m s t a b. Monad m => Traversal s t a b -> Filter m a b -> Filter m s t
overF l m = ((nondet (getConst . l (Const . pure)) >>> cut m) >>. sequence' &&& id) >>> arr (uncurry (set (unsafePartsOf l)))

-- | Lift an efectful action to a 'Filtering'.
eff :: Monad m => (a -> m b) -> Filter m a b
eff k = Filter \x -> Choose \nil cons -> k x >>= flip cons nil

eachF :: Monad m => Filter m a b -> Filter m [a] [b]
eachF = Filter . traverse . runFilter_

traceF :: (Show a, MonadIO m) => String -> Filter m a a
traceF msg = eff \x -> x <$ liftIO (putStrLn (msg ++ ": " ++ ppShow x))

build :: (MonadFail m, Show a) => Filter m () a -> m a
build f = runFilter f () >>= \case
  [a] -> pure a
  xs -> fail $ "Filter.build: returned multiple values: " ++ ppShow xs

infixl 8 >>>.
(>>>.) :: Applicative m => Filter m x s -> Fold s a -> Filter m x a
f >>>. l = f >>> pick l

instance IsString a => IsString (Filter m x a) where
  fromString s = Filter \_ -> pure (fromString s)
