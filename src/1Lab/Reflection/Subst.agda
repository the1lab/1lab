open import 1Lab.Reflection
open import 1Lab.Type

open import Prim.Data.Nat

module 1Lab.Reflection.Subst where

{-# NO_UNIVERSE_CHECK #-}
record Impossible : Type where
  field throw-impossible : ∀ {ℓ} {A : Type ℓ} → TC A

open Impossible

impossible : Impossible
impossible .throw-impossible = typeError "The impossible happened!"

data Subst : Type where
  ids        : Subst
  _∷_        : Term → Subst → Subst
  wk         : Nat → Subst → Subst
  lift       : Nat → Subst → Subst
  strengthen : Impossible → Nat → Subst → Subst

infixr 20 _∷_

wkS : Nat → Subst → Subst
wkS zero ρ = ρ
wkS n (wk x ρ) = wk (n + x) ρ
wkS n ρ        = wk n ρ

liftS : Nat → Subst → Subst
liftS zero ρ       = ρ
liftS n ids        = ids
liftS n (lift k ρ) = lift (n + k) ρ
liftS n ρ          = lift n ρ

_++#_ : List Term → Subst → Subst
x ++# ρ = foldr (_∷_) ρ x
infix 15 _++#_

raiseS : Nat → Subst
raiseS n = wk n ids

raise-fromS : Nat → Nat → Subst
raise-fromS n k = liftS n $ raiseS k

singletonS : Nat → Term → Subst
singletonS n u = map (λ i → var i []) (count (n - 1)) ++# u ∷ (raiseS n)
  where
    count : Nat → List Nat
    count zero = []
    count (suc n) = 1 ∷ map suc (count n)

{-# TERMINATING #-}
subst-tm  : Subst → Term → TC Term
subst-tm* : Subst → List (Arg Term) → TC (List (Arg Term))
apply-tm  : Term → Arg Term → TC Term

raise : Nat → Term → TC Term
raise n = subst-tm (raiseS n)

subst-tm* ρ [] = pure []
subst-tm* ρ (arg ι x ∷ ls) = do
  x ← subst-tm ρ x
  (arg ι x ∷_) <$> subst-tm* ρ ls

apply-tm* : Term → List (Arg Term) → TC Term
apply-tm* tm [] = pure tm
apply-tm* tm (x ∷ xs) = do
  tm′ ← apply-tm tm x
  apply-tm* tm′ xs

lookup-tm : (σ : Subst) (i : Nat) → TC Term
lookup-tm ids i = pure $ var i []
lookup-tm (wk n ids) i = pure $ var (i + n) []
lookup-tm (wk n ρ) i = lookup-tm ρ i >>= subst-tm (raiseS n)
lookup-tm (x ∷ ρ) i with (i == 0)
… | true  = pure x
… | false = lookup-tm ρ (i - 1)
lookup-tm (strengthen err n ρ) i with (i < n)
… | true = err .throw-impossible
… | false = lookup-tm ρ (i - n)
lookup-tm (lift n σ) i with (i < n)
… | true  = pure $ var i []
… | false = lookup-tm σ (i - n) >>= raise n

apply-tm (var x args)      argu = pure $ var x (args ++ argu ∷ [])
apply-tm (con c args)      argu = pure $ con c (args ++ argu ∷ [])
apply-tm (def f args)      argu = pure $ def f (args ++ argu ∷ [])
apply-tm (lam v (abs n t)) (arg _ argu) = subst-tm (argu ∷ ids) t
apply-tm (pat-lam cs args) argu = typeError "Unsupported apply pat-lam"
apply-tm (pi a b)          argu = typeError "Type error: apply Π to argument"
apply-tm (agda-sort s)     argu = typeError "Type error: apply sort to argument"
apply-tm (lit l)           argu = typeError "Type error: apply literal to argument"
apply-tm (meta x args)     argu = pure $ meta x (args ++ argu ∷ [])
apply-tm unknown           argu = do
  mv ← new-meta unknown
  apply-tm mv argu

subst-tm ids tm = pure tm
subst-tm ρ (var i args) = do
  r ← lookup-tm ρ i
  es ← subst-tm* ρ args
  apply-tm* r es
subst-tm ρ (con c args)      = con c <$> subst-tm* ρ args
subst-tm ρ (def f args)      = def f <$> subst-tm* ρ args
subst-tm ρ (meta x args)     = meta x <$> subst-tm* ρ args
subst-tm ρ (pat-lam cs args) = typeError $ "Unsupported subst pat-lam"
subst-tm ρ (lam v (abs n b)) = lam v ∘ abs n <$> subst-tm (liftS 1 ρ) b
subst-tm ρ (pi (arg ι a) (abs n b)) = do
  a ← subst-tm ρ a
  b ← subst-tm (liftS 1 ρ) b
  pure (pi (arg ι a) (abs n b))
subst-tm ρ (lit l) = pure (lit l)
subst-tm ρ unknown = pure unknown
subst-tm ρ (agda-sort s) with s
… | set t     = agda-sort ∘ set <$> subst-tm ρ t
… | lit n     = pure (agda-sort (lit n))
… | prop t    = agda-sort ∘ prop <$> subst-tm ρ t
… | propLit n = pure (agda-sort (propLit n))
… | inf n     = pure (agda-sort (inf n))
… | unknown   = pure unknown
