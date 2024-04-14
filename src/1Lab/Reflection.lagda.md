<!--
```agda
open import 1Lab.Type.Sigma
open import 1Lab.Path
open import 1Lab.Type hiding (absurd)

open import Data.Product.NAry
open import Data.String.Show
open import Data.List.Base
open import Data.Dec.Base
open import Data.Vec.Base
open import Data.Bool

open import Meta.Append
```
-->

```agda
module 1Lab.Reflection where

open import Data.String.Base public
open import Meta.Traversable public
open import Data.Float.Base public
open import Data.Maybe.Base public
open import Data.Word.Base public
open import Meta.Idiom public
open import Meta.Bind public
open import Meta.Alt public

open Data.Product.NAry using ([_]) public
open Data.List.Base hiding (lookup ; tabulate) public
open Data.Vec.Base using (Vec ; [] ; _∷_ ; lookup ; tabulate) public
open Data.Dec.Base public
open Data.Bool public

open import Data.Reflection.Fixity   public
open import Data.Reflection.Name     public
open import Data.Reflection.Meta     public
open import Data.Reflection.Argument public
open import Data.Reflection.Abs      public
open import Data.Reflection.Literal  public
open import Data.Reflection.Term     public
open import Data.Reflection.Error    public
```

## The TC monad

To drive meta computations, we have the TC monad, reflecting Agda's
`TCM` monad.

```agda
private module P where
  postulate
    TC                : ∀ {a} → Type a → Type a
    returnTC          : ∀ {a} {A : Type a} → A → TC A
    bindTC            : ∀ {a b} {A : Type a} {B : Type b} → TC A → (A → TC B) → TC B
    unify             : Term → Term → TC ⊤
    infer-type        : Term → TC Term
    check-type        : Term → Term → TC Term
    normalise         : Term → TC Term
    reduce            : Term → TC Term
    catchTC           : ∀ {a} {A : Type a} → TC A → TC A → TC A
    quoteTC           : ∀ {a} {A : Type a} → A → TC Term
    unquoteTC         : ∀ {a} {A : Type a} → Term → TC A
    quoteωTC          : ∀ {A : Typeω} → A → TC Term
    getContext        : TC Telescope
    extend-context    : ∀ {a} {A : Type a} → String → Arg Term → TC A → TC A
    in-context        : ∀ {a} {A : Type a} → Telescope → TC A → TC A
    freshName         : String → TC Name
    declare           : Arg Name → Term → TC ⊤
    declare-postulate : Arg Name → Term → TC ⊤
    define-function   : Name → List Clause → TC ⊤
    get-type          : Name → TC Term
    get-definition    : Name → TC Definition
    blockTC           : ∀ {a} {A : Type a} → Blocker → TC A
    commitTC          : TC ⊤
    isMacro           : Name → TC Bool

    typeError         : ∀ {a} {A : Type a} → List ErrorPart → TC A
    formatErrorParts  : List ErrorPart → TC String
    debugPrint        : String → Nat → List ErrorPart → TC ⊤

  -- If 'true', makes the following primitives also normalise
  -- their results: infer-type, check-type, quoteTC, get-type, and getContext
    withNormalisation : ∀ {a} {A : Type a} → Bool → TC A → TC A
    askNormalisation  : TC Bool

  -- If 'true', makes the following primitives to reconstruct hidden arguments:
  -- get-definition, normalise, reduce, infer-type, check-type and getContext
    withReconstructed : ∀ {a} {A : Type a} → Bool → TC A → TC A
    askReconstructed  : TC Bool

  -- Whether implicit arguments at the end should be turned into metavariables
    withExpandLast : ∀ {a} {A : Type a} → Bool → TC A → TC A
    askExpandLast  : TC Bool

  -- White/blacklist specific definitions for reduction while executing the TC computation
  -- 'true' for whitelist, 'false' for blacklist
    withReduceDefs : ∀ {a} {A : Type a} → (Σ Bool λ _ → List Name) → TC A → TC A
    askReduceDefs  : TC (Σ Bool λ _ → List Name)

  -- Fail if the given computation gives rise to new, unsolved
  -- "blocking" constraints.
    noConstraints : ∀ {a} {A : Type a} → TC A → TC A

  -- Run the given TC action and return the first component. Resets to
  -- the old TC state if the second component is 'false', or keep the
  -- new TC state if it is 'true'.
    run-speculative : ∀ {a} {A : Type a} → TC (Σ A λ _ → Bool) → TC A

  -- Get a list of all possible instance candidates for the given meta
  -- variable (it does not have to be an instance meta).
    get-instances : Meta → TC (List Term)

    declareData      : Name → Nat → Term → TC ⊤
    defineData       : Name → List (Σ Name (λ _ → Term)) → TC ⊤
```

<details>
<summary>And now we bind the whole shebang above to the
`BUILTIN`{.agda}s that Agda knows about.
</summary>

```agda
  {-# BUILTIN AGDATCM                  TC                         #-}
  {-# BUILTIN AGDATCMRETURN            returnTC                   #-}
  {-# BUILTIN AGDATCMBIND              bindTC                     #-}
  {-# BUILTIN AGDATCMUNIFY             unify                      #-}
  {-# BUILTIN AGDATCMTYPEERROR         typeError                  #-}
  {-# BUILTIN AGDATCMINFERTYPE         infer-type                 #-}
  {-# BUILTIN AGDATCMCHECKTYPE         check-type                 #-}
  {-# BUILTIN AGDATCMNORMALISE         normalise                  #-}
  {-# BUILTIN AGDATCMREDUCE            reduce                     #-}
  {-# BUILTIN AGDATCMCATCHERROR        catchTC                    #-}
  {-# BUILTIN AGDATCMQUOTETERM         quoteTC                    #-}
  {-# BUILTIN AGDATCMUNQUOTETERM       unquoteTC                  #-}
  {-# BUILTIN AGDATCMQUOTEOMEGATERM    quoteωTC                   #-}
  {-# BUILTIN AGDATCMGETCONTEXT        getContext                 #-}
  {-# BUILTIN AGDATCMEXTENDCONTEXT     extend-context             #-}
  {-# BUILTIN AGDATCMINCONTEXT         in-context                 #-}
  {-# BUILTIN AGDATCMFRESHNAME         freshName                  #-}
  {-# BUILTIN AGDATCMDECLAREDEF        declare                    #-}
  {-# BUILTIN AGDATCMDECLAREPOSTULATE  declare-postulate          #-}
  {-# BUILTIN AGDATCMDEFINEFUN         define-function            #-}
  {-# BUILTIN AGDATCMGETTYPE           get-type                   #-}
  {-# BUILTIN AGDATCMGETDEFINITION     get-definition             #-}
  {-# BUILTIN AGDATCMBLOCK             blockTC                    #-}
  {-# BUILTIN AGDATCMCOMMIT            commitTC                   #-}
  {-# BUILTIN AGDATCMISMACRO           isMacro                    #-}
  {-# BUILTIN AGDATCMWITHNORMALISATION withNormalisation          #-}
  {-# BUILTIN AGDATCMFORMATERRORPARTS  formatErrorParts           #-}
  {-# BUILTIN AGDATCMDEBUGPRINT        debugPrint                 #-}
  {-# BUILTIN AGDATCMWITHRECONSTRUCTED withReconstructed          #-}
  {-# BUILTIN AGDATCMWITHEXPANDLAST    withExpandLast             #-}
  {-# BUILTIN AGDATCMWITHREDUCEDEFS    withReduceDefs             #-}
  {-# BUILTIN AGDATCMASKNORMALISATION  askNormalisation           #-}
  {-# BUILTIN AGDATCMASKRECONSTRUCTED  askReconstructed           #-}
  {-# BUILTIN AGDATCMASKEXPANDLAST     askExpandLast              #-}
  {-# BUILTIN AGDATCMASKREDUCEDEFS     askReduceDefs              #-}
  {-# BUILTIN AGDATCMNOCONSTRAINTS     noConstraints              #-}
  {-# BUILTIN AGDATCMRUNSPECULATIVE    run-speculative            #-}
  {-# BUILTIN AGDATCMGETINSTANCES      get-instances              #-}
  {-# BUILTIN AGDATCMDECLAREDATA       declareData                #-}
  {-# BUILTIN AGDATCMDEFINEDATA        defineData                 #-}

open P
  hiding ( returnTC ; bindTC ; catchTC )
  public

instance
  Map-TC : Map (eff TC)
  Map-TC .Map.map f x = P.bindTC x λ x → P.returnTC (f x)

  Idiom-TC : Idiom (eff TC)
  Idiom-TC .Idiom.pure = P.returnTC
  Idiom-TC .Idiom._<*>_ f g = P.bindTC f λ f → P.bindTC g λ g → pure (f g)

  Bind-TC : Bind (eff TC)
  Bind-TC .Bind._>>=_ = P.bindTC

  Alt-TC : Alt (eff TC)
  Alt-TC .Alt.fail  = P.typeError mempty
  Alt-TC .Alt._<|>_ = P.catchTC
```
</details>

# Reflection helpers

```agda
Args : Type
Args = List (Arg Term)

Fun : ∀ {ℓ ℓ'} → Type ℓ → Type ℓ' → Type (ℓ ⊔ ℓ')
Fun A B = A → B

idfun : ∀ {ℓ} (A : Type ℓ) → A → A
idfun A x = x

under-abs : ∀ {ℓ} {A : Type ℓ} → Term → TC A → TC A
under-abs (lam v (abs nm _)) m = extend-context nm (arg (arginfo v (modality relevant quantity-ω)) unknown) m
under-abs (pi a (abs nm _))  m = extend-context nm a m
under-abs _ m = m

extend-context* : ∀ {a} {A : Type a} → Telescope → TC A → TC A
extend-context* [] a = a
extend-context* ((nm , tm) ∷ xs) a = extend-context nm tm (extend-context* xs a)

new-meta : Term → TC Term
new-meta ty = do
  mv ← check-type unknown ty
  debugPrint "tactic.meta" 70
    [ "Created new meta " , termErr mv , " of type " , termErr ty ]
  pure mv

new-meta' : Term → TC (Meta × Term)
new-meta' ty = do
  tm@(meta mv _) ← check-type unknown ty
    where _ → typeError "impossible new-meta'"
  debugPrint "tactic.meta" 70
    [ "Created new meta " , termErr tm , " of type " , termErr tm ]
  pure (mv , tm)

block-on-meta : ∀ {a} {A : Type a} → Meta → TC A
block-on-meta m = blockTC (blocker-meta m)

vlam : String → Term → Term
vlam nam body = lam visible (abs nam body)

infer-hidden : Nat → Args → Args
infer-hidden zero    xs = xs
infer-hidden (suc n) xs = unknown h∷ infer-hidden n xs

infer-tel : Telescope → Args
infer-tel tel = (λ (_ , arg ai _) → arg ai unknown) <$> tel

“refl” : Term
“refl” = def (quote refl) []

-- Run a TC computation and reset the state after. If the returned value
-- makes references to metas generated in the reset computation, you'll
-- probably get __IMPOSSIBLE__s!
resetting : ∀ {ℓ} {A : Type ℓ} → TC A → TC A
resetting k = run-speculative ((_, false) <$> k)

all-metas-in : Term → List Blocker
all-metas-in tm = go tm [] where
  go  : Term → List Blocker → List Blocker
  go* : List (Arg Term) → List Blocker → List Blocker

  go (var _ args)             acc = go* args acc
  go (con _ args)             acc = go* args acc
  go (def _ args)             acc = go* args acc
  go (lam _ (abs _ t))        acc = go t acc
  go (pat-lam cs args)        acc = acc
  go (pi (arg _ a) (abs _ b)) acc = go a (go b acc)
  go (agda-sort s)            acc = acc
  go (lit l)                  acc = acc
  go (meta x args)            acc = go* args (blocker-meta x ∷ acc)
  go unknown                  acc = acc

  go* []             acc = acc
  go* (arg _ x ∷ xs) acc = go x (go* xs acc)

wait-for-type : Term → TC Term
wait-for-type tm with all-metas-in tm
... | [] = pure tm
... | it = blockTC (blocker-all it)

wait-just-a-bit : Term → TC Term
wait-just-a-bit (meta m _) = block-on-meta m
wait-just-a-bit tm = pure tm

blocking-meta : Term → Maybe Blocker
blocking-meta* : List (Arg Term) → Maybe Blocker

blocking-meta (var x as)       = nothing
blocking-meta (con c as)       = nothing
blocking-meta (def f as)       = blocking-meta* as
blocking-meta (lam v t)        = nothing
blocking-meta (pat-lam _ as)   = blocking-meta* as
blocking-meta (pi a (abs _ b)) = blocking-meta b
blocking-meta (agda-sort s)    = nothing
blocking-meta (lit l)          = nothing
blocking-meta (meta x _)       = just (blocker-meta x)
blocking-meta unknown          = nothing

blocking-meta* (arg (arginfo visible _)   tm ∷ _) = blocking-meta tm
blocking-meta* (arg (arginfo instance' _) tm ∷ _) = blocking-meta tm
blocking-meta* (arg (arginfo hidden _)    tm ∷ as) = blocking-meta* as

blocking-meta* [] = nothing

reduceB : Term → TC Term
reduceB tm = do
  tm' ← reduce tm
  case blocking-meta tm' of λ where
    (just b) → blockTC b
    nothing  → pure tm'

unapply-path : Term → TC (Maybe (Term × Term × Term))
unapply-path red@(def (quote PathP) (l h∷ T v∷ x v∷ y v∷ [])) = do
  domain ← new-meta (def (quote Type) (l v∷ []))
  ty ← pure (def (quote Path) (domain v∷ x v∷ y v∷ []))
  debugPrint "tactic" 50
    [ "(no reduction) unapply-path: got a "
    , termErr red
    , " but I really want it to be "
    , termErr ty
    ]
  unify red ty
  pure (just (domain , x , y))

unapply-path tm = reduce tm >>= λ where
  tm@(meta _ _) → do
    dom ← new-meta (def (quote Type) (unknown v∷ []))
    l ← new-meta dom
    r ← new-meta dom
    unify tm (def (quote Path) (dom v∷ l v∷ r v∷ []))
    traverse wait-for-type (l ∷ r ∷ [])
    pure (just (dom , l , r))

  red@(def (quote PathP) (l h∷ T v∷ x v∷ y v∷ [])) → do
    domain ← new-meta (def (quote Type) (l v∷ []))
    ty ← pure (def (quote Path) (domain v∷ x v∷ y v∷ []))

    debugPrint "tactic" 50
      [ "unapply-path: got a "
      , termErr red
      , " but I really want it to be "
      , termErr ty
      ]

    unify red ty
    pure (just (domain , x , y))
  _ → pure nothing

get-boundary : Term → TC (Maybe (Term × Term))
get-boundary tm = unapply-path tm >>= λ where
  (just (_ , x , y)) → pure (just (x , y))
  nothing            → pure nothing

instance
  Has-visibility-Telescope : Has-visibility Telescope
  Has-visibility-Telescope .set-visibility v tel = ×-map₂ (set-visibility v) <$> tel
```

## Debugging tools

```agda
debug! : ∀ {ℓ} {A : Type ℓ} → Term → TC A
debug! tm = typeError ("[DEBUG]: " ∷ termErr tm ∷ [])

quote-repr-macro : ∀ {ℓ} {A : Type ℓ} → A → Term →  TC ⊤
quote-repr-macro a hole = do
  tm ← quoteTC a
  repr ← quoteTC tm
  typeError $ "The term\n  "
    ∷ termErr tm
    ∷ "\nHas quoted representation\n  "
    ∷ termErr repr ∷ []

macro
  quote-repr! : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → A → Term → TC ⊤
  quote-repr! a = quote-repr-macro a

unify-loudly : Term → Term → TC ⊤
unify-loudly a b = do
  debugPrint "tactic" 50 $ termErr a ∷ " =? " ∷ termErr b ∷ []
  unify a b
```
