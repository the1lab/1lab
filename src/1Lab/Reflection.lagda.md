<!--
```agda
open import 1Lab.Path
open import 1Lab.Type hiding (absurd)

open import Data.Product.NAry
open import Data.List.Base
open import Data.Vec.Base
open import Data.Dec.Base
open import Data.Bool
```
-->

```agda
module 1Lab.Reflection where

open import Prim.Data.String public
open import Prim.Data.Float public
open import Prim.Data.Maybe public
open import Data.Maybe.Base using (maybe→alt) public
open import Prim.Data.Word public
open import Meta.Traverse public
open import Meta.Idiom public
open import Meta.Bind public
open import Meta.Alt public

open Data.Vec.Base using (Vec ; [] ; _∷_ ; lookup ; tabulate) public
open Data.Product.NAry using ([_]) public
open Data.List.Base public
open Data.Dec.Base public
open Data.Bool public

open import 1Lab.Reflection.Data.Fixity public
open import 1Lab.Reflection.Data.Name public
open import 1Lab.Reflection.Data.Meta public
open import 1Lab.Reflection.Data.Argument public
open import 1Lab.Reflection.Data.Abs public
open import 1Lab.Reflection.Data.Literal public
open import 1Lab.Reflection.Data.Term public
```

## The TC monad

To drive meta computations, we have the TC monad, reflecting Agda's
`TCM` monad.

```agda
postulate
  TC               : ∀ {a} → Type a → Type a
  returnTC         : ∀ {a} {A : Type a} → A → TC A
  bindTC           : ∀ {a b} {A : Type a} {B : Type b} → TC A → (A → TC B) → TC B
  unify            : Term → Term → TC ⊤
  typeError        : ∀ {a} {A : Type a} → List ErrorPart → TC A
  inferType        : Term → TC Term
  checkType        : Term → Term → TC Term
  normalise        : Term → TC Term
  reduce           : Term → TC Term
  catchTC          : ∀ {a} {A : Type a} → TC A → TC A → TC A
  quoteTC          : ∀ {a} {A : Type a} → A → TC Term
  unquoteTC        : ∀ {a} {A : Type a} → Term → TC A
  quoteωTC         : ∀ {A : Typeω} → A → TC Term
  getContext       : TC Telescope
  extendContext    : ∀ {a} {A : Type a} → String → Arg Term → TC A → TC A
  inContext        : ∀ {a} {A : Type a} → Telescope → TC A → TC A
  freshName        : String → TC Name
  declareDef       : Arg Name → Term → TC ⊤
  declarePostulate : Arg Name → Term → TC ⊤
  defineFun        : Name → List Clause → TC ⊤
  getType          : Name → TC Term
  getDefinition    : Name → TC Definition
  blockTC          : ∀ {a} {A : Type a} → Blocker → TC A
  commitTC         : TC ⊤
  isMacro          : Name → TC Bool

  formatErrorParts : List ErrorPart → TC String

  -- Prints the third argument if the corresponding verbosity level is turned
  -- on (with the -v flag to Agda).
  debugPrint : String → Nat → List ErrorPart → TC ⊤

  -- If 'true', makes the following primitives also normalise
  -- their results: inferType, checkType, quoteTC, getType, and getContext
  withNormalisation : ∀ {a} {A : Type a} → Bool → TC A → TC A
  askNormalisation  : TC Bool

  -- If 'true', makes the following primitives to reconstruct hidden arguments:
  -- getDefinition, normalise, reduce, inferType, checkType and getContext
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
  runSpeculative : ∀ {a} {A : Type a} → TC (Σ A λ _ → Bool) → TC A

  -- Get a list of all possible instance candidates for the given meta
  -- variable (it does not have to be an instance meta).
  getInstances : Meta → TC (List Term)

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
{-# BUILTIN AGDATCMINFERTYPE         inferType                  #-}
{-# BUILTIN AGDATCMCHECKTYPE         checkType                  #-}
{-# BUILTIN AGDATCMNORMALISE         normalise                  #-}
{-# BUILTIN AGDATCMREDUCE            reduce                     #-}
{-# BUILTIN AGDATCMCATCHERROR        catchTC                    #-}
{-# BUILTIN AGDATCMQUOTETERM         quoteTC                    #-}
{-# BUILTIN AGDATCMUNQUOTETERM       unquoteTC                  #-}
{-# BUILTIN AGDATCMQUOTEOMEGATERM    quoteωTC                   #-}
{-# BUILTIN AGDATCMGETCONTEXT        getContext                 #-}
{-# BUILTIN AGDATCMEXTENDCONTEXT     extendContext              #-}
{-# BUILTIN AGDATCMINCONTEXT         inContext                  #-}
{-# BUILTIN AGDATCMFRESHNAME         freshName                  #-}
{-# BUILTIN AGDATCMDECLAREDEF        declareDef                 #-}
{-# BUILTIN AGDATCMDECLAREPOSTULATE  declarePostulate           #-}
{-# BUILTIN AGDATCMDEFINEFUN         defineFun                  #-}
{-# BUILTIN AGDATCMGETTYPE           getType                    #-}
{-# BUILTIN AGDATCMGETDEFINITION     getDefinition              #-}
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
{-# BUILTIN AGDATCMRUNSPECULATIVE    runSpeculative             #-}
{-# BUILTIN AGDATCMGETINSTANCES      getInstances               #-}
{-# BUILTIN AGDATCMDECLAREDATA       declareData                #-}
{-# BUILTIN AGDATCMDEFINEDATA        defineData                 #-}

instance
  Map-TC : Map (eff TC)
  Map-TC .Map._<$>_ f x = bindTC x λ x → returnTC (f x)

  Idiom-TC : Idiom (eff TC)
  Idiom-TC .Idiom.pure = returnTC
  Idiom-TC .Idiom._<*>_ f g = bindTC f λ f → bindTC g λ g → pure (f g)

  Bind-TC : Bind (eff TC)
  Bind-TC .Bind._>>=_ = bindTC

  Alt-TC : Alt (eff TC)
  Alt-TC .Alt.fail' xs = typeError [ strErr xs ]
  Alt-TC .Alt._<|>_ = catchTC
```
</details>

# Reflection helpers

```agda
Fun : ∀ {ℓ ℓ'} → Type ℓ → Type ℓ' → Type (ℓ ⊔ ℓ')
Fun A B = A → B

idfun : ∀ {ℓ} (A : Type ℓ) → A → A
idfun A x = x

underAbs : ∀ {ℓ} {A : Type ℓ} → Term → TC A → TC A
underAbs (lam v (abs nm _)) m = extendContext nm (arg (arginfo v (modality relevant quantity-ω)) unknown) m
underAbs (pi a (abs nm _)) m = extendContext nm a m
underAbs _ m = m

new-meta : Term → TC Term
new-meta ty = do
  mv ← checkType unknown ty
  debugPrint "tactic.meta" 70
    [ "Created new meta " , termErr mv , " of type " , termErr ty ]
  pure mv

new-meta' : Term → TC (Meta × Term)
new-meta' ty = do
  tm@(meta mv _) ← checkType unknown ty
    where _ → typeError "impossible new-meta'"
  debugPrint "tactic.meta" 70
    [ "Created new meta " , termErr tm , " of type " , termErr tm ]
  pure (mv , tm)

blockOnMeta   : ∀ {a} {A : Type a} → Meta → TC A
blockOnMeta m = blockTC (blockerMeta m)

vlam : String → Term → Term
vlam nam body = lam visible (abs nam body)

infer-hidden : Nat → List (Arg Term) → List (Arg Term)
infer-hidden zero    xs = xs
infer-hidden (suc n) xs = unknown h∷ infer-hidden n xs

“refl” : Term
“refl” = def (quote refl) []

wait-for-args : List (Arg Term) → TC (List (Arg Term))
wait-for-type : Term → TC Term

wait-for-type (var x args) = var x <$> wait-for-args args
wait-for-type (con c args) = con c <$> wait-for-args args
wait-for-type (def f args) = def f <$> wait-for-args args
wait-for-type (lam v (abs x t)) = pure (lam v (abs x t))
wait-for-type (pat-lam cs args) = pure (pat-lam cs args)
wait-for-type (pi (arg i a) (abs x b)) = do
  a ← wait-for-type a
  b ← wait-for-type b
  pure (pi (arg i a) (abs x b))
wait-for-type (agda-sort s) = pure (agda-sort s)
wait-for-type (lit l) = pure (lit l)
wait-for-type (meta x x₁) = blockOnMeta x
wait-for-type unknown = pure unknown

wait-for-args [] = pure []
wait-for-args (arg i a ∷ xs) = ⦇ ⦇ (arg i) (wait-for-type a) ⦈ ∷ wait-for-args xs ⦈

wait-just-a-bit : Term → TC Term
wait-just-a-bit (meta m _) = blockOnMeta m
wait-just-a-bit tm = pure tm

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
  _ → returnTC nothing

get-boundary : Term → TC (Maybe (Term × Term))
get-boundary tm = unapply-path tm >>= λ where
  (just (_ , x , y)) → pure (just (x , y))
  nothing            → pure nothing
```

## Debugging Tools

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

print-depth : String → Nat → Nat → List ErrorPart → TC ⊤
print-depth key level nesting es = debugPrint key level $
  strErr (nest nesting ("[" <> primShowNat nesting <> "]  ")) ∷ es
  where
    _<>_ : String → String → String
    _<>_ = primStringAppend
    infixr 10 _<>_

    nest : Nat → String → String
    nest zero s = s
    nest (suc x) s = nest x (s <> "  ")
```
