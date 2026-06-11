<!--
```agda
open import 1Lab.Type.Sigma
open import 1Lab.Path
open import 1Lab.Type hiding (absurd)

open import Data.Product.NAry
open import Data.String.Show
open import Data.Bool.Base
open import Data.List.Base
open import Data.Dec.Base
open import Data.Vec.Base

open import Meta.Append
```
-->

```agda
module 1Lab.Reflection where
```

<!--
```agda
open import Data.String.Base public
open import Meta.Traversable public
open import Data.Float.Base public
open import Data.Maybe.Base public
open import Meta.Idiom public
open import Meta.Bind public
open import Meta.Alt public

open Data.Product.NAry using ([_]) public
open Data.List.Base hiding (lookup ; tabulate) public
open Data.Vec.Base using (Vec ; [] ; _∷_ ; lookup ; tabulate) public
open Data.Bool.Base public
open Data.Dec.Base public

open import Data.Reflection.Fixity   public
open import Data.Reflection.Name     public
open import Data.Reflection.Meta     public
open import Data.Reflection.Argument public
open import Data.Reflection.Abs      public
open import Data.Reflection.Literal  public
open import Data.Reflection.Term     public
open import Data.Reflection.Error    public

private variable
  a b c : Level
  A B C : Type a
```
-->

# Metaprogramming facilities

Mikan's metaprogramming facilities work by exposing a number of the
primitives used by the elaborator as user-level definitions which, when
animated through use of the appropriate `BUILTIN` pragmas, allow the
implementation of custom elaborator behaviour for macros and `tactic`
arguments.

<!--
```agda
private module P where
  postulate
```
-->

```agda
    -- A monad of type-checking computations.
    --
    -- The 'returnTC' and 'bindTC' primitives should be used through the
    -- 'Map', 'Idiom' and 'Bind' instances for TC.
    TC       : Type a → Type a
    returnTC : A → TC A
    bindTC   : TC A → (A → TC B) → TC B

    -- Run the first computation; if it fails, run the second
    -- type-checking computation instead.
    --
    -- Changes to the type-checking state performed by the failing
    -- computation are discarded.
    --
    -- This primitive should be accessed by the 'Alt' instance for TC.
    catchTC : TC A → TC A → TC A

    -- Suspend execution of this type-checking computation until the
    -- Blocker is resolved.
    -- When a TC computation blocks, the type-checking state is restored
    -- to the latest snapshot if one was taken by 'commitTC', or to what
    -- the state was when the metaprogram was entered.
    blockTC : Blocker → TC A

    -- Save a snapshot of the type-checking state to be used if the TC
    -- computation suspends on 'blockTC'.
    commitTC  : TC ⊤

    -- Fail if execution of the continuation creates unsolved "blocking"
    -- constraints. The following forms of constraint are considered
    -- "blocking":
    --
    --   * type and term conversion checking
    --
    --   * deferred type-checking problems introduced by the built-in
    --     term elaborator when it can not make progress because a type
    --     is insufficiently instantiated
    --
    --   * checking the definition of a function, which may be blocked
    --     on the type of a pattern.
    noConstraints : TC A → TC A

    -- Throw a type error with the given message.
    typeError : List ErrorPart → TC A

    -- Render an error message to a String value.
    formatErrorParts : List ErrorPart → TC String

    -- Prints the given error message to the debug buffer if the given
    -- verbosity is enabled, i.e. if the user gave (either in the
    -- command line or an OPTIONS pragma) the option `-vkey:N` where `N`
    -- is any number greater than or equal to the required level `L`.
    debugPrint
      : String -- The verbosity `key` to use.
      → Nat    -- The least verbosity level `L` where the message should be printed.
      → List ErrorPart → TC ⊤

    -- Call the conversion checker on the input terms, which must be
    -- inferrable forms.
    -- This can solve metavariables, updating the type-checking state.
    unify : Term → Term → TC ⊤

    -- Treat the input Term as an expression and infer its type using
    -- the built-in term elaborator; return the inferred type.
    infer-type : (expr : Term) → TC Term

    -- Elaborate the first Term argument, treated as an expression,
    -- against the second argument, which must be a type according to
    -- the built-in type elaborator; return the elaborated form of the
    -- input.
    check-type : (expr : Term) (want : Term) → TC Term

    -- Perform head-reduction on the input term, which must be an
    -- inferrable form.
    reduce : Term → TC Term
    -- Perform full normalisation on the input term, which must be an
    -- inferrable form.
    normalise : Term → TC Term

    -- Use the built-in term elaborator to check the *reflected* Term
    -- against the *meta* Type, returning on success a value of that
    -- Type.
    unquoteTC : ∀ {a} {A : Type a} → Term → TC A

    -- Return the reflected Term representation of an actual value.
    quoteTC : A → TC Term

    -- Return the reflected Term representation of a value whose type
    -- lives in the sort Typeω.
    quoteωTC : ∀ {A : Typeω} → A → TC Term

    -- Get the current context as a telescope, i.e. so that it is
    -- indexable by de Bruijn index.
    -- Note that the types in the returned telescope are valid /at their
    -- prefix/, i.e., using them as terms in the current context
    -- requires weakening them by (1 + idx).
    getContext : TC Telescope

    -- Add a single entry to the context of the continuation.
    extend-context
      : String    -- Name to use for the context entry.
      → Arg Term
        -- The ArgInfo determines the variable's visibility in the
        -- context telescope.
      → TC A → TC A

    -- Run the continuation in the context formed by extending that in
    -- which the metaprogram was entered with the given telescope.
    in-context : Telescope → TC A → TC A

    -- Create a fresh name from the given string.
    -- The name will not be added to the scope.
    freshName : String → TC Name

    -- Add a pending type signature for the given name to the TC state.
    --
    -- It must be defined by 'define-function' before the surrounding TC
    -- computation exits.
    declare
      : Arg Name -- The 'ArgInfo' controls whether the name is an instance.
      → Term     -- Type of the declaration.
      → TC ⊤

    -- Define a function that must have been previously declared by the
    -- given clauses.
    --
    -- The definition can either be pending because the user wrote a
    -- type signature or because it was added by 'declare'.
    define-function : Name → List Clause → TC ⊤

    -- Define a postulate. The arguments are as per 'define-function',
    -- but the resulting name can not have a definition.
    declare-postulate : Arg Name → Term → TC ⊤

    -- Look up the type of a defined name.
    --
    -- The type returned is relative to the context of the current
    -- module (if any), i.e., if the name is defined in the same
    -- parametrised module where the TC computation was executed, the
    -- returned type will not contain binders for the module parameters.
    get-type : Name → TC Term

    -- Look up what a defined name refers to in the signature.
    --
    -- The information about the definition is relative to the context
    -- of the current module (if any), e.g., if the name refers to a
    -- function defined in the same parametrised module where the
    -- metaprogram is being executed, the returned clauses will not have
    -- pattern bindings for the module telescope.
    get-definition    : Name → TC Definition

    -- Look up whether a defined name is the name of a macro.
    isMacro           : Name → TC Bool

    -- If 'true', makes the following primitives also normalise
    -- their results within the continuation:
    -- infer-type, check-type, quoteTC, get-type, and getContext
    withNormalisation : Bool → TC A → TC A
    askNormalisation  : TC Bool

    -- If 'true', the following primitives will perform parameter
    -- reconstruction on their results within the continuation:
    --   get-definition, normalise, reduce, infer-type, check-type and
    --   getContext
    --
    -- Parameter reconstruction fills in the parameters of data-type
    -- constructors, record projections, and projection-like functions,
    -- which are normally optimised out of the term representation.
    -- When parameter reconstruction is disabled, these arguments will
    -- still be present in the reflected argument spine, but their value
    -- will be 'unknown'.
    withReconstructed : Bool → TC A → TC A
    askReconstructed  : TC Bool

    -- If 'true', invocations of the built-in term elaborator (e.g.
    -- infer-type) will insert metavariables corresponding to leading
    -- invisible binders in the type of the expression.
    withExpandLast : Bool → TC A → TC A
    askExpandLast  : TC Bool

    -- Controls whether the given list of names should be reduced in the
    -- continuation. The names can refer to any type of definition, but
    -- controlling unfolding through 'withReduceDefs' works best if they
    -- refer to defined functions.
    --
    -- If the Bool argument is 'true', only the given names will be
    -- reduced; if it is 'false', all but the given names will be
    -- reduced.
    withReduceDefs : Bool × List Name → TC A → TC A
    askReduceDefs  : TC (Bool × List Name)

    -- Execute the continuation, returning its first return value.
    --
    -- If the returned Bool is 'false', modifications made to the TC
    -- state during the continuation are reset. They are kept if the
    -- Bool is 'true'.
    --
    -- The returned value can become invalid if the state is rolled
    -- back, e.g. because it refers to metavariables created during
    -- execution of the continuation. This is not checked.
    run-speculative : TC (A × Bool) → TC A

    -- Get a list of the valid instance candidates for the given
    -- metavariable, which does not need to be an instance meta.
    --
    -- The returned candidates are sorted in order of specificity, i.e.,
    -- if two candidates C : T and D : T' are both possible, and the
    -- type T is a substitution instance of T' but not vice-versa, the
    -- candidate C will appear before D in the list.
    get-instances : Meta → TC (List Term)

    -- Add a pending data-type signature for the given name to the TC
    -- state.
    --
    -- The pending signature must be defined by 'defineData' before the
    -- surrounding TC computation exits.
    -- This function can introduce pending data-type signatures whose
    -- type is not actually valid for a data-type, e.g. because it does
    -- not return a sort. The type is only checked for validity when
    -- 'defineData' is called.
    declareData
      : Name -- The name of the data-type
      → Nat
      -- The number of quantifiers in the given type that should be
      -- treated as binding parameters, rather than indices.
      → Term -- The type of the data-type.
      → TC ⊤

    -- Define a data-type whose definition must have been pending.
    --
    -- The given constructor types must have enough leading quantifiers
    -- to introduce all of the data-type's declared parameters.
    --
    -- The definition can either be pending because the user wrote a
    -- type signature or because it was added by 'declareData'. This
    -- function checks whether the pending signature is actually valid
    -- for a data-type.
    defineData
      : Name               -- The name of the data type.
      → List (Name × Term) -- The names and types of the constructors.
      → TC ⊤
```

<!--
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
-->

# Reflection helpers

```agda
Args : Type
Args = List (Arg Term)

Fun : ∀ {ℓ ℓ'} → Type ℓ → Type ℓ' → Type (ℓ ⊔ ℓ')
Fun A B = A → B

idfun : ∀ {ℓ} (A : Type ℓ) → A → A
idfun A x = x

under-abs : ∀ {ℓ} {A : Type ℓ} → Term → TC A → TC A
under-abs (lam v (abs nm _)) m = extend-context nm (arg (arginfo v) unknown) m
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

unifies? : Term → Term → TC Bool
unifies? `x `y = run-speculative ((unify `x `y >> pure (true , true)) <|> pure (false , false))

checks? : Term → Term → TC (Maybe Term)
checks? tm tp = run-speculative (check-type tm tp <&> (λ tm → (just tm , true)) <|> pure (nothing , false))

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

blocking-meta* (arg (arginfo visible)   tm ∷ _) = blocking-meta tm
blocking-meta* (arg (arginfo instance') tm ∷ _) = blocking-meta tm
blocking-meta* (arg (arginfo hidden)    tm ∷ as) = blocking-meta* as

blocking-meta* [] = nothing

reduceB : Term → TC Term
reduceB tm = do
  tm' ← reduce tm
  case blocking-meta tm' of λ where
    (just b) → blockTC b
    nothing  → pure tm'

-- The first argument decides whether we want a PathP.
unapply-path' : Bool → Term → TC (Maybe (Term × Term × Term))
unapply-path' true red@(def (quote PathP) (l h∷ T v∷ x v∷ y v∷ [])) = do
  pure (just (T , x , y))
unapply-path' false red@(def (quote PathP) (l h∷ T v∷ x v∷ y v∷ [])) = do
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

unapply-path' true tm = reduce tm >>= λ where
  tm@(meta _ _) → do
    (Tmv , T) ← new-meta' (pi (argN (quoteTerm I)) (abs "i" (def (quote Type) (unknown v∷ []))))
    l ← new-meta (meta Tmv (quoteTerm i0 v∷ []))
    r ← new-meta (meta Tmv (quoteTerm i1 v∷ []))
    unify tm (def (quote PathP) (T v∷ l v∷ r v∷ []))
    traverse wait-for-type (l ∷ r ∷ [])
    pure (just (T , l , r))

  red@(def (quote PathP) (T v∷ l v∷ r v∷ [])) → do
    pure (just (T , l , r))

  _ → pure nothing

unapply-path' pathp tm = reduce tm >>= λ where
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

unapply-path unapply-pathp : Term → TC (Maybe (Term × Term × Term))
unapply-path = unapply-path' false
unapply-pathp = unapply-path' true

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
