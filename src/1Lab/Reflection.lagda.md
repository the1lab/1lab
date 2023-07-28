<!--
```agda
open import 1Lab.Type.Sigma
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type hiding (absurd)

open import Data.Product.NAry
open import Data.Vec.Base
open import Data.Bool
open import Data.List
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
open Data.List public
open Data.Bool public
```

# Metaprogramming

Here, we bind and define helpers for Agda's clunky metaprogramming
facilities.

## QNames

The "Q" is for **q**ualified.

```agda
postulate Name : Type
{-# BUILTIN QNAME Name #-}

primitive
  primQNameEquality : Name → Name → Bool
  primQNameLess     : Name → Name → Bool
  primShowQName     : Name → String
```

## Fixity declarations

The fixity of an identifier is given by an associativity (left, right or
neither), and a precedence.

```agda
data Associativity : Type where
  left-assoc  : Associativity
  right-assoc : Associativity
  non-assoc   : Associativity

data Precedence : Type where
  related   : Float → Precedence
  unrelated : Precedence

data Fixity : Type where
  fixity : Associativity → Precedence → Fixity

{-# BUILTIN ASSOC      Associativity #-}
{-# BUILTIN ASSOCLEFT  left-assoc    #-}
{-# BUILTIN ASSOCRIGHT right-assoc   #-}
{-# BUILTIN ASSOCNON   non-assoc     #-}

{-# BUILTIN PRECEDENCE    Precedence #-}
{-# BUILTIN PRECRELATED   related    #-}
{-# BUILTIN PRECUNRELATED unrelated  #-}

{-# BUILTIN FIXITY       Fixity #-}
{-# BUILTIN FIXITYFIXITY fixity #-}

primitive
  primQNameFixity : Name → Fixity
  primQNameToWord64s : Name → Word64 × Word64
```

## Metavariables

Metavariables are reflected, essentially, as natural numbers. Thus they
can be shown and tested for equality.

```agda
postulate Meta : Type
{-# BUILTIN AGDAMETA Meta #-}

primitive
  primMetaEquality : Meta → Meta → Bool
  primMetaLess     : Meta → Meta → Bool
  primShowMeta     : Meta → String
  primMetaToNat    : Meta → Nat

data Blocker : Type where
  blockerAny  : List Blocker → Blocker
  blockerAll  : List Blocker → Blocker
  blockerMeta : Meta → Blocker

{-# BUILTIN AGDABLOCKER     Blocker #-}
{-# BUILTIN AGDABLOCKERANY  blockerAny #-}
{-# BUILTIN AGDABLOCKERALL  blockerAll #-}
{-# BUILTIN AGDABLOCKERMETA blockerMeta #-}
```

## Arguments

An _argument_ is the data that specifies the domain of a
`pi`{.Agda}-abstraction. More than just a type, arguments have a
`visibility`{.Agda ident=Visibility}, a `relevance`{.Agda
ident=Relevance}, and a `Quantity`{.Agda ident=Quantity}.

```agda
-- Arguments can be (visible), {hidden}, or {{instance}}.
data Visibility : Type where
  visible hidden instance′ : Visibility

{-# BUILTIN HIDING   Visibility #-}
{-# BUILTIN VISIBLE  visible    #-}
{-# BUILTIN HIDDEN   hidden     #-}
{-# BUILTIN INSTANCE instance′  #-}

-- Arguments can be relevant or irrelevant.
data Relevance : Type where
  relevant irrelevant : Relevance

{-# BUILTIN RELEVANCE  Relevance  #-}
{-# BUILTIN RELEVANT   relevant   #-}
{-# BUILTIN IRRELEVANT irrelevant #-}

-- Arguments also have a quantity.
data Quantity : Type where
  quantity-0 quantity-ω : Quantity

{-# BUILTIN QUANTITY   Quantity   #-}
{-# BUILTIN QUANTITY-0 quantity-0 #-}
{-# BUILTIN QUANTITY-ω quantity-ω #-}
```

Packaging a `Relevance`{.Agda} and a `Quantity`{.Agda} gets you a
`Modality`{.Agda}; A modality and a `Visibility`{.Agda} make an
`ArgInfo`{.Agda}. An `ArgInfo` and something else makes an `Arg`{.Agda}.
Got it?

```agda
record Modality : Type where
  constructor modality
  field
    r : Relevance
    q : Quantity

{-# BUILTIN MODALITY             Modality #-}
{-# BUILTIN MODALITY-CONSTRUCTOR modality #-}

record ArgInfo : Type where
  constructor arginfo
  field
    arg-vis : Visibility
    arg-modality : Modality

record Arg {a} (A : Type a) : Type a where
  constructor arg
  field
    arg-info : ArgInfo
    unarg : A

{-# BUILTIN ARGINFO    ArgInfo  #-}
{-# BUILTIN ARGARGINFO arginfo #-}
{-# BUILTIN ARG        Arg      #-}
{-# BUILTIN ARGARG     arg      #-}
```

## Abstractions

Pairs of strings and things are called `Abs`{.Agda}tractions.

```agda
record Abs {a} (A : Type a) : Type a where
  constructor abs
  field
    abs-name : String
    abs-binder : A

{-# BUILTIN ABS    Abs #-}
{-# BUILTIN ABSABS abs #-}
```

## Literals

Reflecting all of Agda's built-in types, we have `Literal`{.Agda}s. As a
bonus, there are also metavariable literals!

```agda
data Literal : Type where
  nat    : (n : Nat)    → Literal
  word64 : (n : Word64) → Literal
  float  : (x : Float)  → Literal
  char   : (c : Char)   → Literal
  string : (s : String) → Literal
  name   : (x : Name)   → Literal
  meta   : (x : Meta)   → Literal

{-# BUILTIN AGDALITERAL   Literal #-}
{-# BUILTIN AGDALITNAT    nat     #-}
{-# BUILTIN AGDALITWORD64 word64  #-}
{-# BUILTIN AGDALITFLOAT  float   #-}
{-# BUILTIN AGDALITCHAR   char    #-}
{-# BUILTIN AGDALITSTRING string  #-}
{-# BUILTIN AGDALITQNAME  name    #-}
{-# BUILTIN AGDALITMETA   meta    #-}
```

## Agda's syntax

And now we finally get to Agda's syntax.

```agda
data Term    : Type
data Sort    : Type
data Pattern : Type
data Clause  : Type
Telescope = List (String × Arg Term)

data Term where
  var       : (x : Nat) (args : List (Arg Term)) → Term
  con       : (c : Name) (args : List (Arg Term)) → Term
  def       : (f : Name) (args : List (Arg Term)) → Term
  lam       : (v : Visibility) (t : Abs Term) → Term
  pat-lam   : (cs : List Clause) (args : List (Arg Term)) → Term
  pi        : (a : Arg Term) (b : Abs Term) → Term
  agda-sort : (s : Sort) → Term
  lit       : (l : Literal) → Term
  meta      : (x : Meta) → List (Arg Term) → Term
  unknown   : Term

data Sort where
  set     : (t : Term) → Sort
  lit     : (n : Nat) → Sort
  prop    : (t : Term) → Sort
  propLit : (n : Nat) → Sort
  inf     : (n : Nat) → Sort
  unknown : Sort

data Pattern where
  con    : (c : Name) (ps : List (Arg Pattern)) → Pattern
  dot    : (t : Term)    → Pattern
  var    : (x : Nat)     → Pattern
  lit    : (l : Literal) → Pattern
  proj   : (f : Name)    → Pattern
  absurd : (x : Nat)     → Pattern  -- absurd patterns counts as variables

data Clause where
  clause        : (tel : Telescope) (ps : List (Arg Pattern)) (t : Term) → Clause
  absurd-clause : (tel : Telescope) (ps : List (Arg Pattern)) → Clause

data Definition : Type where
  function    : (cs : List Clause) → Definition
  data-type   : (pars : Nat) (cs : List Name) → Definition
  record-type : (c : Name) (fs : List (Arg Name)) → Definition
  data-cons   : (d : Name) → Definition
  axiom       : Definition
  prim-fun    : Definition
```

## The TC monad

To drive meta computations, we have the TC monad, reflecting Agda's
`TCM` monad.

```agda
data ErrorPart : Type where
  strErr  : String → ErrorPart
  termErr : Term → ErrorPart
  pattErr : Pattern → ErrorPart
  nameErr : Name → ErrorPart

instance
  String-ErrorPart : IsString ErrorPart
  String-ErrorPart .IsString.Constraint _ = ⊤
  String-ErrorPart .IsString.fromString s = strErr s

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
{-# BUILTIN AGDATERM      Term    #-}
{-# BUILTIN AGDASORT      Sort    #-}
{-# BUILTIN AGDAPATTERN   Pattern #-}
{-# BUILTIN AGDACLAUSE    Clause  #-}

{-# BUILTIN AGDATERMVAR         var       #-}
{-# BUILTIN AGDATERMCON         con       #-}
{-# BUILTIN AGDATERMDEF         def       #-}
{-# BUILTIN AGDATERMMETA        meta      #-}
{-# BUILTIN AGDATERMLAM         lam       #-}
{-# BUILTIN AGDATERMEXTLAM      pat-lam   #-}
{-# BUILTIN AGDATERMPI          pi        #-}
{-# BUILTIN AGDATERMSORT        agda-sort #-}
{-# BUILTIN AGDATERMLIT         lit       #-}
{-# BUILTIN AGDATERMUNSUPPORTED unknown   #-}

{-# BUILTIN AGDASORTSET         set     #-}
{-# BUILTIN AGDASORTLIT         lit     #-}
{-# BUILTIN AGDASORTPROP        prop    #-}
{-# BUILTIN AGDASORTPROPLIT     propLit #-}
{-# BUILTIN AGDASORTINF         inf     #-}
{-# BUILTIN AGDASORTUNSUPPORTED unknown #-}

{-# BUILTIN AGDAERRORPART       ErrorPart #-}
{-# BUILTIN AGDAERRORPARTSTRING strErr    #-}
{-# BUILTIN AGDAERRORPARTTERM   termErr   #-}
{-# BUILTIN AGDAERRORPARTPATT   pattErr   #-}
{-# BUILTIN AGDAERRORPARTNAME   nameErr   #-}

{-# BUILTIN AGDADEFINITION                Definition  #-}
{-# BUILTIN AGDADEFINITIONFUNDEF          function    #-}
{-# BUILTIN AGDADEFINITIONDATADEF         data-type   #-}
{-# BUILTIN AGDADEFINITIONRECORDDEF       record-type #-}
{-# BUILTIN AGDADEFINITIONDATACONSTRUCTOR data-cons   #-}
{-# BUILTIN AGDADEFINITIONPOSTULATE       axiom       #-}
{-# BUILTIN AGDADEFINITIONPRIMITIVE       prim-fun    #-}

{-# BUILTIN AGDAPATCON    con     #-}
{-# BUILTIN AGDAPATDOT    dot     #-}
{-# BUILTIN AGDAPATVAR    var     #-}
{-# BUILTIN AGDAPATLIT    lit     #-}
{-# BUILTIN AGDAPATPROJ   proj    #-}
{-# BUILTIN AGDAPATABSURD absurd  #-}

{-# BUILTIN AGDACLAUSECLAUSE clause        #-}
{-# BUILTIN AGDACLAUSEABSURD absurd-clause #-}
{-# BUILTIN AGDATCM                           TC                         #-}
{-# BUILTIN AGDATCMRETURN                     returnTC                   #-}
{-# BUILTIN AGDATCMBIND                       bindTC                     #-}
{-# BUILTIN AGDATCMUNIFY                      unify                      #-}
{-# BUILTIN AGDATCMTYPEERROR                  typeError                  #-}
{-# BUILTIN AGDATCMINFERTYPE                  inferType                  #-}
{-# BUILTIN AGDATCMCHECKTYPE                  checkType                  #-}
{-# BUILTIN AGDATCMNORMALISE                  normalise                  #-}
{-# BUILTIN AGDATCMREDUCE                     reduce                     #-}
{-# BUILTIN AGDATCMCATCHERROR                 catchTC                    #-}
{-# BUILTIN AGDATCMQUOTETERM                  quoteTC                    #-}
{-# BUILTIN AGDATCMUNQUOTETERM                unquoteTC                  #-}
{-# BUILTIN AGDATCMQUOTEOMEGATERM             quoteωTC                   #-}
{-# BUILTIN AGDATCMGETCONTEXT                 getContext                 #-}
{-# BUILTIN AGDATCMEXTENDCONTEXT              extendContext              #-}
{-# BUILTIN AGDATCMINCONTEXT                  inContext                  #-}
{-# BUILTIN AGDATCMFRESHNAME                  freshName                  #-}
{-# BUILTIN AGDATCMDECLAREDEF                 declareDef                 #-}
{-# BUILTIN AGDATCMDECLAREPOSTULATE           declarePostulate           #-}
{-# BUILTIN AGDATCMDEFINEFUN                  defineFun                  #-}
{-# BUILTIN AGDATCMGETTYPE                    getType                    #-}
{-# BUILTIN AGDATCMGETDEFINITION              getDefinition              #-}
{-# BUILTIN AGDATCMBLOCK                      blockTC                    #-}
{-# BUILTIN AGDATCMCOMMIT                     commitTC                   #-}
{-# BUILTIN AGDATCMISMACRO                    isMacro                    #-}
{-# BUILTIN AGDATCMWITHNORMALISATION          withNormalisation          #-}
{-# BUILTIN AGDATCMFORMATERRORPARTS           formatErrorParts           #-}
{-# BUILTIN AGDATCMDEBUGPRINT                 debugPrint                 #-}
{-# BUILTIN AGDATCMWITHRECONSTRUCTED          withReconstructed          #-}
{-# BUILTIN AGDATCMWITHEXPANDLAST             withExpandLast             #-}
{-# BUILTIN AGDATCMWITHREDUCEDEFS             withReduceDefs             #-}
{-# BUILTIN AGDATCMASKNORMALISATION           askNormalisation           #-}
{-# BUILTIN AGDATCMASKRECONSTRUCTED           askReconstructed           #-}
{-# BUILTIN AGDATCMASKEXPANDLAST              askExpandLast              #-}
{-# BUILTIN AGDATCMASKREDUCEDEFS              askReduceDefs              #-}
{-# BUILTIN AGDATCMNOCONSTRAINTS              noConstraints              #-}
{-# BUILTIN AGDATCMRUNSPECULATIVE             runSpeculative             #-}
{-# BUILTIN AGDATCMGETINSTANCES               getInstances               #-}
{-# BUILTIN AGDATCMDECLAREDATA                declareData                #-}
{-# BUILTIN AGDATCMDEFINEDATA                 defineData                 #-}

instance
  Map-TC : Map (eff TC)
  Map-TC .Map._<$>_ f x = bindTC x λ x → returnTC (f x)

  Idiom-TC : Idiom (eff TC)
  Idiom-TC .Idiom.pure = returnTC
  Idiom-TC .Idiom._<*>_ f g = bindTC f λ f → bindTC g λ g → pure (f g)

  Bind-TC : Bind (eff TC)
  Bind-TC .Bind._>>=_ = bindTC

  Alt-TC : Alt (eff TC)
  Alt-TC .Alt.fail′ xs = typeError [ strErr xs ]
  Alt-TC .Alt._<|>_ = catchTC
```
</details>

# Reflection helpers

```agda
argH0 argH argN : ∀ {ℓ} {A : Type ℓ} → A → Arg A
argH = arg (arginfo hidden (modality relevant quantity-ω))
argH0 = arg (arginfo hidden (modality relevant quantity-0))
argN = arg (arginfo visible (modality relevant quantity-ω))

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

new-meta′ : Term → TC (Meta × Term)
new-meta′ ty = do
  tm@(meta mv _) ← checkType unknown ty
    where _ → typeError $ [ "impossible new-meta′" ]
  debugPrint "tactic.meta" 70
    [ "Created new meta " , termErr tm , " of type " , termErr tm ]
  pure (mv , tm)

blockOnMeta   : ∀ {a} {A : Type a} → Meta → TC A
blockOnMeta m = blockTC (blockerMeta m)

vlam : String → Term → Term
vlam nam body = lam visible (abs nam body)

pattern _v∷_ t xs = arg (arginfo visible (modality relevant quantity-ω)) t ∷ xs
pattern _h∷_ t xs = arg (arginfo hidden (modality relevant quantity-ω)) t ∷ xs
pattern _hm∷_ t xs = arg (arginfo hidden (modality relevant _)) t ∷ xs

infixr 30 _v∷_ _h∷_ _hm∷_

infer-hidden : Nat → List (Arg Term) → List (Arg Term)
infer-hidden zero xs = xs
infer-hidden (suc n) xs = unknown h∷ infer-hidden n xs

getName : Term → Maybe Name
getName (def x _) = just x
getName (con x _) = just x
getName _ = nothing

_name=?_ : Name → Name → Bool
x name=? y = primQNameEquality x y

_visibility=?_ : Visibility → Visibility → Bool
visible visibility=? visible = true
hidden visibility=? hidden = true
instance′ visibility=? instance′ = true
_ visibility=? _ = false

-- [TODO: Reed M, 06/05/2022] We don't actually use any fancy modalities
-- anywhere AFAICT, so let's ignore those.
_arginfo=?_ : ArgInfo → ArgInfo → Bool
arginfo v₁ m₁ arginfo=? arginfo v₂ m₂ = (v₁ visibility=? v₂)

arg=? : ∀ {a} {A : Type a} → (A → A → Bool) → Arg A → Arg A → Bool
arg=? eq=? (arg i₁ x) (arg i₂ y) = and (i₁ arginfo=? i₂) (eq=? x y)

-- We want to compare terms up to α-equivalence, so we ignore binder
-- names.
abs=? : ∀ {a} {A : Type a} → (A → A → Bool) → Abs A → Abs A → Bool
abs=? eq=? (abs _ x) (abs _ y) = eq=? x y

{-# TERMINATING #-}
-- [TODO: Reed M, 06/05/2022] Finish this

_term=?_ : Term → Term → Bool
var nm₁ args₁ term=? var nm₂ args₂ = and (nm₁ == nm₂) (all=? (arg=? _term=?_) args₁ args₂)
con c₁ args₁ term=? con c₂ args₂ = and (c₁ name=? c₂) (all=? (arg=? _term=?_) args₁ args₂)
def f₁ args₁ term=? def f₂ args₂ = and (f₁ name=? f₂) (all=? (arg=? _term=?_) args₁ args₂)
lam v₁ t₁ term=? lam v₂ t₂ = and (v₁ visibility=? v₂) (abs=? _term=?_ t₁ t₂)
pat-lam cs₁ args₁ term=? pat-lam cs₂ args₂ = false
pi a₁ b₁ term=? pi a₂ b₂ = and (arg=? _term=?_ a₁ a₂) (abs=? _term=?_ b₁ b₂)
agda-sort s term=? t₂ = false
lit l term=? t₂ = false
meta x x₁ term=? t₂ = false
unknown term=? t₂ = false
_ term=? _ = false

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
  quote-repr! : ∀ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′} → A → Term → TC ⊤
  quote-repr! a = quote-repr-macro a

instance
  IsString-Error : IsString (List ErrorPart)
  IsString-Error .IsString.Constraint _ = ⊤
  IsString-Error .fromString s = fromString s ∷ []

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
