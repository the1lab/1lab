```agda
open import 1Lab.Type.Sigma
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type hiding (absurd)

open import Data.Bool
open import Data.List

module 1Lab.Reflection where

open import 1Lab.Prim.Data.String public
open import 1Lab.Prim.Data.Float public
open import 1Lab.Prim.Data.Maybe public
open import 1Lab.Prim.Data.Word public
open import 1Lab.Prim.Monad public
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
  blockOnMeta      : ∀ {a} {A : Type a} → Meta → TC A
  commitTC         : TC ⊤
  isMacro          : Name → TC Bool

  -- If the argument is 'true' makes the following primitives also normalise
  -- their results: inferType, checkType, quoteTC, getType, and getContext
  withNormalisation : ∀ {a} {A : Type a} → Bool → TC A → TC A

  -- Makes the following primitives to reconstruct hidden arguments
  -- getDefinition, normalise, reduce, inferType, checkType and getContext
  withReconstructed : ∀ {a} {A : Type a} → TC A → TC A

  formatErrorParts : List ErrorPart → TC String
  -- Prints the third argument if the corresponding verbosity level is turned
  -- on (with the -v flag to Agda).
  debugPrint : String → Nat → List ErrorPart → TC ⊤

  -- Only allow reduction of specific definitions while executing the TC computation
  onlyReduceDefs : ∀ {a} {A : Type a} → List Name → TC A → TC A

  -- Don't allow reduction of specific definitions while executing the TC computation
  dontReduceDefs : ∀ {a} {A : Type a} → List Name → TC A → TC A

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
{-# BUILTIN AGDATCMBLOCKONMETA                blockOnMeta                #-}
{-# BUILTIN AGDATCMCOMMIT                     commitTC                   #-}
{-# BUILTIN AGDATCMISMACRO                    isMacro                    #-}
{-# BUILTIN AGDATCMWITHNORMALISATION          withNormalisation          #-}
{-# BUILTIN AGDATCMFORMATERRORPARTS           formatErrorParts           #-}
{-# BUILTIN AGDATCMDEBUGPRINT                 debugPrint                 #-}
{-# BUILTIN AGDATCMONLYREDUCEDEFS             onlyReduceDefs             #-}
{-# BUILTIN AGDATCMDONTREDUCEDEFS             dontReduceDefs             #-}
{-# BUILTIN AGDATCMWITHRECONSPARAMS           withReconstructed          #-}
{-# BUILTIN AGDATCMNOCONSTRAINTS              noConstraints              #-}
{-# BUILTIN AGDATCMRUNSPECULATIVE             runSpeculative             #-}
{-# BUILTIN AGDATCMGETINSTANCES               getInstances               #-}
{-# BUILTIN AGDATCMDECLAREDATA                declareData                #-}
{-# BUILTIN AGDATCMDEFINEDATA                 defineData                 #-}

instance
  Do-TC : Do-syntax TC
  Do-TC .Do-syntax._>>=_ = bindTC

  Idiom-TC : Idiom-syntax TC
  Idiom-TC .Idiom-syntax.pure = returnTC
  Idiom-TC .Idiom-syntax._<*>_ f g = do
    f ← f
    g ← g
    pure (f g)

  Alt-TC : Alt-syntax TC
  Alt-TC .Alt-syntax._<|>_ = catchTC
```
</details>

# Reflection helpers

```agda
Fun : ∀ {ℓ ℓ'} → Type ℓ → Type ℓ' → Type (ℓ ⊔ ℓ')
Fun A B = A → B

idfun : ∀ {ℓ} (A : Type ℓ) → A → A
idfun A x = x

equivFun : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → A ≃ B → A → B
equivFun (f , e) = f

equivInv : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → A ≃ B → B → A
equivInv (f , e) = equiv→inverse e

equivSec : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (e : A ≃ B)
         → _
equivSec (f , e) = equiv→counit e

equivRet : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (e : A ≃ B)
         → _
equivRet (f , e) = equiv→unit e

newMeta : Term → TC Term
newMeta = checkType unknown

varg : {ℓ : _} {A : Type ℓ} → A → Arg A
varg = arg (arginfo visible (modality relevant quantity-ω))

vlam : String → Term → Term
vlam nam body = lam visible (abs nam body)

pattern _v∷_ t xs = arg (arginfo visible (modality relevant quantity-ω)) t ∷ xs
pattern _h∷_ t xs = arg (arginfo hidden (modality relevant quantity-ω)) t ∷ xs
pattern _h0∷_ t xs = arg (arginfo hidden (modality relevant quantity-0)) t ∷ xs

infixr 30 _v∷_ _h∷_ _h0∷_

infer-hidden : Nat → List (Arg Term) → List (Arg Term)
infer-hidden zero xs = xs
infer-hidden (suc n) xs = unknown h∷ infer-hidden n xs

“_↦_” : Term → Term → Term
“_↦_” x y = def (quote Fun) (x v∷ y v∷ [])

“Type” : Term → Term
“Type” l = def (quote Type) (l v∷ [])

tApply : Term → List (Arg Term) → Term
tApply t l = def (quote id) (t v∷ l)

tStrMap : Term → Term → Term
tStrMap A f = def (quote Σ-map₂) (f v∷ A v∷ [])

tStrProj : Term → Name → Term
tStrProj A sfield = tStrMap A (def sfield [])

data Vec {ℓ} (A : Type ℓ) : Nat → Type ℓ where
  []  : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

infixr 20 _∷_

makeVarsFrom : {n : Nat} → Nat → Vec Term n
makeVarsFrom {zero} k = []
makeVarsFrom {suc n} k = var (n + k) [] ∷ (makeVarsFrom k)

iter : ∀ {ℓ} {A : Type ℓ} → Nat → (A → A) → A → A
iter zero f = id
iter (suc n) f = f ∘ iter n f

getName : Term → Maybe Name
getName (def x _) = just x
getName (con x _) = just x
getName _ = nothing

_name=?_ : Name → Name → Bool
x name=? y = primQNameEquality x y

findName : Term → TC Name
findName (def nm _) = returnTC nm
findName (lam hidden (abs _ t)) = findName t
findName (meta m _) = blockOnMeta m
findName t = typeError (strErr "The projections in a field descriptor must be record selectors: " ∷ termErr t ∷ [])

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

debug! : ∀ {ℓ} {A : Type ℓ} → Term → TC A
debug! tm = typeError (strErr "[DEBUG]: " ∷ termErr tm ∷ [])

get-boundary : Term → TC (Maybe (Term × Term))
get-boundary tm@(def (quote _≡_) (_ h∷ T h∷ x v∷ y v∷ [])) = do
  returnTC (just (x , y))
get-boundary tm@(def (quote Path) (_ h∷ T v∷ x v∷ y v∷ [])) = do
  returnTC (just (x , y))
get-boundary tm@(def (quote PathP) (_ h∷ T v∷ x v∷ y v∷ [])) = do
  unify tm (def (quote _≡_) (x v∷ y v∷ []))
  returnTC (just (x , y))
get-boundary (meta m _) = blockOnMeta m
get-boundary _ = returnTC nothing
```
