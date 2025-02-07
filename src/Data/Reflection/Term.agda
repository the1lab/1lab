open import 1Lab.Path.IdentitySystem
open import 1Lab.Path
open import 1Lab.Type hiding (absurd)

open import Data.Reflection.Argument
open import Data.Reflection.Literal
open import Data.Reflection.Meta
open import Data.Reflection.Name
open import Data.Reflection.Abs
open import Data.String.Base
open import Data.Float.Base
open import Data.List.Base
open import Data.Word.Base
open import Data.Dec.Base
open import Data.Nat.Base
open import Data.Id.Base

open import Meta.Append

module Data.Reflection.Term where

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
  meta      : (m : Meta) (args : List (Arg Term)) → Term
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
  absurd : (x : Nat)     → Pattern  -- absurd patterns count as variables

data Clause where
  clause        : (tel : Telescope) (ps : List (Arg Pattern)) (t : Term) → Clause
  absurd-clause : (tel : Telescope) (ps : List (Arg Pattern)) → Clause

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

data Definition : Type where
  function    : (cs : List Clause) → Definition
  data-type   : (pars : Nat) (cs : List Name) → Definition
  record-type : (c : Name) (fs : List (Arg Name)) → Definition
  data-cons   : (d : Name) (q : Quantity) → Definition
  axiom       : Definition
  prim-fun    : Definition

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

instance
  {-# TERMINATING #-}
  Discrete-Term    : Discrete Term
  Discrete-Sort    : Discrete Sort
  Discrete-Pattern : Discrete Pattern
  Discrete-Clause  : Discrete Clause

  Discrete-Term = Discreteᵢ→discrete λ where
    (var x args) (var x₁ args₁) → case (x ≡ᵢ? x₁ , args ≡ᵢ? args₁) of λ where
      (yes reflᵢ , yes reflᵢ) → yes reflᵢ
      (yes as , no ¬ps)       → no λ { reflᵢ → ¬ps reflᵢ }
      (no ¬as , _)            → no λ { reflᵢ → ¬as reflᵢ }
    (con c args) (con c₁ args₁) → case (c ≡ᵢ? c₁ , args ≡ᵢ? args₁) of λ where
      (yes reflᵢ , yes reflᵢ) → yes reflᵢ
      (yes as , no ¬ps)       → no λ { reflᵢ → ¬ps reflᵢ }
      (no ¬as , _)            → no λ { reflᵢ → ¬as reflᵢ }
    (pat-lam cs args) (pat-lam cs₁ args₁) → case (cs ≡ᵢ? cs₁ , args ≡ᵢ? args₁) of λ where
      (yes reflᵢ , yes reflᵢ) → yes reflᵢ
      (yes as , no ¬ps)       → no λ { reflᵢ → ¬ps reflᵢ }
      (no ¬as , _)            → no λ { reflᵢ → ¬as reflᵢ }
    (agda-sort s) (agda-sort s₁) → case s ≡ᵢ? s₁ of λ where
      (yes reflᵢ) → yes reflᵢ
      (no ¬a) → no λ { reflᵢ → ¬a reflᵢ }
    (lit l) (lit l₁) → case l ≡ᵢ? l₁ of λ where
      (yes reflᵢ) → yes reflᵢ
      (no ¬a) → no λ { reflᵢ → ¬a reflᵢ }
    (meta x x₁) (meta x₂ x₃) → case (x ≡ᵢ? x₂ , x₁ ≡ᵢ? x₃) of λ where
      (yes reflᵢ , yes reflᵢ) → yes reflᵢ
      (yes as , no ¬ps)       → no λ { reflᵢ → ¬ps reflᵢ }
      (no ¬as , _)            → no λ { reflᵢ → ¬as reflᵢ }
    (lam v t) (lam v₁ t₁) → case (v ≡ᵢ? v₁ , t ≡ᵢ? t₁) of λ where
      (yes reflᵢ , yes reflᵢ) → yes reflᵢ
      (yes as , no ¬ps)       → no λ { reflᵢ → ¬ps reflᵢ }
      (no ¬as , _)            → no λ { reflᵢ → ¬as reflᵢ }
    (pi a b) (pi a₁ b₁) → case (a ≡ᵢ? a₁ , b ≡ᵢ? b₁) of λ where
      (yes reflᵢ , yes reflᵢ) → yes reflᵢ
      (yes as , no ¬ps)       → no λ { reflᵢ → ¬ps reflᵢ }
      (no ¬as , _)            → no λ { reflᵢ → ¬as reflᵢ }
    (def f args) (def f₁ args₁) → case (f ≡ᵢ? f₁ , args ≡ᵢ? args₁) of λ where
      (yes reflᵢ , yes reflᵢ) → yes reflᵢ
      (yes as , no ¬ps)       → no λ { reflᵢ → ¬ps reflᵢ }
      (no ¬as , _)            → no λ { reflᵢ → ¬as reflᵢ }

    (var x args) (con c args₁) → no (λ ())
    (var x args) (def f args₁) → no (λ ())
    (var x args) (lam v t) → no (λ ())
    (var x args) (pat-lam cs args₁) → no (λ ())
    (var x args) (pi a b) → no (λ ())
    (var x args) (agda-sort s) → no (λ ())
    (var x args) (lit l) → no (λ ())
    (var x args) (meta x₁ x₂) → no (λ ())
    (var x args) unknown → no (λ ())
    (con c args) (var x args₁) → no (λ ())
    (con c args) (def f args₁) → no (λ ())
    (con c args) (lam v t) → no (λ ())
    (con c args) (pat-lam cs args₁) → no (λ ())
    (con c args) (pi a b) → no (λ ())
    (con c args) (agda-sort s) → no (λ ())
    (con c args) (lit l) → no (λ ())
    (con c args) (meta x x₁) → no (λ ())
    (con c args) unknown → no (λ ())
    (def f args) (var x args₁) → no (λ ())
    (def f args) (con c args₁) → no (λ ())
    (def f args) (lam v t) → no (λ ())
    (def f args) (pat-lam cs args₁) → no (λ ())
    (def f args) (pi a b) → no (λ ())
    (def f args) (agda-sort s) → no (λ ())
    (def f args) (lit l) → no (λ ())
    (def f args) (meta x x₁) → no (λ ())
    (def f args) unknown → no (λ ())
    (lam v t) (var x args) → no (λ ())
    (lam v t) (con c args) → no (λ ())
    (lam v t) (def f args) → no (λ ())
    (lam v t) (pat-lam cs args) → no (λ ())
    (lam v t) (pi a b) → no (λ ())
    (lam v t) (agda-sort s) → no (λ ())
    (lam v t) (lit l) → no (λ ())
    (lam v t) (meta x x₁) → no (λ ())
    (lam v t) unknown → no (λ ())
    (pat-lam cs args) (var x args₁) → no (λ ())
    (pat-lam cs args) (con c args₁) → no (λ ())
    (pat-lam cs args) (def f args₁) → no (λ ())
    (pat-lam cs args) (lam v t) → no (λ ())
    (pat-lam cs args) (pi a b) → no (λ ())
    (pat-lam cs args) (agda-sort s) → no (λ ())
    (pat-lam cs args) (lit l) → no (λ ())
    (pat-lam cs args) (meta x x₁) → no (λ ())
    (pat-lam cs args) unknown → no (λ ())
    (pi a b) (var x args) → no (λ ())
    (pi a b) (con c args) → no (λ ())
    (pi a b) (def f args) → no (λ ())
    (pi a b) (lam v t) → no (λ ())
    (pi a b) (pat-lam cs args) → no (λ ())
    (pi a b) (agda-sort s) → no (λ ())
    (pi a b) (lit l) → no (λ ())
    (pi a b) (meta x x₁) → no (λ ())
    (pi a b) unknown → no (λ ())
    (agda-sort s) (var x args) → no (λ ())
    (agda-sort s) (con c args) → no (λ ())
    (agda-sort s) (def f args) → no (λ ())
    (agda-sort s) (lam v t) → no (λ ())
    (agda-sort s) (pat-lam cs args) → no (λ ())
    (agda-sort s) (pi a b) → no (λ ())
    (agda-sort s) (lit l) → no (λ ())
    (agda-sort s) (meta x x₁) → no (λ ())
    (agda-sort s) unknown → no (λ ())
    (lit l) (var x args) → no (λ ())
    (lit l) (con c args) → no (λ ())
    (lit l) (def f args) → no (λ ())
    (lit l) (lam v t) → no (λ ())
    (lit l) (pat-lam cs args) → no (λ ())
    (lit l) (pi a b) → no (λ ())
    (lit l) (agda-sort s) → no (λ ())
    (lit l) (meta x x₁) → no (λ ())
    (lit l) unknown → no (λ ())
    (meta x x₁) (var x₂ args) → no (λ ())
    (meta x x₁) (con c args) → no (λ ())
    (meta x x₁) (def f args) → no (λ ())
    (meta x x₁) (lam v t) → no (λ ())
    (meta x x₁) (pat-lam cs args) → no (λ ())
    (meta x x₁) (pi a b) → no (λ ())
    (meta x x₁) (agda-sort s) → no (λ ())
    (meta x x₁) (lit l) → no (λ ())
    (meta x x₁) unknown → no (λ ())
    unknown (var x args) → no (λ ())
    unknown (con c args) → no (λ ())
    unknown (def f args) → no (λ ())
    unknown (lam v t) → no (λ ())
    unknown (pat-lam cs args) → no (λ ())
    unknown (pi a b) → no (λ ())
    unknown (agda-sort s) → no (λ ())
    unknown (lit l) → no (λ ())
    unknown (meta x x₁) → no (λ ())
    unknown unknown → yes reflᵢ

  Discrete-Sort = Discreteᵢ→discrete λ where
    (set t) (set t₁)         → case t ≡ᵢ? t₁ of λ where
      (yes reflᵢ) → yes reflᵢ
      (no ¬a) → no λ { reflᵢ → ¬a reflᵢ }
    (lit n) (lit n₁)         → case n ≡ᵢ? n₁ of λ where
      (yes reflᵢ) → yes reflᵢ
      (no ¬a) → no λ { reflᵢ → ¬a reflᵢ }
    (prop t) (prop t₁)       → case t ≡ᵢ? t₁ of λ where
      (yes reflᵢ) → yes reflᵢ
      (no ¬a) → no λ { reflᵢ → ¬a reflᵢ }
    (propLit n) (propLit n₁) → case n ≡ᵢ? n₁ of λ where
      (yes reflᵢ) → yes reflᵢ
      (no ¬a) → no λ { reflᵢ → ¬a reflᵢ }
    (inf n) (inf n₁)         → case n ≡ᵢ? n₁ of λ where
      (yes reflᵢ) → yes reflᵢ
      (no ¬a) → no λ { reflᵢ → ¬a reflᵢ }
    unknown unknown          → yes reflᵢ

    (set t) (lit n) → no (λ ())
    (set t) (prop t₁) → no (λ ())
    (set t) (propLit n) → no (λ ())
    (set t) (inf n) → no (λ ())
    (set t) unknown → no (λ ())
    (lit n) (set t) → no (λ ())
    (lit n) (prop t) → no (λ ())
    (lit n) (propLit n₁) → no (λ ())
    (lit n) (inf n₁) → no (λ ())
    (lit n) unknown → no (λ ())
    (prop t) (set t₁) → no (λ ())
    (prop t) (lit n) → no (λ ())
    (prop t) (propLit n) → no (λ ())
    (prop t) (inf n) → no (λ ())
    (prop t) unknown → no (λ ())
    (propLit n) (set t) → no (λ ())
    (propLit n) (lit n₁) → no (λ ())
    (propLit n) (prop t) → no (λ ())
    (propLit n) (inf n₁) → no (λ ())
    (propLit n) unknown → no (λ ())
    (inf n) (set t) → no (λ ())
    (inf n) (lit n₁) → no (λ ())
    (inf n) (prop t) → no (λ ())
    (inf n) (propLit n₁) → no (λ ())
    (inf n) unknown → no (λ ())
    unknown (set t) → no (λ ())
    unknown (lit n) → no (λ ())
    unknown (prop t) → no (λ ())
    unknown (propLit n) → no (λ ())
    unknown (inf n) → no (λ ())

  Discrete-Pattern = Discreteᵢ→discrete λ where
    (con c ps) (con c₁ ps₁) → case (c ≡ᵢ? c₁ , ps ≡ᵢ? ps₁) of λ where
      (yes reflᵢ , yes reflᵢ) → yes reflᵢ
      (yes as , no ¬ps)       → no λ { reflᵢ → ¬ps reflᵢ }
      (no ¬as , _)            → no λ { reflᵢ → ¬as reflᵢ }
    (dot t) (dot t₁) → case t ≡ᵢ? t₁ of λ where
      (yes reflᵢ) → yes reflᵢ
      (no ¬a) → no λ { reflᵢ → ¬a reflᵢ }
    (var x) (var x₁) → case x ≡ᵢ? x₁ of λ where
      (yes reflᵢ) → yes reflᵢ
      (no ¬a) → no λ { reflᵢ → ¬a reflᵢ }
    (lit l) (lit l₁) → case l ≡ᵢ? l₁ of λ where
      (yes reflᵢ) → yes reflᵢ
      (no ¬a) → no λ { reflᵢ → ¬a reflᵢ }
    (proj f) (proj f₁) → case f ≡ᵢ? f₁ of λ where
      (yes reflᵢ) → yes reflᵢ
      (no ¬a) → no λ { reflᵢ → ¬a reflᵢ }
    (absurd x) (absurd x₁) → case x ≡ᵢ? x₁ of λ where
      (yes reflᵢ) → yes reflᵢ
      (no ¬a) → no λ { reflᵢ → ¬a reflᵢ }

    (con c ps) (dot t) → no (λ ())
    (con c ps) (var x) → no (λ ())
    (con c ps) (lit l) → no (λ ())
    (con c ps) (proj f) → no (λ ())
    (con c ps) (absurd x) → no (λ ())
    (dot t) (con c ps) → no (λ ())
    (dot t) (var x) → no (λ ())
    (dot t) (lit l) → no (λ ())
    (dot t) (proj f) → no (λ ())
    (dot t) (absurd x) → no (λ ())
    (var x) (con c ps) → no (λ ())
    (var x) (dot t) → no (λ ())
    (var x) (lit l) → no (λ ())
    (var x) (proj f) → no (λ ())
    (var x) (absurd x₁) → no (λ ())
    (lit l) (con c ps) → no (λ ())
    (lit l) (dot t) → no (λ ())
    (lit l) (var x) → no (λ ())
    (lit l) (proj f) → no (λ ())
    (lit l) (absurd x) → no (λ ())
    (proj f) (con c ps) → no (λ ())
    (proj f) (dot t) → no (λ ())
    (proj f) (var x) → no (λ ())
    (proj f) (lit l) → no (λ ())
    (proj f) (absurd x) → no (λ ())
    (absurd x) (con c ps) → no (λ ())
    (absurd x) (dot t) → no (λ ())
    (absurd x) (var x₁) → no (λ ())
    (absurd x) (lit l) → no (λ ())
    (absurd x) (proj f) → no (λ ())

  Discrete-Clause = Discreteᵢ→discrete λ where
    (clause tel ps t) (clause tel₁ ps₁ t₁) → case (tel ≡ᵢ? tel₁ , ps ≡ᵢ? ps₁ , t ≡ᵢ? t₁) of λ where
      (yes reflᵢ , yes reflᵢ , yes reflᵢ) → yes reflᵢ
      (yes as , yes bs , no ¬ps)          → no λ { reflᵢ → ¬ps reflᵢ }
      (yes as , no ¬ps , _)               → no λ { reflᵢ → ¬ps reflᵢ }
      (no ¬as , _)                        → no λ { reflᵢ → ¬as reflᵢ }
    (clause tel ps t) (absurd-clause tel₁ ps₁) → no (λ ())
    (absurd-clause tel ps) (clause tel₁ ps₁ t) → no (λ ())
    (absurd-clause tel ps) (absurd-clause tel₁ ps₁) → case (tel ≡ᵢ? tel₁ , ps ≡ᵢ? ps₁) of λ where
      (yes reflᵢ , yes reflᵢ) → yes reflᵢ
      (yes as , no ¬ps)       → no λ { reflᵢ → ¬ps reflᵢ }
      (no ¬as , _)            → no λ { reflᵢ → ¬as reflᵢ }

pi-view : Term → Telescope × Term
pi-view (pi a (abs n b)) with pi-view b
... | tele , t = ((n , a) ∷ tele) , t
pi-view t = [] , t

pi-impl-view : Term → Telescope × Term
pi-impl-view t@(pi (arg (arginfo visible _) _) _) = [] , t
pi-impl-view (pi a (abs n b)) with pi-impl-view b
... | tele , t = ((n , a) ∷ tele) , t
pi-impl-view t = [] , t

unpi-view : Telescope → Term → Term
unpi-view []            k = k
unpi-view ((n , a) ∷ t) k = pi a (abs n (unpi-view t k))

tel→lam : Telescope → Term → Term
tel→lam []                               t = t
tel→lam ((n , arg (arginfo v _) _) ∷ ts) t = lam v (abs n (tel→lam ts t))

{-
Turn a telescope into a list of arguments, with arguments of implicit Π types
recursively η-expanded to avoid Agda inserting implicit arguments.
Example:
  tel→args (a : {b : {c : C} → B} → A) = (λ {b} → a {λ {c} → b {c}})
-}
{-# TERMINATING #-}
tel→args : Nat → Telescope → List (Arg Term)
tel→args skip [] = []
tel→args skip ((_ , arg ai t) ∷ tel) = arg ai
  (tel→lam impl (var (skip + length tel + length impl) (tel→args 0 impl)))
  ∷ tel→args skip tel
  where
    impl = pi-impl-view t .fst

tel→pats : Nat → Telescope → List (Arg Pattern)
tel→pats skip [] = []
tel→pats skip ((_ , arg ai _) ∷ tel) = arg ai (var (skip + length tel)) ∷ tel→pats skip tel

list-term : List Term → Term
list-term []       = con (quote List.[]) []
list-term (x ∷ xs) = con (quote List._∷_) (argN x ∷ argN (list-term xs) ∷ [])

list-pattern : List (Arg Pattern) → Pattern
list-pattern []       = con (quote List.[]) []
list-pattern (x ∷ xs) = con (quote List._∷_) (x ∷ argN (list-pattern xs) ∷ [])

-- Notation class for the reflected in reflected syntax which have a
-- notion of neutrals, for which application is cheap. This is used to
-- support the _##_ family of operators.
record Has-neutrals {ℓ} (A : Type ℓ) : Type (lsuc ℓ) where
  field
    neutral : A → Type ℓ
    applyⁿᵉ : (d : A) ⦃ _ : neutral d ⦄ (arg : List (Arg A)) → A

open Has-neutrals ⦃ ... ⦄ using (applyⁿᵉ) public

module _ {ℓ} {A : Type ℓ} ⦃ a : Has-neutrals A ⦄ (d : A) ⦃ _ : Has-neutrals.neutral a d ⦄ where
  infixl 20 _##_ _##ₙ_ _##ᵢ_ _##ₕ_

  -- Apply a neutral to an argument with specified information.
  _##_ : (arg : Arg A) → A
  _##_ x = Has-neutrals.applyⁿᵉ a d (x ∷ [])

-- Apply a neutral to an argument with the default information.
  _##ₙ_ : (arg : A) → A
  _##ₙ_ x = _##_ (argN x)

  -- Apply a neutral to a hidden argument with the default modality.
  _##ₕ_ : (arg : A) → A
  _##ₕ_ x = _##_ (argH x)

  -- Apply a neutral to an instance argument with the default modality.
  _##ᵢ_ : (arg : A) → A
  _##ᵢ_ x = _##_ (argI x)

instance
  Has-neutrals-Term : Has-neutrals Term
  Has-neutrals-Term = record { neutral = neutral ; applyⁿᵉ = apply } where
    neutral : Term → Type
    neutral (def _ _)     = ⊤
    neutral (con _ _)     = ⊤
    neutral (meta _ _)    = ⊤
    neutral (var _ _)     = ⊤
    neutral (pat-lam _ _) = ⊤
    neutral _             = ⊥

    apply : (d : Term) ⦃ _ : neutral d ⦄ (arg : List (Arg Term)) → Term
    apply (def v as)      a = def v  (as ++ a)
    apply (con v as)      a = con v  (as ++ a)
    apply (meta m as)     a = meta m (as ++ a)
    apply (var v as)      a = var v  (as ++ a)
    apply (pat-lam cs as) a = pat-lam cs (as ++ a)
    apply (pi _ _)      ⦃ () ⦄ _
    apply (lam _ _)     ⦃ () ⦄ _
    apply (agda-sort _) ⦃ () ⦄ _

  Has-neutrals-Pattern : Has-neutrals Pattern
  Has-neutrals-Pattern = record { neutral = neutral ; applyⁿᵉ = apply } where
    neutral : Pattern → Type
    neutral (con _ _) = ⊤
    neutral _ = ⊥

    apply : (d : Pattern) ⦃ _ : neutral d ⦄ (arg : List (Arg Pattern)) → Pattern
    apply (con c ps) a = con c (ps ++ a)

pattern con₀ v = con v []
pattern def₀ v = def v []
pattern var₀ v = var v []

-- Test whether a term is "hereditarily atomic", i.e. it is a head
-- application and all of its arguments are hereditarily atomic.
is-atomic-tree? : Term → Bool
is-atomic-args? : List (Arg Term) → Bool

is-atomic-tree? (var x args)  = is-atomic-args? args
is-atomic-tree? (con c args)  = is-atomic-args? args
is-atomic-tree? (def f args)  = is-atomic-args? args
is-atomic-tree? (meta m args) = is-atomic-args? args
is-atomic-tree? (lit l)       = true
{-# CATCHALL #-}
is-atomic-tree? _             = false

is-atomic-args? [] = true
is-atomic-args? (arg _ x ∷ xs) with is-atomic-tree? x
... | true  = is-atomic-args? xs
... | false = false
