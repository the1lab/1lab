{-# OPTIONS -v refl:20 #-}
open import 1Lab.Reflection
open import 1Lab.HLevel.Retracts
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

import Agda.Builtin.Sigma as S

open import Data.Nat
open import Data.List

module 1Lab.HLevel.Auto where

data hlevel-oblig (n : Nat) : ∀ {ℓ ℓ′} → Type ℓ → Type ℓ′ → Typeω
record some-oblig (n : Nat) {ℓ} (T : Type ℓ) : Typeω where
  inductive
  constructor mk-so
  field
    ty : Type ℓ
    wit : hlevel-oblig n T ty
open some-oblig

data hlevel-oblig n where
  exact : ∀ {ℓ} {T : Type ℓ} → hlevel-oblig n T (is-hlevel T n)

  pi : ∀ {ℓ ℓ′} {A : Type ℓ} {T : A → Type ℓ′}
     → (f : ∀ x → some-oblig n (T x))
     → hlevel-oblig n ((x : A) → T x) ((x : A) → ty (f x))

  pi′
    : ∀ {ℓ ℓ′} {A : Type ℓ} {T : A → Type ℓ′}
    → (f : ∀ x → some-oblig n (T x))
    → hlevel-oblig n ({x : A} → T x) ((x : A) → ty (f x))

  sig : ∀ {ℓ ℓ′ ℓ′′} {A : Type ℓ} {T : A → Type ℓ′} {X : Type ℓ′′}
      → hlevel-oblig n A X
      → (f : ∀ x → some-oblig n (T x))
      → hlevel-oblig n (Σ[ x ∈ A ] T x) (Σ[ at ∈ X ] ((x : A) → ty (f x)))

  arr : ∀ {ℓ ℓ′} {A : Type ℓ} {T : Type ℓ′} {X : Type ℓ′}
      → hlevel-oblig n T X → hlevel-oblig n (A → T) X

  prod
    : ∀ {ℓt ℓto ℓs ℓso} {T : Type ℓt} {To : Type ℓto}
        {S : Type ℓs} {So : Type ℓso}
    → hlevel-oblig n T To → hlevel-oblig n S So
    → hlevel-oblig n (T × S) (To × So)

  path : ∀ {ℓ ℓ′} {T : Type ℓ} {X : Type ℓ′} {x y : T}
       → hlevel-oblig n T X
       → hlevel-oblig n (Path T x y) X

  path′ : ∀ {ℓ ℓ′} {T : Type ℓ} {X : Type ℓ′} {x y : T}
       → hlevel-oblig (suc n) T X
       → hlevel-oblig n (Path T x y) X

reify : ∀ {ℓ ℓ′} {T : Type ℓ} {k : Type ℓ′} {n : Nat}
      → hlevel-oblig n T k → k → is-hlevel T n
reify exact k = k
reify {n = n} (pi k) x = Π-is-hlevel n λ a → reify (k a .wit) (x a)
reify {n = n} (pi′ k) x =
  retract→is-hlevel n (λ f {x} → f x) (λ f x → f {x}) (λ _ → refl) $
    Π-is-hlevel n λ a → reify (k a .wit) (x a)
reify {n = n} (arr k) x = Π-is-hlevel n λ a → reify k x
reify {n = n} (sig x y) (a , b) = Σ-is-hlevel n (reify x a) λ o → reify (y o .wit) (b o)
reify {n = n} (prod x y) (a , b) = ×-is-hlevel n (reify x a) (reify y b)
reify {n = n} (path k) x = Path-is-hlevel n (reify k x)
reify {n = n} (path′ k) x = Path-is-hlevel' n (reify k x) _ _

getHlType : Nat → Term → TC Term
getHlType zero (def (quote is-contr) (_ h∷ t v∷ [])) = returnTC t
getHlType n (def (quote is-hlevel) (_ h∷ t v∷ _)) = returnTC t
getHlType (suc n) (pi (arg _ x) y) = returnTC x
getHlType _ tm = typeError (strErr "auto-hl: type " ∷ termErr tm ∷ strErr " is not h-level type" ∷ [])

make-oblig-term : Nat → Term → TC ⊤
make-oblig-term zero t = typeError (strErr "make-oblig-term ran out of fuel!" ∷ [])
make-oblig-term (suc n) t = do
    try1 (quote arr)
      <|> tryProd
      <|> trySigma
      <|> tryPi visible (quote hlevel-oblig.pi)
      <|> try1 (quote path)
      <|> try1 (quote path′)
      <|> useExact
  where
    useExact = do
      unify t (con (quote exact) [])

    try1 : Name → TC ⊤
    try1 x = do
      h2 ← newMeta unknown
      tt ← unify t (con x (h2 v∷ []))
      make-oblig-term n h2

    tryProd = do
      h1 ← newMeta unknown
      h2 ← newMeta unknown
      tt ← unify t (con (quote prod) (h1 v∷ h2 v∷ []))
      make-oblig-term n h1
      make-oblig-term n h2

    tryPi : Visibility → Name → TC ⊤
    tryPi vis sol = do
      dom ← newMeta unknown

      -- Create a new meta with a variable of the domain type in scope
      cod ← extendContext (varg dom) $ newMeta unknown
      type ← inferType t

      -- The scoping here is, to use the scientific term, all kinds of
      -- fucked up! We open the abstraction in the Π type to extract
      -- both the domain (which is closed wrt the environment we're
      -- working in) *and the codomain, which is OPEN*
      --
      -- Moreover if you try to use a type from outside inside the
      -- extendContext, since all the de Bruijn indices will be
      -- off-by-one, *mysterious type errors will happen*! Use `unknown`
      -- and let Agda figure out the scoping.

      unify
        (def (quote hlevel-oblig)
          (  unknown
          v∷ pi (arg (arg-info vis (modality relevant quantity-ω)) dom)
              (abs "_" cod)
          v∷ unknown v∷ []))
        type

      -- The lambda body is an *OPEN TERM* so that we can close over it
      -- when making the "pi" obligation
      λ-body ← extendContext (varg dom) $ do
        h2 ← newMeta (def (quote hlevel-oblig) (unknown v∷ cod v∷ unknown v∷ []))
        make-oblig-term n h2
        returnTC $ con (quote mk-so) (unknown v∷ h2 v∷ [])

      unify t (con sol (lam visible (abs "x" λ-body) v∷ []))

    trySigma = do
      dom ← newMeta unknown
      cod ← extendContext (varg dom) $ newMeta unknown

      type ← inferType t
      unify (def (quote hlevel-oblig)
        (  unknown
        v∷ def (quote S.Σ) (dom v∷ (lam visible (abs "_" cod)) v∷ [])
        v∷ unknown v∷ [])) type

      lm ← extendContext (varg dom) $ do
        h2 ← newMeta (def (quote hlevel-oblig) (unknown v∷ cod v∷ unknown v∷ []))
        make-oblig-term n h2
        returnTC $ con (quote mk-so) (unknown v∷ h2 v∷ [])

      fst ← newMeta (def (quote hlevel-oblig) (unknown v∷ dom v∷ unknown v∷ []))
      make-oblig-term n fst

      let
        solved = (con (quote hlevel-oblig.sig) (fst v∷ lam visible (abs "x" lm) v∷ []))
      unify t solved

macro
  auto-hlevel : ∀ {ℓ} {T : Type ℓ} → Nat → T → Term → TC ⊤
  auto-hlevel {T = T} hl inst goal = do
    `hl ← quoteTC hl
    ty ← inferType goal >>= normalise
    unify ty (def (quote is-hlevel) (unknown v∷ `hl v∷ []))
    goal-ty ← newMeta unknown
    inf-ty ← getHlType hl ty
    m ← newMeta (def (quote hlevel-oblig) (`hl v∷ inf-ty v∷ goal-ty v∷ []))
    make-oblig-term 10 m
    `inst ← quoteTC inst
    let
      solved =
        def (quote reify) (unknown h∷ unknown h∷ inf-ty h∷ m v∷ `inst v∷ [])
    unify goal solved

field-names→sigma : ∀ {ℓ} {A : Type ℓ} → List A → Term
field-names→sigma [] = def (quote ⊤) []
field-names→sigma (_ ∷ []) = unknown
field-names→sigma (_ ∷ xs) =
  def (quote Σ) (lam visible (abs "_" (field-names→sigma xs)) v∷ [])

Fields : Type
Fields = List (Name × List Name)
         --    ^ record projection

field-names→pair : List (Arg Name) → Term → (Term × Fields)
field-names→pair [] rec = con (quote tt) [] , []
field-names→pair (arg _ nm ∷ []) rec = def nm (rec v∷ []) , (nm , []) ∷ []
field-names→pair (arg _ x ∷ xs) rec with field-names→pair xs rec
... | term , fields = con (quote S._,_) (def x (rec v∷ []) v∷ term v∷ [])
                    , (x , quote fst ∷ []) ∷ map (λ (f , p) → f , quote snd ∷ p) fields

field-names→fields : List Name → List (Arg Name) → Fields
field-names→fields _ [] = []
field-names→fields pref (arg _ x ∷ []) = (x , pref) ∷ []
field-names→fields pref (arg _ x ∷ xs) =
  (x , quote fst ∷ pref) ∷ field-names→fields (quote snd ∷ pref) xs

onlyVis : ∀ {ℓ} {x : Type ℓ} → List (Arg x) → List x
onlyVis [] = []
onlyVis (arg (arg-info visible m) y ∷ xs)   = y ∷ onlyVis xs
onlyVis (arg (arg-info hidden m) y ∷ xs)    = onlyVis xs
onlyVis (arg (arg-info instance′ m) y ∷ xs) = onlyVis xs

record→iso : Name → Term → TC Term
record→iso namen unfolded =
  (inferType (def namen []) >>= normalise) >>= go []
  where
  go : List ArgInfo → Term → TC Term
  go acc (pi (arg i argTy) (abs s ty)) = do
    r ← (go (i ∷ acc) ty)
    returnTC $ pi (arg i' argTy) (abs s r)
    where
    i' = arg-info hidden (modality relevant quantity-ω)
  go acc (agda-sort _) = do
    let rec = def namen (makeArgs 0 [] acc)
    returnTC $ def (quote Iso) (rec v∷ unfolded v∷ [])
    where
    makeArgs : Nat → List (Arg Term) → List ArgInfo → List (Arg Term)
    makeArgs n acc [] = acc
    makeArgs n acc (i ∷ infos) = makeArgs (suc n) (arg i (var n []) ∷ acc) infos
  go _ _ = typeError (strErr "Not a record type name: " ∷ nameErr namen ∷ [])

undo-clauses : Fields → List Clause
undo-clauses = go where
  go : List (Name × List Name) → List Clause
  go [] = []
  go ((r-field , sel-path) ∷ xs) =
    clause (("sig" , varg unknown) ∷ [])
           (varg (proj (quote snd)) ∷ varg (proj (quote is-iso.inv)) ∷ varg (var 0) ∷ varg (proj r-field) ∷ [])
           (foldr (λ n t → def n (t v∷ [])) (var 0 []) (reverse sel-path))
      ∷ go xs

undo-redo-clauses : Fields → List Clause
undo-redo-clauses = go where
  go : Fields → List Clause
  go [] = []
  go ((r-field , _) ∷ xs) =
    clause (("sig" , varg unknown) ∷ ("i" , varg (quoteTerm I)) ∷ [])
           ( varg (proj (quote snd)) ∷ varg (proj (quote is-iso.linv))
           ∷ varg (var 1) ∷ varg (var 0) ∷ varg (proj r-field) ∷ [])
           (def r-field (var 1 [] v∷ []))
      ∷ go xs

make-record-iso-sigma : Name → TC Name
make-record-iso-sigma `R = do
  record-type _ fields ← getDefinition `R
    where _ → typeError (nameErr `R ∷ strErr " is not a record type" ∷ [])

  let (func , fields) = field-names→pair fields (var 0 [])
  let `S = field-names→sigma fields
  -- typeError (termErr (lam visible (abs "rec" func)) ∷ [])
  `fields ← quoteTC fields >>= normalise
  -- typeError (termErr `fields ∷ [])

  ty ← record→iso `R `S

  nm ← freshName "Σiso"
  decl ← declareDef (varg nm) ty
  defineFun nm
    ( clause (("rec" , varg unknown) ∷ [])
              (varg (proj (quote fst)) ∷ varg (var 0) ∷ [])
              func
    ∷ undo-clauses fields ++
    clause (("_" , varg unknown) ∷ [])
            (varg (proj (quote snd)) ∷ varg (proj (quote is-iso.rinv)) ∷ varg (var 0) ∷ [])
            (def (quote refl) [])
    ∷ undo-redo-clauses fields)
  returnTC nm

macro
  record≃sigma : ∀ {ℓ} (R : Type ℓ) → Term → TC ⊤
  record≃sigma R goal = do
    `R ← quoteTC R
    just R-nm ← returnTC $ getName `R
      where _ → typeError (strErr "Expression " ∷ termErr `R ∷ strErr " does not name a record type" ∷ [])
    nm ← make-record-iso-sigma R-nm
    unify goal (def (quote Iso→Equiv) (def nm [] v∷ []))

  sigma≃record : ∀ {ℓ} (R : Type ℓ) → Term → TC ⊤
  sigma≃record R goal = do
    `R ← quoteTC R
    just R-nm ← returnTC $ getName `R
      where _ → typeError (strErr "Expression " ∷ termErr `R ∷ strErr " does not name a record type" ∷ [])
    nm ← make-record-iso-sigma R-nm
    unify goal (def (quote _e⁻¹) (def (quote Iso→Equiv) (def nm [] v∷ []) v∷ []))