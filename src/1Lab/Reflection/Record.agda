{-# OPTIONS -v refl:20 #-}
open import 1Lab.Reflection
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

open import Data.List

import Agda.Builtin.Sigma as S
import Agda.Builtin.Nat as N

module 1Lab.Reflection.Record where

field-names→sigma : ∀ {ℓ} {A : Type ℓ} → List A → Term
field-names→sigma [] = def (quote ⊤) []
field-names→sigma (_ ∷ []) = unknown
field-names→sigma (_ ∷ xs) =
  def (quote Σ) (lam visible (abs "_" (field-names→sigma xs)) v∷ [])

Fields : Type
Fields = List (Name × List Name)

field-names→paths : List (Arg Name) → Fields
field-names→paths [] = []
field-names→paths (arg _ nm ∷ []) = (nm , []) ∷ []
field-names→paths (arg _ x ∷ xs) with field-names→paths xs
... | fields = (x , quote fst ∷ []) ∷ map (λ (f , p) → f , quote snd ∷ p) fields

record→iso : Name → (List (Arg Term) → TC Term) → TC Term
record→iso namen unfolded =
  (inferType (def namen []) >>= normalise) >>= go []
  where
  go : List ArgInfo → Term → TC Term
  go acc (pi argu@(arg i argTy) (abs s ty)) = do
    r ← extendContext argu $ go (i ∷ acc) ty
    returnTC $ pi (arg i' argTy) (abs s r)
    where
    i' = arg-info hidden (modality relevant quantity-ω)
  go acc (agda-sort _) = do
    let rec = def namen (makeArgs 0 [] acc)
    unfolded ← unfolded (implicitArgs 0 [] acc)
    returnTC $ def (quote Iso) (rec v∷ unfolded v∷ [])
    where
      makeArgs : Nat → List (Arg Term) → List ArgInfo → List (Arg Term)
      makeArgs n acc [] = acc
      makeArgs n acc (i ∷ infos) = makeArgs (suc n) (arg i (var n []) ∷ acc) infos

      implicitArgs : Nat → List (Arg Term) → List ArgInfo → List (Arg Term)
      implicitArgs n acc [] = acc
      implicitArgs n acc (_ ∷ i) = implicitArgs (suc n) (var n [] h∷ acc) i
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

redo-clauses : Fields → List Clause
redo-clauses = go where
  go : List (Name × List Name) → List Clause
  go [] = []
  go ((r-field , sel-path) ∷ xs) =
    clause (("rec" , varg unknown) ∷ [])
           (varg (proj (quote fst)) ∷ varg (var 0) ∷ map (varg ∘ proj) sel-path)
           (def r-field (var 0 [] v∷ []))
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

redo-undo-clauses : Fields → List Clause
redo-undo-clauses = go where
  go : List (Name × List Name) → List Clause
  go [] = []
  go ((r-field , sel-path) ∷ xs) =
    clause (("rec" , varg unknown) ∷ ("i" , varg (quoteTerm I)) ∷ [])
           (varg (proj (quote snd)) ∷ varg (proj (quote is-iso.rinv)) ∷ varg (var 1) ∷ varg (var 0) ∷ map (varg ∘ proj) sel-path)
           (foldr (λ n t → def n (t v∷ [])) (var 1 []) (reverse sel-path))
      ∷ go xs

pi-term→sigma : Term → TC Term
pi-term→sigma (pi (arg _ x) (abs n (def n′ _))) = returnTC x
pi-term→sigma (pi (arg _ x) (abs n y)) = do
  sig ← pi-term→sigma y
  returnTC $ def (quote S.Σ) (x v∷ lam visible (abs n sig) v∷ [])
pi-term→sigma _ = typeError (strErr "Not a record type constructor! " ∷ [])

instantiate′ : Term → Term → Term
instantiate′ (pi _ (abs _ xs)) (pi _ (abs _ b)) = instantiate′ xs b
instantiate′ (agda-sort _) tm = tm
instantiate′ _ tm = tm

make-record-iso-sigma : Bool → TC Name → Name → TC Name
make-record-iso-sigma declare? getName `R = do
  record-type `R-con fields ← getDefinition `R
    where _ → typeError (nameErr `R ∷ strErr " is not a record type" ∷ [])

  let fields = field-names→paths fields

  `R-ty ← getType `R
  con-ty ← getType `R-con
  ty ← record→iso `R λ args → do
    let con-ty = instantiate′ `R-ty con-ty
    `S ← pi-term→sigma con-ty
    returnTC `S

  nm ← getName
  returnTC declare? >>= λ where
    true → declareDef (varg nm) ty
    false → returnTC tt

  defineFun nm
    ( redo-clauses fields ++
      undo-clauses fields ++
      redo-undo-clauses fields ++
      undo-redo-clauses fields)
  returnTC nm

{-
Usage: slap

  unquoteDecl eqv = declare-record-iso eqv (quote Your-record)

in a module! The macro *DOES NOT WORK* in where clauses (or in record
definitions!). It does work in arbitrarily nested modules, and in the
top-level module, as the example below demonstrates: we can declare the
isomorphism adjacent to the record, outside the module where the record
is defined, and in a different module altogether.

All features of non-recursive records are supported, including
no-eta-equality, implicit and instance fields, and fields with implicit
arguments as types.
-}

declare-record-iso : Name → Name → TC ⊤
declare-record-iso nm rec = do
  make-record-iso-sigma true (returnTC nm) rec
  returnTC tt

define-record-iso : Name → Name → TC ⊤
define-record-iso nm rec = do
  make-record-iso-sigma false (returnTC nm) rec
  returnTC tt

private
  module _ {ℓ} (A : Type ℓ) where
    record T : Type ℓ where
      no-eta-equality
      field
        ⦃ fp ⦄ : A
        {f} : A → A
        fixed : f fp ≡ fp

    unquoteDecl eqv = declare-record-iso eqv (quote T)

    _ : Iso T (S.Σ A (λ fp → S.Σ (A → A) (λ f → f fp ≡ fp)))
    _ = eqv

  unquoteDecl eqv-outside = declare-record-iso eqv-outside (quote T)

  _ : {ℓ : Level} {A : Type ℓ} → Iso (T A) (S.Σ A (λ fp → S.Σ (A → A) (λ f → f fp ≡ fp)))
  _ = eqv-outside

  module _ (x : Nat) where
    unquoteDecl eqv-extra = declare-record-iso eqv-extra (quote T)

  _ : Nat → {ℓ : Level} {A : Type ℓ}
    → Iso (T A) (S.Σ A (λ fp → S.Σ (A → A) (λ f → f fp ≡ fp)))
  _ = eqv-extra

  record T2 : Type where
    -- works without eta equality too
    field
      some-field : Nat

  s-eqv : Iso T2 Nat
  unquoteDef s-eqv = define-record-iso s-eqv (quote T2)
