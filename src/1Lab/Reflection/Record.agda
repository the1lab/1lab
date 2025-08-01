{-# OPTIONS -v refl:20 #-}
open import 1Lab.Reflection.Signature
open import 1Lab.Reflection.Subst
open import 1Lab.Reflection
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

open import Meta.Foldable
open import Meta.Append

import Prim.Data.Sigma as S
import Prim.Data.Nat as N

module 1Lab.Reflection.Record where

Fields : Type
Fields = List (Name × List Name)

-- Annotate a list of field names with a "projection path" to access
-- them in the corresponding Σ-type.
-- Example: [f1, f2, f3] ↦ [(f1, .fst), (f2, .snd .fst), (f3, .snd .snd)]
field-names→paths : List (Arg Name) → Fields
field-names→paths [] = []
field-names→paths (arg _ nm ∷ []) = (nm , []) ∷ []
field-names→paths (arg _ x  ∷ (y ∷ ys)) with field-names→paths (y ∷ ys)
... | fields = (x , quote fst ∷ []) ∷ map (λ (f , p) → f , quote snd ∷ p) fields

-- Given the name of a record type and the corresponding Σ-type, generate
-- the type of the corresponding iso helper.
-- Example: ∀ {xs : Δ} → Iso (R xs) (Σ A (Σ B C))
record→iso : Name → Term → TC Term
record→iso namen unfolded = go [] =<< normalise =<< get-type namen where
  go : List ArgInfo → Term → TC Term
  go acc (pi argu@(arg i argTy) (abs s ty)) = do
    -- If `go` ever needs the TC context to be correct, uncomment the
    -- following line.
    r ← -- extend-context "arg" argu $
        go (i ∷ acc) ty
    pure $ pi (argH argTy) (abs s r)

  go acc (agda-sort _) = do
    let rec = def namen (reverse (map-up (λ n i → arg i (var n [])) 0 acc))
    pure $ def (quote Iso) (rec v∷ unfolded v∷ [])

  go _ _ = typeError [ "Not a record type name: " , nameErr namen ]

-- Given the name of a record type, generate the type of the
-- corresponding path constructor.
-- Example: ∀ {xs : Δ} {r1 r2 : R xs} p1 p2 p3 → r1 ≡ r2
record→path : Name → List (Arg Name) → TC Term
record→path namen fields = go [] =<< normalise =<< get-type namen where
  go : List ArgInfo → Term → TC Term
  go acc (pi argu@(arg i argTy) (abs s ty)) = do
    -- If `go` ever needs the TC context to be correct, uncomment the
    -- following line.
    r ← -- extend-context "arg" argu $
        go (i ∷ acc) ty
    pure $ pi (argH argTy) (abs s r)

  go acc (agda-sort _) = do
    let rec = def namen (reverse (map-up (λ n i → arg i (var n [])) 0 acc))
    let n = length fields
    pure $ pi (argH rec) $ abs "r1"
         $ pi (argH (raise 1 rec)) $ abs "r2"
         $ foldr (λ _ x → pi (argN unknown) (abs "p" x))
          (def (quote _≡_) (var (suc n) [] v∷ var n [] v∷ []))
          fields

  go _ _ = typeError [ "Not a record type name: " , nameErr namen ]

-- Generate the clauses of the isomorphism corresponding to the given field.
undo-clause : Name × List Name → Clause
undo-clause (r-field , sel-path) = clause
  (("sig" , argN unknown) ∷ [])
  [ argN (proj (quote snd))
  , argN (proj (quote is-iso.from))
  , argN (var 0)
  , argN (proj r-field)
  ]
  (foldr (λ n t → def n (t v∷ [])) (var 0 []) (reverse sel-path))

redo-clause : Name × List Name → Clause
redo-clause (r-field , sel-path) = clause
  (("rec" , argN unknown) ∷ [])
  (argN (proj (quote fst)) ∷ argN (var 0) ∷ map (argN ∘ proj) sel-path)
  (def r-field (var 0 [] v∷ []))

undo-redo-clause : Name × List Name → Clause
undo-redo-clause ((r-field , _)) = clause
  (("sig" , argN unknown) ∷ ("i" , argN (quoteTerm I)) ∷ [])
  ( argN (proj (quote snd)) ∷ argN (proj (quote is-iso.linv))
  ∷ argN (var 1) ∷ argN (var 0) ∷ argN (proj r-field) ∷ [])
  (def r-field (var 1 [] v∷ []))

redo-undo-clause : Name × List Name → Clause
redo-undo-clause (r-field , sel-path) = clause
  (("rec" , argN unknown) ∷ ("i" , argN (quoteTerm I)) ∷ [])
  (  [ argN (proj (quote snd)) , argN (proj (quote is-iso.rinv)) , argN (var 1) , argN (var 0) ]
  <> map (argN ∘ proj) sel-path)
  (foldr (λ n t → def n (t v∷ [])) (var 1 []) (reverse sel-path))

-- Transform the type of a record constructor into a Σ-type isomorphic
-- to the record.
pi-term→sigma : Term → TC Term
pi-term→sigma (pi (arg _ x) (abs n (def n' _))) = pure x
pi-term→sigma (pi (arg _ x) (abs n y)) = do
  sig ← pi-term→sigma y
  pure $ def (quote S.Σ) (x v∷ lam visible (abs n sig) v∷ [])
pi-term→sigma _ = typeError (strErr "Not a record type constructor! " ∷ [])

instantiate' : Term → Term → Term
instantiate' (pi _ (abs _ xs)) (pi _ (abs _ b)) = instantiate' xs b
instantiate' (agda-sort _) tm = tm
instantiate' _ tm = tm

-- Assemble the last n variables into a path in a Σ-type.
Σ-pathpⁿ : Nat → Term
Σ-pathpⁿ zero = unknown -- empty record types are not supported
Σ-pathpⁿ (suc zero) = var zero []
Σ-pathpⁿ (suc (suc n)) = def (quote Σ-pathp) (var (suc n) [] v∷ Σ-pathpⁿ (suc n) v∷ [])

make-record-iso-sigma : Bool → Name → Name → TC ⊤
make-record-iso-sigma declare? nm `R = do
  `R-con , fields ← get-record-type `R

  let fields = field-names→paths fields

  when declare? do
    `R-ty ← normalise =<< get-type `R
    con-ty ← normalise =<< get-type `R-con
    let con-ty = instantiate' `R-ty con-ty
    unfolded ← pi-term→sigma con-ty
    ty ← record→iso `R unfolded
    declare (argN nm) ty

  define-function nm
    ( map redo-clause fields ++
      map undo-clause fields ++
      map redo-undo-clause fields ++
      map undo-redo-clause fields)

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

You can also use

  unquoteDecl R-path = declare-record-path R-path (quote R)

to define a "path constructor" helper for building a path between two
elements of R. Defining PathPs over paths in the record's parameters is
not (yet) supported.
-}

declare-record-iso : Name → Name → TC ⊤
declare-record-iso = make-record-iso-sigma true

define-record-iso : Name → Name → TC ⊤
define-record-iso = make-record-iso-sigma false

make-record-path : Bool → Name → Name → TC ⊤
make-record-path declare? nm `R = do
  eqv ← helper-function-name nm "eqv"
  declare-record-iso eqv `R
  `R-con , fields ← get-record-type `R
  let n = length fields

  when declare? do
    `R-ty ← normalise =<< get-type `R
    ty ← record→path `R fields
    declare (argN nm) ty

  define-function nm
    [ clause
      (map (λ _ → "p" , argN unknown) fields)
      (map-up (λ i _ → argN (var (n - i))) 1 fields)
      (def (quote Iso.injective) (def eqv [] v∷ Σ-pathpⁿ n v∷ []))
    ]

declare-record-path : Name → Name → TC ⊤
declare-record-path = make-record-path true

define-record-path : Name → Name → TC ⊤
define-record-path = make-record-path false

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

  unquoteDecl T-path = declare-record-path T-path (quote T)

  _ : {ℓ : Level} {A : Type ℓ} {t1 t2 : T A} → ∀ a b c → t1 ≡ t2
  _ = T-path

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
