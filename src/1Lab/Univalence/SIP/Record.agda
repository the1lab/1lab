open import 1Lab.Univalence.SIP.Record.Parse
open import 1Lab.Univalence.SIP.Record.Base
open import 1Lab.Univalence.SIP.Record.Prop
open import 1Lab.Univalence.SIP.Auto
open import 1Lab.Univalence.SIP
open import 1Lab.Reflection
open import 1Lab.Type.Sigma
open import 1Lab.Univalence
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

open import Agda.Builtin.List

open import Data.List

module 1Lab.Univalence.SIP.Record where

private
  pathMap
    : ∀ {ℓ ℓ'} {S : I → Type ℓ} {T : I → Type ℓ'}
      → (f : {i : I} → S i → T i)
      → {x : S i0} {y : S i1}
      → PathP S x y → PathP T (f x) (f y)

  pathMap f p i = f (p i)

  -- Build proof of univalence from an isomorphism
  module _ {ℓ ℓ₁ ℓ₁'} (S : Type ℓ → Type ℓ₁) (ι : IsHomT ℓ₁' S) where
    fwdShape : Type _
    fwdShape =
        (A B : Σ S) (e : A .fst ≃ B .fst)
      → ι A B e → PathP (λ i → S (ua e i)) (A .snd) (B .snd)

    bwdShape : Type _
    bwdShape =
        (A B : Σ S) (e : A .fst ≃ B .fst)
      → PathP (λ i → S (ua e i)) (A .snd) (B .snd) → ι A B e

    fwdBwdShape : fwdShape → bwdShape → Type _
    fwdBwdShape fwd bwd =
      (A B : Σ S) (e : A .fst ≃ B .fst) → ∀ p → fwd A B e (bwd A B e p) ≡ p

    bwdFwdShape : fwdShape → bwdShape → Type _
    bwdFwdShape fwd bwd =
      (A B : Σ S) (e : A .fst ≃ B .fst) → ∀ r → bwd A B e (fwd A B e r) ≡ r

    explicitUnivalentStr : (fwd : fwdShape) (bwd : bwdShape)
      → fwdBwdShape fwd bwd → bwdFwdShape fwd bwd
      → isUnivalent' S ι
    explicitUnivalentStr fwd bwd fwdBwd bwdFwd A B e = Iso→Equiv isom
      where
      open isIso
      isom : Iso _ _
      isom .fst = fwd A B e
      isom .snd .inv = bwd A B e
      isom .snd .rinv = fwdBwd A B e
      isom .snd .linv = bwdFwd A B e

-- Build an isomorphism given a Spec numbered with the variables of each
-- pre-built equivalence. More explicitly, the iso built is a term with
-- [the max number in the spec] free variables, which should be closed
-- over and applied to proofs that the respective fields are univalent.

-- In more detail: For a specification
--
--    record: field[ X by P ] axiom[ Y by Q ]
--    where:
--      X : S X → R X
--      P : IsHomT R
--      Y : S X → Prop -- roughly
--      Q : isProp (Y _) -- roughly
--
-- The isomorphism built has type
--   isUnivalent' R P → PropHelperType Y Q → isUnivalent' S H
private module _ (spec : Spec Nat) where
  open Spec spec

  -- is-hom → Path for a structure field
  fwdDatum : Vec Term 4
           -- A , B , equiv : A ≃ B , streq : is-hom equiv
           → Term -- endpoint : I
           → Name × Name × Nat
           -- field accessor for structure , field accessor for homomorphism
           -- free variable in which we get the proof that this field is built
           -- from a univalent structure
           → Term
  fwdDatum (A ∷ B ∷ e ∷ streq ∷ []) i (struct-field , pres-field , n) =
    def (quote equivFun)
      (tApply (var n []) (tStrProj A struct-field v∷ tStrProj B struct-field v∷ e v∷ [])
        v∷ def pres-field (streq v∷ [])
        v∷ i
        v∷ [])
    -- equivFun n (A .field) (B .field) equiv .preserves streq i

  -- Centre of contraction of the path space of P (prevPath i) (because
  -- P is propositional)
  fwdProperty : Vec Term 4 → Term → Term → Name × Nat → Term
  fwdProperty (A ∷ B ∷ e ∷ streq ∷ _) i prevPath the-prop =
    def (quote fst) (var (the-prop .snd) [] v∷ A v∷ B v∷ e v∷ prevPath v∷ i v∷ [])

  -- Path → is-hom for a structure field. Uses the assumption of
  -- univalence for the structure. Prop fields don't need backwards
  -- clauses.
  bwdClause : Vec Term 4
            → Name × Name × Nat
            → Clause
  bwdClause (A ∷ B ∷ e ∷ q ∷ []) (struct-field , pres-field , n) =
    clause [] (proj pres-field v∷ [])
      (def (quote equivInv)
        (tApply
          (var n [])
          (tStrProj A struct-field v∷ tStrProj B struct-field v∷ e v∷ [])
          v∷ def (quote pathMap) (def struct-field [] v∷ q v∷ [])
          v∷ []))

  -- Proof that fwd ∘ bwd ≡ id. Relies on the assumption that all fields
  -- are univalent structures.
  fwdBwdDatum : Vec Term 4
              → Term → Term → Name × Name × Nat
              → Term
  fwdBwdDatum (A ∷ B ∷ e ∷ q ∷ []) j i (struct-field , pres-field , n) =
    def (quote equivSec)
      (tApply
        (var n [])
        (tStrProj A struct-field v∷ tStrProj B struct-field v∷ e v∷ [])
        v∷ def (quote pathMap) (def struct-field [] v∷ q v∷ [])
        v∷ j v∷ i
        v∷ [])

    -- equivSec n (A .field) (B .field) equiv .field streq j i

  -- Contraction paths for the path space of P (prevPath i) (because P
  -- is propositional). Connects whatever we were given to the choice we
  -- made in fwdProperty
  fwdBwdProperty : Vec Term 4 → (j i prevPath : Term)
                 → Name × Nat → Term
  fwdBwdProperty (A ∷ B ∷ e ∷ q ∷ _) j i prevPath (_ , n) =
    def (quote snd) (var n [] v∷ A v∷ B v∷ e v∷ q v∷ prevPath v∷ j v∷ i v∷ [])


  -- Path → is-hom for a structure field. Uses the assumption of
  -- univalence for the structure. Prop fields don't need backwards
  -- clauses.
  bwdFwdClause : Vec Term 4
               → Term
               → Name × Name × Nat
               → Clause
  bwdFwdClause (A ∷ B ∷ e ∷ streq ∷ []) j (struct-field , pres-field , n) =
    clause [] (proj pres-field v∷ [])
      (def (quote equivRet)
        (tApply
          (var n [])
          (tStrProj A struct-field v∷ tStrProj B struct-field v∷ e v∷ [])
          v∷ def pres-field (streq v∷ []) v∷ j v∷ []))

  -- ι A B e → PathP (λ i → S (ua e i)) (A .snd) (B .snd)
  fwd : Term
  fwd = vlam "A" (vlam "B" (vlam "e" (vlam "streq" (vlam "i" (pat-lam body [])))))
    where
      fwdClauses : Nat → List (InternalField × Nat)
                 → List (Name × Term) → List (Name × Term)

      fwdClauses k [] = id

      -- Clause for a structure field: use fwdDatum to piggyback off the
      -- assumption that all structure fields are univalent structures
      fwdClauses k ((structureField str pres , n) ∷ fs) =
        ((str , fwdDatum (makeVarsFrom k) (var 0 []) (str , pres , 4 + k + n))
          ∷_) ∘ fwdClauses k fs

      -- For a property field: *HAS TO GO AFTER THE STRUCTURE IT
      -- MENTIONS* (hence we put it AFTER fs - by the type of
      -- RecordFields' constructors the prop can only depend on fs)
      fwdClauses k ((propertyField namen , n) ∷ fs) =
         fwdClauses k fs ∘
          ((namen , fwdProperty (makeVarsFrom k) (var 0 [])
                      prevPath (namen , 4 + k + n))
          ∷_)
        where
          prevPath =
            vlam "i"
              (foldl
                (λ t (_ , t') → con (quote _,_) (t v∷ t' v∷ []))
                (con (quote tt) [])
                (reverse (fwdClauses (suc k) fs [])))

      body =
        map (λ (n , t) → clause [] (varg (proj n) ∷ []) t) (fwdClauses 1 fields [])

  -- PathP (λ i → S (ua e i)) (A .snd) (B .snd) → ι A B e
  bwd : Term
  bwd = vlam "A" (vlam "B" (vlam "e" (vlam "q" (pat-lam (bwdClauses fields) []))))
    where
      bwdClauses : List (InternalField × Nat) → List Clause
      bwdClauses [] = []
      bwdClauses ((structureField struct-field pres-field , n) ∷ fs) =
        bwdClause (makeVarsFrom 0) (struct-field , pres-field , 4 + n)
        ∷ bwdClauses fs
      bwdClauses ((propertyField _ , _) ∷ fs) = bwdClauses fs

  fwdBwd : Term
  fwdBwd = vlam "A" (vlam "B" (vlam "e"
             (vlam "q" (vlam "j" (vlam "i" (pat-lam body []))))))
    where
      fwdBwdClauses : Nat → List (InternalField × Nat)
                    → List (Name × Term) → List (Name × Term)
      fwdBwdClauses k [] = id
      fwdBwdClauses k ((structureField struct pres , n) ∷ fs) =
        ((struct , fwdBwdDatum (makeVarsFrom k)
                    (var 1 [])
                    (var 0 [])
                    (struct , pres , 4 + k + n))
        ∷_) ∘ fwdBwdClauses k fs

      -- For a property field: *HAS TO GO AFTER THE STRUCTURE IT
      -- MENTIONS* (hence we put it AFTER fs - by the type of
      -- RecordFields' constructors the prop can only depend on fs)
      fwdBwdClauses k ((propertyField namen , n) ∷ fs) =
        fwdBwdClauses k fs ∘
        ((namen , fwdBwdProperty (makeVarsFrom k)
           (var 1 []) (var 0 []) prevPath (namen , 4 + k + n)) ∷_)
        where
          prevPath =
            vlam "j" (vlam "i"
              (foldl
                (λ t (_ , t') → con (quote _,_) (t v∷ t' v∷ []))
                (con (quote tt) [])
                (reverse (fwdBwdClauses (2 + k) fs []))))

      body = map (λ (n , t) → clause [] (varg (proj n) ∷ []) t)
              (fwdBwdClauses 2 fields [])

  bwdFwd : Term
  bwdFwd = vlam "A" (vlam "B" (vlam "e"
            (vlam "streq" (vlam "j" (pat-lam (bwdFwdClauses fields) [])))))
    where
      bwdFwdClauses : List (InternalField × Nat) → List Clause
      bwdFwdClauses [] = []
      bwdFwdClauses ((structureField struct pres , n) ∷ fs) =
        bwdFwdClause (makeVarsFrom 1) (var 0 []) (struct , pres , 5 + n)
        ∷ bwdFwdClauses fs
      bwdFwdClauses ((propertyField _ , _) ∷ fs) = bwdFwdClauses fs

  -- Iso→Equiv, roughly
  univalentRecord : Term
  univalentRecord = do
    def (quote explicitUnivalentStr)
      (unknown v∷ unknown v∷ fwd v∷ bwd v∷ fwdBwd v∷ bwdFwd v∷ [])

private module _ (spec : Spec TypedTm) where
  open Spec

  -- Since RecordFields is built up out of "snocs", but parseFields
  -- transforms it into "conses" without reversing, the fields we have
  -- here are in the wrong order.
  private
    actual-fields = reverse (spec .fields)

  -- It's actually fine not to reverse the fields here - the code to
  -- generate fwd/bwd/fwdBwd/bwdFwd is written with the assumption that
  -- the fields are in the inverse order and the free variables are in
  -- the correct oder.
  closed-over-spec : Spec Nat
  closed-over-spec .structure = spec .structure
  closed-over-spec .homomorphism = spec .homomorphism
  closed-over-spec .fields = mapUp (λ n → Σ-map₂ (λ _ → n)) 0 (spec .fields)

  -- The actual executable code for the isomorphism. Has a bunch of free
  -- variables which we quantify over.
  closure : Term
  closure = iter (length (spec .fields)) (vlam "var")
    (univalentRecord closed-over-spec)

  -- Each of these free variables is an assumption discharged by one of
  -- the fields, e.g. that a certain structure field is a univalent
  -- structure, or that an axiomatic field is propositional.
  environment : List (Arg Term)
  environment = map (varg ∘ TypedTm.term ∘ snd) actual-fields

  -- Since we made a function but not a top-level definition for it, we
  -- have to generate a type. Then we use an explicitly-typed id
  -- function as a type ascription.
  closure-type : Term
  closure-type =
    foldr (λ ty cod → “ ty ↦ cod ”)
          (def (quote isUnivalent') (spec .structure v∷ spec .homomorphism v∷ []))
          (map (TypedTm.type ∘ snd) actual-fields)

  spec→isUnivalent : Term
  spec→isUnivalent = def (quote idfun) (closure-type v∷ closure v∷ environment)

macro
  autoUnivalentRecord : Term → Term → TC ⊤
  autoUnivalentRecord spec goal = do
    spec ← reduce spec >>= parseSpec
    unify goal
      (def (quote repackage)
        (  spec .Spec.structure
        v∷ spec .Spec.homomorphism
        v∷ spec→isUnivalent spec
        v∷ []))
