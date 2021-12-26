open import 1Lab.Univalence.SIP
open import 1Lab.Reflection
open import 1Lab.Type.Sigma
open import 1Lab.Univalence
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

open import Data.List

module 1Lab.Univalence.SIP.Record.Base where

IsHomT : ∀ {ℓ ℓ₁} (l : Level) → (Type ℓ → Type ℓ₁) → Type _
IsHomT l S = (A B : Σ S) → (A .fst ≃ B .fst) → Type l

-- We declare, inductively-recursively(!), a syntax for describing how
-- to project the fields _and_ their corresponding presentation
-- properties from a pair of records. Here are the signatures for stuff
-- involved in the recursion:
module _ {ℓ ℓ₁ ℓ₁'} where
  -- Actual descriptors for record fields
  data RecordFields (R : Type ℓ → Type ℓ₁) (ι : IsHomT ℓ₁' R) : Typeω

  -- Computes the LUB level of the fields described
  level-of-fields→prod
    : {R : Type ℓ → Type ℓ₁} {ι : IsHomT ℓ₁' R}
    → RecordFields R ι
    → Level
  
  -- Computes a nested product type of the fields described
  fields→prod
    : {R : Type ℓ → Type ℓ₁} {ι : IsHomT ℓ₁' R}
      (fields : RecordFields R ι)
    → Type ℓ → Type (level-of-fields→prod fields)

  -- Projects the fields described into the nested product type
  -- structure
  project-fields
    : {R : Type ℓ → Type ℓ₁} {ι : IsHomT ℓ₁' R}
      (fs : RecordFields R ι)
    → {X : Type ℓ} → R X → fields→prod fs X

  -- What it means for P to be a proposition over the fields fs
  isPropProperty
    : ∀ {ℓ₂} (R : Type ℓ → Type ℓ₁) (ι : IsHomT ℓ₁' R)
        (fs : RecordFields R ι)
        (P : (X : Type ℓ) → fields→prod fs X → Type ℓ₂)
    → Type (lsuc ℓ ⊔ ℓ₁ ⊔ ℓ₂)
  isPropProperty R ι fs P =
    {X : Type ℓ} (r  : R X) → isProp (P X (project-fields fs r))

  -- Now the actual definitions.
  data RecordFields R ι where
    -- The empty record descriptor
    record: : RecordFields R ι

    -- Project a field (must not depend on previous fields of the
    -- record)
    _field[_by_]
      : (previous-fields : RecordFields R ι)

      → ∀ {ℓ₂ ℓ₂'} {S : Type ℓ → Type ℓ₂} {ι' : IsHomT ℓ₂' S}
      --           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
      --           These arguments specify a notion of structure
      --           for the field

      → (project : {X : Type ℓ} → R X → S X)
      -- ^ Projection from the record to the notion of structure

      → (project-preservation : {A B : Σ R} {e : A .fst ≃ B .fst}
                              → ι A B e
                              → ι' (Σ-map₂ project A) (Σ-map₂ project B) e)
      -- ^ Corresponding preservation datum for the field

      → RecordFields R ι

    -- Project a proposition/predicate, which /can/ depend on previous
    -- fields of the record.
    _axiom[_by_]
      : (previous-fields : RecordFields R ι)
      -- ^ The previous fields

      → ∀ {ℓ₂} {P : (X : Type ℓ) → fields→prod previous-fields X → Type ℓ₂}
      --       ^ The actual proposition

      → (predicate : {X : Type ℓ} (r : R X) → P X (project-fields previous-fields r))
      -- ^ Extract a proof of the proposition from the record

      → isPropProperty R ι previous-fields P
      -- ^ "Preservation datum" (P must be a proposition)

      → RecordFields R ι

  level-of-fields→prod record: = lzero
  level-of-fields→prod (_field[_by_] fs {ℓ₂ = ℓ₂} _ _) =
    level-of-fields→prod fs ⊔ ℓ₂
  level-of-fields→prod (_axiom[_by_] fs {ℓ₂ = ℓ₂} _ _) =
    level-of-fields→prod fs ⊔ ℓ₂

  fields→prod record: _ = ⊤
  fields→prod (_field[_by_] fs {S = S} _ _) X =
    fields→prod fs X × S X
  fields→prod (_axiom[_by_] fs {P = P} _ _) X =
    Σ[ S ∈ fields→prod fs X ] (P X S)

  project-fields record: x₁ = tt
  project-fields (x field[ project by project-preservation ]) str =
    project-fields x str , project str
  project-fields (x axiom[ x₂ by x₃ ]) x₁ =
    (project-fields x x₁) , x₂ x₁

data AutoRecord : Typeω where
  autoRecord : ∀ {ℓ ℓ₁ ℓ₁'}
             → (R : Type ℓ → Type ℓ₁) (ι : IsHomT ℓ₁' R)
             → RecordFields R ι
             → AutoRecord

  -- ^ Package a record, notion of structure, and field descriptors onto
  -- an AutoRecord that the autoUnivalentRecord macro can consume.

isUnivalent' : ∀ {ℓ ℓ₁ ℓ₂} (S : Type ℓ → Type ℓ₁) → IsHomT ℓ₂ S → Type _
isUnivalent' S ι =
  ∀ (X Y : _)
  → (f : X .fst ≃ Y .fst)
  → ι X Y f ≃ PathP (λ i → S (ua f i)) (X .snd) (Y .snd)

tm→isHomT : ∀ {ℓ ℓ₁} {S} (tm : StrTm ℓ ℓ₁ S) → IsHomT ℓ₁ S
tm→isHomT tm = tm→Structure tm .is-hom

tm→⌜isUnivalent⌝ : ∀ {ℓ ℓ₁} {S} (tm : StrTm ℓ ℓ₁ S) → Type _
tm→⌜isUnivalent⌝ tm = isUnivalent' _ (tm→isHomT tm)

tm→isUnivalent' : ∀ {ℓ ℓ₁} {S} (tm : StrTm ℓ ℓ₁ S) → isUnivalent' S (tm→isHomT tm)
tm→isUnivalent' tm X Y f = tm→Structure-univalent tm f

isUnivalent'→isUnivalent
  : ∀ {ℓ ℓ₁ ℓ₂ : Level} (S : Type ℓ → Type ℓ₁)
  → (ι : IsHomT ℓ₂ S)
  → isUnivalent' S ι
  → isUnivalent {ℓ = ℓ₂} {S = S} (HomT→Str ι)
isUnivalent'→isUnivalent S ι ua {X} {Y} = ua X Y

record TypedTm : Type where
  field type : Term
        term : Term

data InternalField : Type where
  structureField : Name → Name → InternalField
  propertyField : Name → InternalField

record Spec (A : Type) : Type where
  field
    structure    : Term
    homomorphism : Term
    fields : List (InternalField × A)
