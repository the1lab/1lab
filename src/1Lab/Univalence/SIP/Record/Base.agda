open import 1Lab.Data.Sigma.Properties
open import 1Lab.Data.List
open import 1Lab.Univalence.SIP
open import 1Lab.Univalence
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type
open import 1Lab.Reflection

module 1Lab.Univalence.SIP.Record.Base where

IsHomT : ∀ {ℓ ℓ₁} (l : Level) → (Type ℓ → Type ℓ₁) → Type _
IsHomT l S = (A B : Σ S) → (A .fst ≃ B .fst) → Type l

module _ {ℓ ℓ₁ ℓ₁'} where
  data RecordFields (R : Type ℓ → Type ℓ₁) (ι : IsHomT ℓ₁' R) : Typeω

  level-of-fields→prod
    : {R : Type ℓ → Type ℓ₁} {ι : IsHomT ℓ₁' R}
    → RecordFields R ι
    → Level
  
  fields→prod
    : {R : Type ℓ → Type ℓ₁} {ι : IsHomT ℓ₁' R}
      (fields : RecordFields R ι)
    → Type ℓ → Type (level-of-fields→prod fields)

  project-fields
    : {R : Type ℓ → Type ℓ₁} {ι : IsHomT ℓ₁' R}
      (fs : RecordFields R ι)
    → {X : Type ℓ} → R X → fields→prod fs X

  isPropProperty
    : ∀ {ℓ₂} (R : Type ℓ → Type ℓ₁) (ι : IsHomT ℓ₁' R)
        (fs : RecordFields R ι)
        (P : (X : Type ℓ) → fields→prod fs X → Type ℓ₂)
    → Type (lsuc ℓ ⊔ ℓ₁ ⊔ ℓ₂)
  isPropProperty R ι fs P =
    {X : Type ℓ} (r  : R X) → isProp (P X (project-fields fs r))


  data RecordFields R ι where
    record: : RecordFields R ι

    _field[_by_]
      : (previous-fields : RecordFields R ι)
      → ∀ {ℓ₂ ℓ₂'} {S : Type ℓ → Type ℓ₂} {ι' : IsHomT ℓ₂' S}
      → (project : {X : Type ℓ} → R X → S X)
      → (project-preservation : {A B : Σ R} {e : A .fst ≃ B .fst}
                              → ι A B e
                              → ι' (Σ-map₂ project A) (Σ-map₂ project B) e)
      → RecordFields R ι

    _axiom[_by_]
      : (previous-fields : RecordFields R ι)
      → ∀ {ℓ₂} {P : (X : Type ℓ) → fields→prod previous-fields X → Type ℓ₂}
      → (predicate : {X : Type ℓ} (r : R X) → P X (project-fields previous-fields r))
      → isPropProperty R ι previous-fields P
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

isUnivalent' : ∀ {ℓ ℓ₁ ℓ₂} (S : Type ℓ → Type ℓ₁) → IsHomT ℓ₂ S → Type _
isUnivalent' S ι =
  ∀ (X Y : _)
  → (f : X .fst ≃ Y .fst)
  → ι X Y f ≃ PathP (λ i → S (ua f i)) (X .snd) (Y .snd)

tm→isHomT : ∀ {ℓ} (tm : StrTm ℓ) → IsHomT ℓ (interp tm)
tm→isHomT tm = tm→Structure tm .is-hom

tm→⌜isUnivalent⌝ : ∀ {ℓ} (tm : StrTm ℓ) → Type _
tm→⌜isUnivalent⌝ tm = isUnivalent' (interp tm) (tm→isHomT tm)

tm→isUnivalent' : ∀ {ℓ} (tm : StrTm ℓ) → isUnivalent' (interp tm) (tm→isHomT tm)
tm→isUnivalent' tm X Y f = tm→Structure-univalent tm f

repackage : ∀ {ℓ ℓ₁ ℓ₂} (S : Type ℓ → Type ℓ₁)
          → (ι : IsHomT ℓ₂ S)
          → isUnivalent' S ι
          → isUnivalent {S = S} (HomT→Str ι)
repackage S ι ua = ua _ _

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