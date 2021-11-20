open import 1Lab.Type
open import 1Lab.Path
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Data.Dec
open import 1Lab.Data.Bool
open import 1Lab.Univalence

module wip.untruncate where

variable
  ℓ : Level
  A : Type ℓ

data ∥_∥ (A : Type ℓ) : Type ℓ where
  inc    : A → ∥ A ∥
  squash : (x y : ∥ A ∥) → x ≡ y

elim : {ℓ' : _} (P : ∥ A ∥ → Type ℓ')
     → (f : (x : A) → P (inc x))
     → ((x : ∥ A ∥) → isProp (P x))
     → (x : ∥ A ∥) → P x
elim P f prop (inc x) = f x
elim P f prop (squash x x₁ i) =
  isProp→PathP
    (λ i → prop (squash x x₁ i)) 
    (elim P f prop x)
    (elim P f prop x₁) i

Type∙ : (ℓ : _) → Type (lsuc ℓ)
Type∙ ℓ = Σ[ X ∈ Type ℓ ] X

Homogeneous : {ℓ : _} → Type∙ ℓ → _
Homogeneous (X , x) = (y : X) → Path (Type∙ _) (X , x) (X , y)

Discrete→Homogeneous : {ℓ : _} (X : Type∙ ℓ) → Discrete (X .fst) → Homogeneous X
Discrete→Homogeneous (X , x) disc y = path where
  swap→ : X → X
  swap→ z =
    case (λ _ → X)
         (λ _ → y)
         (λ _ → case (λ _ → X) (λ _ → x) (λ _ → z) (disc z y))
         (disc z x)

  swap-invol : (x : X) → swap→ (swap→ x) ≡ x
  swap-invol z with disc z x
  swap-invol z | yes z≡x with disc y x
  swap-invol z | yes z≡x | yes y≡x = y≡x ∙ sym z≡x
  swap-invol z | yes z≡x | no ¬y≡x with disc y y
  swap-invol z | yes z≡x | no ¬y≡x | yes y≡y = sym z≡x
  swap-invol z | yes z≡x | no ¬y≡x | no ¬y≡y = absurd (¬y≡y refl)
  swap-invol z | no ¬z≡x with disc z y
  swap-invol z | no ¬z≡x | yes z≡y with disc x x
  swap-invol z | no ¬z≡x | yes z≡y | yes x≡x = sym z≡y
  swap-invol z | no ¬z≡x | yes z≡y | no ¬x≡x = absurd (¬x≡x refl)
  swap-invol z | no ¬z≡x | no ¬z≡y with disc z x
  swap-invol z | no ¬z≡x | no ¬z≡y | yes z≡x = absurd (¬z≡x z≡x)
  swap-invol z | no ¬z≡x | no ¬z≡y | no ¬z≡x' with disc z y
  swap-invol z | no ¬z≡x | no ¬z≡y | no ¬z≡x' | yes z≡y = absurd (¬z≡y z≡y)
  swap-invol z | no ¬z≡x | no ¬z≡y | no ¬z≡x' | no ¬z≡y' = refl

  swap-swaps : swap→ x ≡ y
  swap-swaps with disc x x
  swap-swaps | yes x = refl
  swap-swaps | no ¬x≡x = absurd (¬x≡x refl)

  auto : X ≡ X
  auto = Iso→path (swap→ , iso swap→ swap-invol swap-invol)

  path : Path (Type∙ _) (X , x) (X , y)
  path = Σ-Path auto (transport-refl _ ∙ swap-swaps)

module untruncate {ℓ : _} {A : Type∙ ℓ} (hom : Homogeneous A) where
  f : A .fst → Σ[ B ∈ Type∙ _ ] (A ≡ B)
  f x = (A .fst , x) , hom _

  f' : ∥ A .fst ∥ → _
  f' = elim (λ _ → Σ[ B ∈ Type∙ _ ] (A ≡ B)) f (λ _ → isContr→isProp p)
    where
      p : _
      p = contr (_ , refl) λ x i → x .snd i , λ j → x .snd (i ∧ j)

  untruncate : (x : ∥ A .fst ∥) → f' x .fst .fst
  untruncate x = f' x .fst .snd

  module _ {x : A .fst} where
    test : untruncate (inc x) ≡ x
    test = refl

module _ where
  open untruncate (Discrete→Homogeneous (Bool , true) Discrete-Bool)

  _ : untruncate (inc true) ≡ true
  _ = refl

  _ : untruncate (inc false) ≡ false
  _ = refl