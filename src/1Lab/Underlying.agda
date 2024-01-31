open import 1Lab.HLevel.Retracts
open import 1Lab.HLevel.Universe
open import 1Lab.HIT.Truncation
open import 1Lab.Resizing
open import 1Lab.HLevel
open import 1Lab.Path
open import 1Lab.Type

module 1Lab.Underlying where

-- Notation class for types which have a chosen projection into a
-- universe, i.e. a preferred "underlying type".
record Underlying {ℓ} (T : Type ℓ) : Typeω where
  field
    ℓ-underlying : Level
    ⌞_⌟          : T → Type ℓ-underlying

open Underlying ⦃ ... ⦄ using (⌞_⌟) public
open Underlying using (ℓ-underlying)

-- Workaround for Agda bug https://github.com/agda/agda/issues/6588 —
-- the principal (instance) argument is reified as visible, so we can
-- drop it using a display form.
{-# DISPLAY Underlying.⌞_⌟ f x = ⌞ x ⌟ #-}

instance
-- For universes, we use the standard notion of "underlying type".

  Underlying-Type : ∀ {ℓ} → Underlying (Type ℓ)
  Underlying-Type {ℓ} .ℓ-underlying = ℓ
  Underlying-Type .⌞_⌟ x = x

  Underlying-n-Type : ∀ {ℓ n} → Underlying (n-Type ℓ n)
  Underlying-n-Type {ℓ} .ℓ-underlying = ℓ
  Underlying-n-Type .⌞_⌟ x = ∣ x ∣

  Underlying-prop : Underlying Ω
  Underlying-prop .ℓ-underlying = lzero
  Underlying-prop .⌞_⌟ x = ∣ x ∣

  -- Lifting instances: for Σ-types, we think of (Σ A B) as "A with
  -- B-structure", so the underlying type is that of A; For Lift, there
  -- is no choice.
  Underlying-Σ
    : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
    → ⦃ ua : Underlying A ⦄
    → Underlying (Σ A B)
  Underlying-Σ ⦃ ua ⦄ .ℓ-underlying = ua .ℓ-underlying
  Underlying-Σ .⌞_⌟ x               = ⌞ x .fst ⌟

  Underlying-Lift
    : ∀ {ℓ ℓ'} {A : Type ℓ} ⦃ ua : Underlying A ⦄
    → Underlying (Lift ℓ' A)
  Underlying-Lift ⦃ ua ⦄ .ℓ-underlying = ua .ℓ-underlying
  Underlying-Lift .⌞_⌟ x = ⌞ x .Lift.lower ⌟

-- The converse of to-is-true, generalised slightly. If P and Q are
-- identical inhabitants of some type of structured types, and Q's
-- underlying type is contractible, then P is inhabited. P's underlying
-- type is obviously also contractible, but adding this as an instance
-- would ruin type inference (I tried.)
from-is-true
  : ∀ {ℓ} {A : Type ℓ} ⦃ _ : Underlying A ⦄ {P Q : A} ⦃ _ : H-Level ⌞ Q ⌟ 0 ⦄
  → P ≡ Q
  → ⌞ P ⌟
from-is-true prf = subst ⌞_⌟ (sym prf) (hlevel 0 .centre)


-- Notation class for type families which are "function-like" (always
-- nondependent). Slight generalisation of the homs of concrete
-- categories.
record
  Funlike {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} (F : A → B → Type ℓ'') : Typeω where
  infixl 999 _#_

  field
    -- The domain and codomain of F must both support an underlying-type
    -- projection, which is determined by the F.
    overlap ⦃ au ⦄ : Underlying A
    overlap ⦃ bu ⦄ : Underlying B

    -- The underlying function (infix).
    _#_ : ∀ {A B} → F A B → ⌞ A ⌟ → ⌞ B ⌟

open Funlike ⦃ ... ⦄ using (_#_) public
{-# DISPLAY Funlike._#_ p f x = f # x #-}

-- Sections of the _#_ operator tend to be badly-behaved since they
-- introduce an argument x : ⌞ ?0 ⌟ whose Underlying instance meta
-- "mutually blocks" the Funlike instance meta. Use the prefix version
-- instead.
apply
  : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {F : A → B → Type ℓ''}
  → ⦃ _ : Funlike F ⦄
  → ∀ {a b} → F a b → ⌞ a ⌟ → ⌞ b ⌟
apply = _#_

-- Shortcut for ap (apply ...)
ap#
  : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {F : A → B → Type ℓ''}
  → ⦃ _ : Funlike F ⦄
  → ∀ {a : A} {b : B} (f : F a b) → ∀ {x y : ⌞ a ⌟} → x ≡ y → f # x ≡ f # y
ap# f = ap (apply f)

-- Generalised happly.
_#ₚ_
  : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {F : A → B → Type ℓ''}
  → ⦃ _ : Funlike F ⦄
  → {a : A} {b : B} {f g : F a b} → f ≡ g → ∀ (x : ⌞ a ⌟) → f # x ≡ g # x
f #ₚ x = ap₂ _#_ f refl


instance
  -- Agda really dislikes inferring the level parameters here.
  Funlike-Fun
    : ∀ {ℓ ℓ'}
    → Funlike {lsuc ℓ} {lsuc ℓ'} {ℓ ⊔ ℓ'} {Type ℓ} {Type ℓ'} λ x y → x → y
  Funlike-Fun = record
    { _#_ = _$_
    }

-- Generalised "sections" (e.g. of a presheaf) notation.
_ʻ_
  : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {F : A → B → Type ℓ''}
  → ⦃ _ : Funlike F ⦄ {a : A} {b : B} ⦃ _ : Underlying ⌞ b ⌟ ⦄
  → F a b → ⌞ a ⌟ → Type _
F ʻ x = ⌞ F # x ⌟

record Membership {ℓ ℓ'} (A : Type ℓ) (ℙA : Type ℓ') ℓ'' : Type (ℓ ⊔ ℓ' ⊔ lsuc ℓ'') where
  field
    _∈_ : A → ℙA → Type ℓ''

  infix 25 _∈_

open Membership ⦃ ... ⦄ public

_∉_ : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {ℙA : Type ℓ'} ⦃ m : Membership A ℙA ℓ'' ⦄
    → A → ℙA → Type ℓ''
x ∉ y = ¬ (x ∈ y)

_⊆_ : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {ℙA : Type ℓ'} ⦃ m : Membership A ℙA ℓ'' ⦄
    → ℙA → ℙA → Type (ℓ ⊔ ℓ'')
s ⊆ t = ∀ a → a ∈ s → a ∈ t

infix 25 _⊆_ _∉_

-- Having this as an instance is girlbossing too close to the sun:
-- instance search doesn't consider superclasses before discarding
-- candidates, so this instance overlaps with *literally* everything
Funlike→membership
  : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {F : A → B → Type ℓ''}
  → ⦃ _ : Funlike F ⦄ {a : A} {b : B} ⦃ _ : Underlying ⌞ b ⌟ ⦄
  → Membership ⌞ a ⌟ (F a b) _
Funlike→membership = record { _∈_ = λ x f → ⌞ f # x ⌟ }

instance
  Membership-pow
    : ∀ {ℓ ℓ'} {A : Type ℓ} {P : Type ℓ'} ⦃ u : Underlying P ⦄
    → Membership A (A → P) _
  Membership-pow = Funlike→membership

-- Generalised "total space" notation.
∫ₚ
  : ∀ {ℓ ℓ' ℓ''} {X : Type ℓ} {ℙX : Type ℓ'} ⦃ m : Membership X ℙX ℓ'' ⦄
  → ℙX → Type _
∫ₚ {X = X} P = Σ X (_∈ P)

image
  : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {F : A → B → Type ℓ''}
  → ⦃ _ : Funlike F ⦄ {a : A} {b : B}
  → (f : F a b) → Type _
image {a = a} {b} f = Σ[ b ∈ ⌞ b ⌟ ] ∃[ a ∈ ⌞ a ⌟ ] (f # a ≡ b)
