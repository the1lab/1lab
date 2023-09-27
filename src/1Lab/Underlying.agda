open import 1Lab.HLevel.Universe
open import 1Lab.Resizing
open import 1Lab.Path
open import 1Lab.Type

module 1Lab.Underlying where

record Underlying {ℓ} (T : Type ℓ) : Typeω where
  field
    ℓ-underlying : Level
    ⌞_⌟          : T → Type ℓ-underlying

open Underlying ⦃ ... ⦄ using (⌞_⌟) public

open Underlying using (ℓ-underlying)

instance
  Underlying-Type : ∀ {ℓ} → Underlying (Type ℓ)
  Underlying-Type {ℓ} .ℓ-underlying = ℓ
  Underlying-Type .⌞_⌟ x = x

  Underlying-n-Type : ∀ {ℓ n} → Underlying (n-Type ℓ n)
  Underlying-n-Type {ℓ} .ℓ-underlying = ℓ
  Underlying-n-Type .⌞_⌟ x = ∣ x ∣

  Underlying-prop : Underlying Ω
  Underlying-prop .ℓ-underlying = lzero
  Underlying-prop .⌞_⌟ x = ∣ x ∣

  Underlying-Σ
    : ∀ {ℓ ℓ′} {A : Type ℓ} {B : A → Type ℓ′}
    → ⦃ ua : Underlying A ⦄
    → Underlying (Σ A B)
  Underlying-Σ ⦃ ua ⦄ .ℓ-underlying = ua .Underlying.ℓ-underlying
  Underlying-Σ .⌞_⌟ x               = ⌞ x .fst ⌟

  -- Workaround for Agda bug https://github.com/agda/agda/issues/6588 —
  -- the principal (instance) argument is reified as visible, so we can
  -- drop it using a display form.
  {-# DISPLAY Underlying.⌞_⌟ f x = ⌞ x ⌟ #-}

record
  Funlike {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'}
    ⦃ au : Underlying A ⦄ ⦃ bu : Underlying B ⦄
    (F : A → B → Type ℓ'') : Typeω where
  infixl 999 _#_

  field
    _#_ : ∀ {A B} → F A B → ⌞ A ⌟ → ⌞ B ⌟
    ext : ∀ {A B} {f g : F A B} → (∀ x → f # x ≡ g # x) → f ≡ g

open Funlike ⦃ ... ⦄ public

{-# DISPLAY Funlike._#_ p f x = f # x #-}

_#ₚ_
  : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {F : A → B → Type ℓ''}
  → ⦃ _ : Underlying A ⦄ ⦃ _ : Underlying B ⦄ ⦃ _ : Funlike F ⦄
  → {a : A} {b : B} {f g : F a b} → f ≡ g → ∀ (x : ⌞ a ⌟) → f # x ≡ g # x
f #ₚ x = ap₂ _#_ f refl

instance
  Funlike-Fun : ∀ {ℓ ℓ'} → Funlike {lsuc ℓ} {lsuc ℓ'} {ℓ ⊔ ℓ'} {Type ℓ} {Type ℓ'} λ x y → x → y
  Funlike-Fun .Funlike._#_ = _$_
  Funlike-Fun .Funlike.ext = funext
