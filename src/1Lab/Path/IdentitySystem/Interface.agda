open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Type

module 1Lab.Path.IdentitySystem.Interface where

open import 1Lab.Path.IdentitySystem
  hiding (to-path-refl)
open import 1Lab.Path using (_≡_)

module
  Ids {ℓ ℓ'} {A : Type ℓ} {R : A → A → Type ℓ'} {refl : ∀ a → R a a}
      (rr : is-identity-system R refl)
  where

  J : ∀ {ℓ a} (P : (b : A) → R a b → Type ℓ) → P a (refl a) → {b : A} (s : R a b) → P b s
  J = IdsJ rr

  J-refl
    : ∀ {ℓ a} (P : ∀ b → R a b → Type ℓ) → (x : P a (refl a))
    → J P x (refl a) ≡ x
  J-refl = IdsJ-refl rr

  module _ {a b} where open Equiv (identity-system-gives-path rr {a} {b}) public

  to-refl : ∀ {a} → to-path rr (refl a) ≡ λ _ → a
  to-refl = 1Lab.Path.IdentitySystem.to-path-refl rr

  from-refl : ∀ {a} → from (λ _ → a) ≡ refl a
  from-refl = 1Lab.Path.transport-refl (refl _)

  hlevel : ∀ n → (∀ x y → is-hlevel (R x y) n) → is-hlevel A (suc n)
  hlevel n = identity-system→hlevel n rr
