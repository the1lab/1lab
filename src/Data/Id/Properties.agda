open import 1Lab.Path.Groupoid
open import 1Lab.Path
open import 1Lab.Type

open import Data.Id.Base

module Data.Id.Properties where

private variable
  ℓ ℓ' ℓ'' : Level
  A B C : Type ℓ
  P Q R : A → Type ℓ
  w x y z : A

symᵢ-symᵢ : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ᵢ y) → symᵢ (symᵢ p) ≡ p
symᵢ-symᵢ reflᵢ = refl

symᵢ-from : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) → symᵢ (Id≃path.from p) ≡ Id≃path.from (sym p)
symᵢ-from = J (λ y p → symᵢ (Id≃path.from p) ≡ Id≃path.from (sym p)) (ap symᵢ (transport-refl reflᵢ) ∙ sym (transport-refl reflᵢ))

apᵢ-from : (f : A → B) {x y : A} (p : x ≡ y) → apᵢ f (Id≃path.from p) ≡ Id≃path.from (ap f p)
apᵢ-from f = J (λ y p → apᵢ f (Id≃path.from p) ≡ Id≃path.from (ap f p)) (ap (apᵢ f) (transport-refl reflᵢ) ∙ sym (transport-refl reflᵢ))

apᵢ-symᵢ : (f : A → B) (p : x ≡ᵢ y) → apᵢ f (symᵢ p) ≡ᵢ symᵢ (apᵢ f p)
apᵢ-symᵢ f reflᵢ = reflᵢ

symPᵢ : {a b : A} {x : P a} {y : P b} (p : a ≡ᵢ b) → Id-over P p x y → Id-over P (symᵢ p) y x
symPᵢ reflᵢ reflᵢ = reflᵢ

symPᵢ⁻ : {a b : A} {x : P a} {y : P b} (p : a ≡ᵢ b) → Id-over P (symᵢ p) y x → Id-over P p x y
symPᵢ⁻ reflᵢ reflᵢ = reflᵢ

∙ᵢ-invl : (p : x ≡ᵢ y) → symᵢ p ∙ᵢ p ≡ reflᵢ
∙ᵢ-invl reflᵢ = refl

∙ᵢ-invr : (p : x ≡ᵢ y) → p ∙ᵢ symᵢ p ≡ reflᵢ
∙ᵢ-invr reflᵢ = refl

∙ᵢ-idr : (p : x ≡ᵢ y) → p ∙ᵢ reflᵢ ≡ p
∙ᵢ-idr reflᵢ = refl

∙ᵢ-assoc : (p : w ≡ᵢ x) (q : x ≡ᵢ y) (r : y ≡ᵢ z) → p ∙ᵢ (q ∙ᵢ r) ≡ (p ∙ᵢ q) ∙ᵢ r
∙ᵢ-assoc reflᵢ reflᵢ reflᵢ = refl

∙ᵢ-to : (p : x ≡ᵢ y) (q : y ≡ᵢ z) → Id≃path.to (p ∙ᵢ q) ≡ Id≃path.to p ∙ Id≃path.to q
∙ᵢ-to reflᵢ reflᵢ = sym (∙-idl _)

symᵢ-to : (p : x ≡ᵢ y) → Id≃path.to (symᵢ p) ≡ sym (Id≃path.to p)
symᵢ-to reflᵢ = refl
