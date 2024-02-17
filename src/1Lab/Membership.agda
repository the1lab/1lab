open import 1Lab.Underlying
open import 1Lab.Type hiding (Σ-syntax)

module 1Lab.Membership where

-- Syntax class for the _∈_ notation. An instance
--
--   Membership A ℙA _
--
-- denotes, essentially, that ℙA has a preferred projection into
--
--   A → Type _
--
-- Note that this projection does not have to be an embedding, or even
-- injective; and x ∈ S does not necessarily need to be valued in
-- propositions, either. In practice, both of these conditions are
-- satisfied.

record Membership {ℓ ℓe} (A : Type ℓe) (ℙA : Type ℓ) ℓm : Type (ℓ ⊔ lsuc (ℓe ⊔ ℓm)) where
  field _∈_ : A → ℙA → Type ℓm
  infix 30 _∈_

open Membership ⦃ ... ⦄ using (_∈_) public

-- The prototypical instance is given by functions into a universe:

instance
  Membership-pow
    : ∀ {ℓ ℓ'} {A : Type ℓ} {P : Type ℓ'} ⦃ u : Underlying P ⦄
    → Membership A (A → P) _
  Membership-pow = record { _∈_ = λ x S → ⌞ S x ⌟ }

-- If a type has membership, then it has a non-membership as well. Note
-- that this is a negative definition, while in some cases it might be
-- possible to implement ∉ as *positive* information.

_∉_ : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {ℙA : Type ℓ'} ⦃ m : Membership A ℙA ℓ'' ⦄
    → A → ℙA → Type ℓ''
x ∉ y = ¬ (x ∈ y)

-- Inclusion relative to the _∈_ projection.

_⊆_ : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {ℙA : Type ℓ'} ⦃ m : Membership A ℙA ℓ'' ⦄
    → ℙA → ℙA → Type (ℓ ⊔ ℓ'')
_⊆_ {A = A} S T = (a : A) → a ∈ S → a ∈ T

-- Total space of a predicate.

∫ₚ
  : ∀ {ℓ ℓ' ℓ''} {X : Type ℓ} {ℙX : Type ℓ'} ⦃ m : Membership X ℙX ℓ'' ⦄
  → ℙX → Type _
∫ₚ {X = X} P = Σ[ x ∈ X ] (x ∈ P)

infix 30 _∉_ _⊆_
