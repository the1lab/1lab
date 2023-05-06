open import Algebra.Group.Notation
open import Algebra.Ring.Module
open import Algebra.Group.Ab
open import Algebra.Group
open import Algebra.Ring

open import Cat.Prelude hiding (_+_ ; _*_)

module Algebra.Ring.Module.Notation where

record Module-notation {ℓ ℓm} (R : Ring ℓ) (T : Type ℓm) : Type (ℓ ⊔ ℓm) where
  private module R = Ring-on (R .snd)

  field
    instance additive-group : Abelian-group-on T

  private
    _+_ : T → T → T
    _+_ = Abelian-group-on._*_ additive-group

  field
    +-comm     : (a b : T) → a + b ≡ b + a

    _⋆_        : ⌞ R ⌟ → T → T
    ⋆-distribl : ∀ r x y → r ⋆ (x + y)   ≡ (r ⋆ x) + (r ⋆ y)
    ⋆-distribr : ∀ r s x → (r R.+ s) ⋆ x ≡ (r ⋆ x) + (s ⋆ x)
    ⋆-assoc    : ∀ r s x → r ⋆ (s ⋆ x)   ≡ (r R.* s) ⋆ x
    ⋆-id       : ∀ x     → R.1r ⋆ x      ≡ x

  infixr 25 _⋆_

module-notation : ∀ {ℓ ℓm} {R : Ring ℓ} (M : Module R ℓm) → Module-notation R ⌞ M ⌟
module-notation M .Module-notation.additive-group = Module-on→Abelian-group-on (M .snd)
module-notation M .Module-notation.+-comm a b = Module-on.+-comm (M .snd)
module-notation M .Module-notation._⋆_        = Module-on._⋆_ (M .snd)
module-notation M .Module-notation.⋆-distribl = Module-on.⋆-distribl (M .snd)
module-notation M .Module-notation.⋆-distribr = Module-on.⋆-distribr (M .snd)
module-notation M .Module-notation.⋆-assoc    = Module-on.⋆-assoc (M .snd)
module-notation M .Module-notation.⋆-id       = Module-on.⋆-id (M .snd)
