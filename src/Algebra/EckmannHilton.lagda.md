
```agda
open import 1Lab.Prelude
open import Algebra.UnitalMagma
open import Algebra.Monoid
open import Algebra.Semigroup

module Algebra.EckmannHilton where
```


# The Eckmann-Hilton Argument

```agda
module _ {ℓ : _} {A : Type ℓ} {_⋆_ : A → A → A} {_✦_ : A → A → A} {e : A} {e' : A}
  (unitalMgm : isUnitalMagma e _⋆_) (unitalMgm' : isUnitalMagma e' _✦_)
  (interchange : (a b c d : A) → (a ⋆ b) ✦ (c ⋆ d) ≡ (a ✦ c) ⋆ (b ✦ d)) where

  unitsEqual : e ≡ e'
  unitsEqual =
    e ≡⟨ sym (idˡ unitalMgm) ⟩
    (e ⋆ e) ≡⟨ ap₂ _⋆_ (sym (idˡ unitalMgm')) (sym (idʳ unitalMgm')) ⟩
    ((e' ✦  e) ⋆ (e ✦ e')) ≡⟨ sym (interchange e' e e e') ⟩
    ((e' ⋆ e) ✦ (e ⋆ e')) ≡⟨ ap₂ _✦_ (idʳ unitalMgm) (idˡ unitalMgm) ⟩
    (e' ✦ e') ≡⟨ idˡ unitalMgm' ⟩
    e' ∎

  ⋆-reverse-✦ : (x y : A) → x ⋆ y ≡ y ✦ x
  ⋆-reverse-✦ x y =
    x ⋆ y ≡⟨ ap₂ _⋆_ (sym (idˡ unitalMgm')) (sym (idʳ unitalMgm')) ⟩
    (e' ✦ x) ⋆ (y ✦ e') ≡⟨ sym (interchange e' y x e') ⟩
    (e' ⋆ y) ✦ (x ⋆ e') ≡⟨ ap₂ _✦_ (ap (_⋆ y) (sym unitsEqual)) (ap (x ⋆_) (sym unitsEqual)) ⟩
    (e ⋆ y) ✦ (x ⋆ e) ≡⟨ ap₂ _✦_ (idˡ unitalMgm) (idʳ unitalMgm) ⟩
    y ✦ x ∎

  operationsEqual : (x y : A) → x ⋆ y ≡ x ✦ y
  operationsEqual x y =
    x ⋆ y ≡⟨ ap₂ _⋆_ (sym (idʳ unitalMgm')) (sym (idˡ unitalMgm')) ⟩
    (x ✦ e') ⋆ (e' ✦ y) ≡⟨ sym (interchange x e' e' y) ⟩
    (x ⋆ e') ✦ (e' ⋆ y) ≡⟨ ap₂ _✦_ (sym (ap (_⋆_ x) unitsEqual)) (sym (ap (_⋆ y) unitsEqual)) ⟩
    (x ⋆ e) ✦ (e ⋆ y) ≡⟨ ap₂ _✦_ (idʳ unitalMgm) (idˡ unitalMgm) ⟩
    x ✦ y ∎

  ⋆-commutative : (x y : A) → x ⋆ y ≡ y ⋆ x
  ⋆-commutative x y = ⋆-reverse-✦ x y ∙ sym (operationsEqual y x)

  ⋆-associative : (x y z : A) → x ⋆ (y ⋆ z) ≡ (x ⋆ y) ⋆ z
  ⋆-associative x y z = sym (
    (x ⋆ y) ⋆ z ≡⟨ ap (λ a → (x ⋆ y) ⋆ a) (sym (idʳ unitalMgm)) ⟩
    (x ⋆ y) ⋆ (z ⋆ e) ≡⟨ ap (λ x → x ⋆ (z ⋆ e)) (⋆-commutative x y) ⟩
    (y ⋆ x) ⋆ (z ⋆ e) ≡⟨ operationsEqual (y ⋆ x) (z ⋆ e) ⟩
    (y ⋆ x) ✦ (z ⋆ e) ≡⟨ interchange y x z e ⟩
    (y ✦ z) ⋆ (x ✦ e) ≡⟨ ⋆-commutative (y ✦ z) (x ✦ e) ⟩
    (x ✦ e) ⋆ (y ✦ z) ≡⟨ ap₂ _⋆_ (sym (operationsEqual x e)) (sym (operationsEqual y z)) ⟩
    (x ⋆ e) ⋆ (y ⋆ z) ≡⟨ ap (_⋆ (y ⋆ z)) (idʳ unitalMgm) ⟩
    x ⋆ (y ⋆ z) ∎)

  ⋆-isMonoid : isMonoid e _⋆_
  ⋆-isMonoid .monoid-semigroup .hasIsMagma = unitalMgm .hasIsMagma
  ⋆-isMonoid .monoid-semigroup .associative = ⋆-associative _ _ _
  ⋆-isMonoid .idˡ = unitalMgm .idˡ
  ⋆-isMonoid .idʳ = unitalMgm .idʳ
```
