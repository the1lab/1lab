---
description: |
  Combinatory bases for PCAs.
---
<!--
```agda
open import 1Lab.Prelude
open import Data.Fin
open import Data.Vec.Base

open import Realizability.PAS
open import Realizability.PCA
```
-->
```agda
module Realizability.PCA.Combinators where
```

# Combinatory completeness of S and K

<!--
```agda
private variable
  ℓ ℓ' ℓ'' : Level
  A : Type ℓ
  k n : Nat
```
-->

```agda
record SK-on (A : Type ℓ) : Type ℓ where
  field
    _⋆_ : A → A → A
    _↓ : A → Ω
    has-pas : is-pas _⋆_ _↓

  infixl 6 _⋆_

  open PAS has-pas public

  field
    ⌜s⌝ : A
    ⌜k⌝ : A

    s-def₂ : ∀ {x y} → ∣ x ↓ ∣ → ∣ y ↓ ∣ → ∣ (⌜s⌝ ⋆ x ⋆ y) ↓ ∣
    s-eval : ∀ {x y z} → ⌜s⌝ ⋆ x ⋆ y ⋆ z ≡ (x ⋆ z) ⋆ (y ⋆ z)
    k-eval : ∀ {x y} → ∣ y ↓ ∣ → ⌜k⌝ ⋆ x ⋆ y ≡ x

  k-def₁ : ∀ {x} → ∣ x ↓ ∣ → ∣ (⌜k⌝ ⋆ x) ↓ ∣
  k-def₁ x↓ = ⋆-defl (subst (λ e → ∣ e ↓ ∣) (sym (k-eval x↓)) x↓)

  k-def : ∣ ⌜k⌝ ↓ ∣
  k-def = rec! (λ v v↓ → ⋆-defl (k-def₁ v↓)) nonempty

  s-def : ∣ ⌜s⌝ ↓ ∣
  s-def = ⋆-defl (⋆-defl (s-def₂ k-def k-def))

  ⌜i⌝ : A
  ⌜i⌝ = ⌜s⌝ ⋆ ⌜k⌝ ⋆ ⌜k⌝

  i-def : ∣ ⌜i⌝ ↓ ∣
  i-def = s-def₂ k-def k-def

  i-eval : ∀ (a : A) → ⌜i⌝ ⋆ a ≡ a
  i-eval a =
    def-ext (∣ a ↓ ∣) ⋆-defr id
      (λ a↓ →
        ⌜s⌝ ⋆ ⌜k⌝ ⋆ ⌜k⌝ ⋆ a ≡⟨ s-eval ⟩
        ⌜k⌝ ⋆ a ⋆ (⌜k⌝ ⋆ a) ≡⟨ k-eval (k-def₁ a↓) ⟩
        a ∎)

sk→pca : SK-on A → PCA-on A
sk→pca {A = A} sk = pca
  module ski→pca where
    open SK-on sk

    abs : Term (1 + n) → Term n
    abs (var fzero) = const (value ⌜i⌝ i-def)
    abs (var (fsuc x)) = op (const (value ⌜k⌝ k-def)) (var x)
    abs (const a) = op (const (value ⌜k⌝ k-def)) (const a)
    abs (op e₁ e₂) = op (op (const (value ⌜s⌝ s-def)) (abs e₁)) (abs e₂)

    abs-def : {n : Nat} → (e : Term (1 + n)) → (ρ : Vec Val n) → ∣ eval (abs e) ρ ↓ ∣
    abs-def (var fzero) ρ = i-def
    abs-def (var (fsuc x)) ρ = k-def₁ (lookup ρ x .def)
    abs-def (const a) ρ = k-def₁ (a .def)
    abs-def (op e₁ e₂) ρ = s-def₂ (abs-def e₁ ρ) (abs-def e₂ ρ)

    abs-eval
      : (e : Term (1 + n)) (a : A) (ρ : Vec Val n)
      → (a↓ : ∣ a ↓ ∣)
      → eval (abs e) ρ ⋆ a ≡ eval e (value a a↓ ∷ ρ)
    abs-eval (var fzero) a ρ a↓ = i-eval a
    abs-eval (var (fsuc x)) a ρ a↓ = k-eval a↓
    abs-eval (const b) a ρ a↓ = k-eval a↓
    abs-eval (op e₁ e₂) a ρ a↓ =
      ⌜s⌝ ⋆ eval (abs e₁) ρ ⋆ eval (abs e₂) ρ ⋆ a         ≡⟨ s-eval ⟩
      (eval (abs e₁) ρ ⋆ a) ⋆ (eval (abs e₂) ρ ⋆ a)       ≡⟨ ap₂ _⋆_ (abs-eval e₁ a ρ a↓) (abs-eval e₂ a ρ a↓) ⟩
      eval e₁ (value a a↓ ∷ ρ) ⋆ eval e₂ (value a a↓ ∷ ρ) ∎

    pca : PCA-on A
    pca .PCA-on._⋆_ = _⋆_
    pca .PCA-on._↓ = _↓
    pca .PCA-on.has-pas = has-pas
    pca .PCA-on.abs = abs
    pca .PCA-on.abs-def {e = e} = abs-def e _
    pca .PCA-on.abs-eval {e = e} = abs-eval e _ _
```

## Combinatory completeness of BCKW

```agda
record BCKW-on (A : Type ℓ) : Type ℓ where
  field
    _⋆_ : A → A → A
    _↓ : A → Ω
    has-pas : is-pas _⋆_ _↓

  infixl 6 _⋆_

  open PAS has-pas public

  field
    ⌜b⌝ : A
    ⌜c⌝ : A
    ⌜k⌝ : A
    ⌜w⌝ : A

    b-def₂ : ∀ {x y} → ∣ x ↓ ∣ → ∣ y ↓ ∣ → ∣ (⌜b⌝ ⋆ x ⋆ y) ↓ ∣
    c-def₂ : ∀ {x y} → ∣ x ↓ ∣ → ∣ y ↓ ∣ → ∣ (⌜c⌝ ⋆ x ⋆ y) ↓ ∣
    w-def₁ : ∀ {x} → ∣ x ↓ ∣ → ∣ (⌜w⌝ ⋆ x) ↓ ∣

    b-eval : ∀ {x y z} → ⌜b⌝ ⋆ x ⋆ y ⋆ z ≡ x ⋆ (y ⋆ z)
    c-eval : ∀ {x y z} → ⌜c⌝ ⋆ x ⋆ y ⋆ z ≡ x ⋆ z ⋆ y
    k-eval : ∀ {x y} → ∣ y ↓ ∣ → ⌜k⌝ ⋆ x ⋆ y ≡ x
    w-eval : ∀ {x y} → ⌜w⌝ ⋆ x ⋆ y ≡ x ⋆ y ⋆ y

  c-def₁ : ∀ {x} → ∣ x ↓ ∣ → ∣ (⌜c⌝ ⋆ x) ↓ ∣
  c-def₁ x↓ = ⋆-defl (c-def₂ x↓ x↓)

bckw→sk : BCKW-on A → SK-on A
bckw→sk {A = A} bckw = sk
  module bckw→sk where

  open BCKW-on bckw

  sk : SK-on A
  sk .SK-on._⋆_ = _⋆_
  sk .SK-on._↓ = _↓
  sk .SK-on.has-pas = has-pas
  sk .SK-on.⌜k⌝ = ⌜k⌝
  sk .SK-on.⌜s⌝ = ⌜b⌝ ⋆ (⌜b⌝ ⋆ ⌜w⌝) ⋆ (⌜b⌝ ⋆ ⌜b⌝ ⋆ ⌜c⌝)
  sk .SK-on.k-eval = k-eval
  sk .SK-on.s-def₂ {x = x} {y = y} x↓ y↓ =
    subst (λ e → ∣ e ↓ ∣)
      (sym $
        (⌜b⌝ ⋆ (⌜b⌝ ⋆ ⌜w⌝) ⋆ (⌜b⌝ ⋆ ⌜b⌝ ⋆ ⌜c⌝) ⋆ x ⋆ y) ≡⟨ ap (_⋆ y) b-eval ⟩
        (⌜b⌝ ⋆ ⌜w⌝ ⋆ (⌜b⌝ ⋆ ⌜b⌝ ⋆ ⌜c⌝ ⋆ x) ⋆ y)         ≡⟨ b-eval ⟩
        (⌜w⌝ ⋆ (⌜ ⌜b⌝ ⋆ ⌜b⌝ ⋆ ⌜c⌝ ⋆ x ⌝ ⋆ y))           ≡⟨ ap! b-eval ⟩
        (⌜w⌝ ⋆ (⌜b⌝ ⋆ (⌜c⌝ ⋆ x) ⋆ y))                   ∎)
      (w-def₁ (b-def₂ (c-def₁ x↓) y↓))
  sk .SK-on.s-eval {x = x} {y = y} {z = z} =
    (⌜ ⌜b⌝ ⋆ (⌜b⌝ ⋆ ⌜w⌝) ⋆ (⌜b⌝ ⋆ ⌜b⌝ ⋆ ⌜c⌝) ⋆ x ⌝ ⋆ y ⋆ z) ≡⟨ ap! b-eval ⟩
    (⌜ ⌜b⌝ ⋆ ⌜w⌝ ⋆ (⌜b⌝ ⋆ ⌜b⌝ ⋆ ⌜c⌝ ⋆ x) ⋆ y ⌝ ⋆ z)         ≡⟨ ap! b-eval ⟩
    (⌜w⌝ ⋆ (⌜b⌝ ⋆ ⌜b⌝ ⋆ ⌜c⌝ ⋆ x ⋆ y) ⋆ z)                   ≡⟨ w-eval ⟩
    (⌜ ⌜b⌝ ⋆ ⌜b⌝ ⋆ ⌜c⌝ ⋆ x ⌝ ⋆ y ⋆ z ⋆ z)                   ≡⟨ ap! b-eval ⟩
    (⌜ ⌜b⌝ ⋆ (⌜c⌝ ⋆ x) ⋆ y ⋆ z ⌝ ⋆ z)                       ≡⟨ ap! b-eval ⟩
    (⌜c⌝ ⋆ x ⋆ (y ⋆ z) ⋆ z)                                 ≡⟨ c-eval ⟩
    (x ⋆ z ⋆ (y ⋆ z)) ∎
```
