---
description: |
  Partial applicative systems
---
<!--
```agda
open import Order.Base

open import 1Lab.Prelude

open import Data.Vec.Base
open import Data.Fin
```
-->
```agda
module Realizability.PAS where
```

# Partial applicative systems

<!--
```agda
private variable
  ℓ ℓ' ℓ'' : Level
  A : Type ℓ
  k n : Nat
```
-->

```agda
record is-pas {A : Type ℓ} (_⋆_ : A → A → A) (_↓ : A → Ω) : Type ℓ where
  field
    ⋆-defl : ∀ {a b} → ∣ (a ⋆ b) ↓ ∣ → ∣ a ↓ ∣
    ⋆-defr : ∀ {a b} → ∣ (a ⋆ b) ↓ ∣ → ∣ b ↓ ∣
    kleene-ext : ∀ {a b} → ∣ a ↓ ∣ ≃ ∣ b ↓ ∣ → (∣ a ↓ ∣ → ∣ b ↓ ∣ → a ≡ b) → a ≡ b
    nonempty : ∃[ a ∈ A ] ∣ a ↓ ∣
    has-is-set : is-set A

  def-ext : ∀ {a b} → (P : Type ℓ') → (∣ a ↓ ∣ → P) → (∣ b ↓ ∣ → P) → (P → a ≡ b) → a ≡ b
  def-ext P l r h =
    kleene-ext (prop-ext!
         (λ a↓ → subst (λ b → ∣ b ↓ ∣) (h (l a↓)) a↓)
         (λ b↓ → subst (λ a → ∣ a ↓ ∣) (sym (h (r b↓))) b↓))
       (λ a↓ b↓ → h (l a↓))
```

## Refinement

```agda
module PAS {A : Type ℓ} {_⋆_ : A → A → A} {_↓ : A → Ω} (has-pas : is-pas _⋆_ _↓) where
  open is-pas has-pas public

  _⊑_ : A → A → Type ℓ
  x ⊑ y = ∣ x ↓ ∣ → ∣ y ↓ ∣ × (x ≡ y)

  ⊑-refl : ∀ {x : A} → x ⊑ x
  ⊑-refl x↓ = x↓ , refl

  ⊑-thin : ∀ {x y} → is-prop (x ⊑ y)
  ⊑-thin = Π-is-hlevel 1 (λ _ → ×-is-hlevel 1 (hlevel 1) (has-is-set _ _))

  ⊑-trans : ∀ {x y z} → x ⊑ y → y ⊑ z → x ⊑ z
  ⊑-trans p q x↓ = (q (p x↓ .fst) .fst) , p x↓ .snd ∙ q (p x↓ .fst) .snd

  ⊑-antisym : ∀ {x y} → x ⊑ y → y ⊑ x → x ≡ y
  ⊑-antisym {x = x} {y = y} x⊑y y⊑x =
    def-ext (∣ x ↓ ∣ × ∣ y ↓ ∣)
      (λ x↓ → x↓ , x⊑y x↓ .fst)
      (λ y↓ → y⊑x y↓ .fst , y↓)
      (λ (x↓ , y↓) → x⊑y x↓ .snd)

  Refinement : Poset ℓ ℓ
  Refinement .Poset.Ob = A
  Refinement .Poset._≤_ = _⊑_
  Refinement .Poset.≤-thin = ⊑-thin
  Refinement .Poset.≤-refl = ⊑-refl
  Refinement .Poset.≤-trans = ⊑-trans
  Refinement .Poset.≤-antisym = ⊑-antisym
```

## Defined elements

```agda
  record Val : Type ℓ where
    constructor value
    field
      elt : A
      def : ∣ elt ↓ ∣

  open Val public

  record Defined (a : A) : Typeω where
    constructor defined-instance
    field
      defined : ∣ a ↓ ∣

  open Defined ⦃...⦄ public

  val : (a : A) → ⦃ Defined a ⦄ → Val
  val a .elt = a
  val a .def = defined
```

<!--
```agda
  Val-is-set : is-set Val
  Val-is-set = Iso→is-hlevel 2 eqv (Σ-is-hlevel 2 has-is-set λ _ → hlevel 2)
    where unquoteDecl eqv = declare-record-iso eqv (quote Val)

  instance
    H-Level-Val : ∀ {n : Nat} → H-Level Val (2 + n)
    H-Level-Val = basic-instance 2 Val-is-set

    Extensional-Val
      : ∀ {ℓr : Level} ⦃ e : Extensional A ℓr ⦄
      → Extensional Val ℓr
    Extensional-Val ⦃ e ⦄ =
      injection→extensional has-is-set val-ext e
      where
         val-ext : ∀ {v₁ v₂ : Val} → v₁ .elt ≡ v₂ .elt → v₁ ≡ v₂
         val-ext {v₁ = v₁} {v₂ = v₂} p i .elt = p i
         val-ext {v₁ = v₁} {v₂ = v₂} p i .def =
           is-prop→pathp (λ i → ((p i) ↓) .is-tr) (v₁ .def) (v₂ .def) i
```
-->

## Diverging elements

```agda
  _↑ : A → Ω
  a ↑ = ¬Ω (a ↓)

  ⋆-divl : ∀ {a} → ∣ a ↑ ∣ → (b : A) → ∣ (a ⋆ b) ↑ ∣
  ⋆-divl a↑ b ab↓ = a↑ (⋆-defl ab↓)

  ⋆-divr : ∀ {b} → (a : A) → ∣ b ↑ ∣ → ∣ (a ⋆ b) ↑ ∣
  ⋆-divr a b↑ ab↓ = b↑ (⋆-defr ab↓)

  diverge-is-prop : ∀ {a b} → ∣ a ↑ ∣ → ∣ b ↑ ∣ → a ≡ b
  diverge-is-prop {a = a} {b = b} a↑ b↑ =
    kleene-ext
      (prop-ext! (λ a↓ → absurd (a↑ a↓)) (λ b↓ → absurd (b↑ b↓)))
      (λ a↓ b↓ → absurd (a↑ a↓))
```

## Terms

```agda
  data Term : Nat → Type ℓ where
    var : ∀ {n} → Fin n → Term n
    const : ∀ {n} → Val → Term n
    op : ∀ {n} → Term n → Term n → Term n

  eval : Term n → Vec Val n → A
  eval (var x) ρ = lookup ρ x .elt
  eval (const v) ρ = v .elt
  eval (op e₁ e₂) ρ = eval e₁ ρ ⋆ eval e₂ ρ

  term : Term 0 → A
  term e = eval e []
```

```agda
  shift : Term n → Term (1 + n)
  shift (var x) = var (fsuc x)
  shift (const x) = var fzero
  shift (op e₁ e₂) = op (shift e₁) (shift e₂)
```

<!--
```agda
  record Splice (A : Type ℓ) {E : Type ℓ'} (e : E) (n : Nat) : Typeω where
    field
      splice : Term n

  instance
    Splice-Const : {a : A} → ⦃ a↓ : Defined a ⦄ → Splice A a n
    Splice-Const {a = a} = record { splice = const (value a defined) }

    Splice-Val : {n : Nat} {v : Val} → Splice A v n
    Splice-Val {v = v} = record { splice = const v }

    Splice-Term : {n : Nat} {e : Term n} → Splice A e n
    Splice-Term {e = e} = record { splice = e }

    Splice-Shift : {n k : Nat} {e : Term n} → ⦃ Splice A e k ⦄ → Splice A e (1 + k)
    Splice-Shift ⦃ s ⦄ = record { splice = shift (Splice.splice s) }

  “_” : {E : Type ℓ'} → (e : E) → ⦃ s : Splice A e n ⦄ → Term n
  “_” e ⦃ s ⦄ = Splice.splice s

  _“⋆”_ : {E₁ : Type ℓ'} {E₂ : Type ℓ''} → (e₁ : E₁) → ⦃ Splice A e₁ n ⦄ → (e₂ : E₂) → ⦃ Splice A e₂ n ⦄ → Term n
  e₁ “⋆” e₂ = op (“ e₁ ”) (“ e₂ ”)

  infixl 6 _“⋆”_
```
-->

```agda
is-pas-is-prop
  : {_⋆_ : A → A → A} {_↓ : A → Ω}
  → is-prop (is-pas _⋆_ _↓)
is-pas-is-prop {A = A} {_⋆_ = _⋆_} {_↓ = _↓} pas pas' =
  Iso→is-hlevel 1 eqv (hlevel 1) pas pas'
  where
    unquoteDecl eqv = declare-record-iso eqv (quote is-pas)
    instance
      HLevel-pas : ∀ {n : Nat} → H-Level A (2 + n)
      HLevel-pas = basic-instance 2 (is-pas.has-is-set pas)
```
