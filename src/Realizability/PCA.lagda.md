---
description: |
  Partial Combinatory Algebras
---
<!--
```agda
open import 1Lab.Prelude

open import Data.Fin
open import Data.Vec.Base

open import Realizability.PAS
```
-->
```agda
module Realizability.PCA where
```

# Partial combinatory algebras

<!--
```agda
private variable
  ℓ ℓ' ℓ'' : Level
  A : Type ℓ
  k n : Nat
```
-->

```agda
record PCA-on (A : Type ℓ) : Type ℓ where
  field
    _⋆_ : A → A → A
    _↓ : A → Ω
    has-pas : is-pas _⋆_ _↓


  infixl 6 _⋆_

  open PAS has-pas public

  field
    abs : ∀ {n} → Term (1 + n) → Term n
    abs-def : {n : Nat} → {e : Term (1 + n)} → {ρ : Vec Val n} → ∣ eval (abs e) ρ ↓ ∣
    abs-eval
      : {n : Nat} {e : Term (1 + n)} {a : A} {ρ : Vec Val n}
      → (a↓ : ∣ a ↓ ∣)
      → (eval (abs e) ρ ⋆ a) ≡ eval e (value a a↓ ∷ ρ)

  lam : (Term (1 + n) → Term (1 + n)) → Term n
  lam k = abs (k (var 0))
```

## Programming with PCAs

```agda
module PCA (pca : PCA-on A) where
  open PCA-on pca public

  absₙ : (k : Nat) → Term (k + n) → Term n
  absₙ zero e = e
  absₙ (suc k) e = (absₙ k (abs e))

  _⋆ₙ_ : ∀ {n} → A → Vec Val n → A
  a ⋆ₙ [] = a
  a ⋆ₙ (b ∷ bs) = (a ⋆ₙ bs) ⋆ b .elt

  abs-evalₙ
    : {k n : Nat}
    → {e : Term (k + n)} {ρ : Vec Val n}
    → (as : Vec Val k)
    → (eval (absₙ k e) ρ ⋆ₙ as) ≡ eval e (as ++ᵥ ρ)
  abs-evalₙ [] = refl
  abs-evalₙ {k = suc k} {e =  e} {ρ = ρ} (a ∷ as) =
    ⌜ eval (absₙ k (abs e)) ρ ⋆ₙ as ⌝ ⋆ (a .elt) ≡⟨ ap! (abs-evalₙ as) ⟩
    eval (abs e) (as ++ᵥ ρ) ⋆ (a .elt)           ≡⟨ abs-eval (a .def) ⟩
    eval e ((a ∷ as) ++ᵥ ρ) ∎
```

<!--
```agda
  -- Weird behaviour; need to mark this as INCOHERENT here instead of alongside the definition?
  {-# INCOHERENT Splice-Shift #-}
```
-->

```agda
  opaque
    “id” : A
    “id” = term (lam λ x → “ x ”)


    id-eval : ∀ (a : A) → “id” ⋆ a ≡ a
    id-eval a = def-ext ∣ a ↓ ∣ ⋆-defr id abs-eval
```

<!--
```agda
    id-def : ∣ “id” ↓ ∣
    id-def = abs-def

  instance
    Defined-id : Defined “id”
    Defined-id .defined = id-def
```
-->

```agda
  opaque
    “comp” : A
    “comp” = term (lam λ f → lam λ g → lam λ x → f “⋆” (g “⋆” x))


    comp-eval : ∀ (f g a : A) → “comp” ⋆ f ⋆ g ⋆ a ≡ f ⋆ (g ⋆ a)
    comp-eval f g a =
      def-ext (∣ f ↓ ∣ × ∣ g ↓ ∣ × ∣ a ↓ ∣)
        (λ c↓ → ⋆-defr (⋆-defl (⋆-defl c↓)) , ⋆-defr (⋆-defl c↓) , ⋆-defr c↓)
        (λ c↓ → ⋆-defl c↓ , ⋆-defl (⋆-defr c↓) , ⋆-defr (⋆-defr c↓))
        (λ (f↓ , g↓ , a↓) → abs-evalₙ (value a a↓ ∷ value g g↓ ∷ value f f↓ ∷ []))
```

<!--
```agda
    comp-def : ∣ “comp” ↓ ∣
    comp-def = abs-def

    comp-def₂ : ∀ {f g : A} → ∣ f ↓ ∣ → ∣ g ↓ ∣ → ∣ (“comp” ⋆ f ⋆ g) ↓ ∣
    comp-def₂ f↓ g↓ = subst (λ e → ∣ e ↓ ∣) (sym (abs-evalₙ (value _ g↓ ∷ value _ f↓ ∷ []))) abs-def

  instance
    Defined-comp : Defined “comp”
    Defined-comp .defined = comp-def

    Defined-comp₂ : ∀ {f g : A} → ⦃ f↓ : Defined f ⦄ → ⦃ g↓ : Defined g ⦄ → Defined (“comp” ⋆ f ⋆ g)
    Defined-comp₂ .defined = comp-def₂ defined defined
```
-->


```agda
  opaque
    “const” : A
    “const” = term (lam λ x → lam λ y → “ x ”)

    “ignore” : A
    “ignore” = term (lam λ x → lam λ y → “ y ”)

    const-eval : ∀ (a b : A) → ∣ b ↓ ∣ → “const” ⋆ a ⋆ b ≡ a
    const-eval a b b↓ =
      def-ext (∣ a ↓ ∣ × ∣ b ↓ ∣)
        (λ c↓ → (⋆-defr (⋆-defl c↓)) , ⋆-defr c↓)
        (λ a↓ → a↓ , b↓)
        (λ (a↓ , b↓) → abs-evalₙ (value b b↓ ∷ value a a↓ ∷ []))

    ignore-eval : ∀ (a b : A) → ∣ a ↓ ∣ → “ignore” ⋆ a ⋆ b ≡ b
    ignore-eval a b a↓ =
      def-ext (∣ a ↓ ∣ × ∣ b ↓ ∣)
        (λ c↓ → (⋆-defr (⋆-defl c↓)) , ⋆-defr c↓)
        (λ b↓ → a↓ , b↓)
        (λ (a↓ , b↓) → abs-evalₙ (value b b↓ ∷ value a a↓ ∷ []))

```

<!--
```agda
    const-def : ∣ “const” ↓ ∣
    const-def = abs-def

    ignore-def : ∣ “ignore” ↓ ∣
    ignore-def = abs-def

    const-def₁ : {x : A} → ∣ x ↓ ∣ → ∣ (“const” ⋆ x) ↓ ∣
    const-def₁ x↓ = subst (λ e → ∣ e ↓ ∣) (sym (abs-eval x↓)) abs-def

  instance
    Defined-const : Defined “const”
    Defined-const .defined = const-def

    Defined-ignore : Defined “ignore”
    Defined-ignore .defined = ignore-def
```
-->

### Pairing

```agda
  opaque
    “pair” : A
    “pair” = term (lam λ x → lam λ y → lam λ p → p “⋆” x “⋆” y)

    “fst” : A
    “fst” = term (lam λ p → p “⋆” “const”)

    “snd” : A
    “snd” = term (lam λ p → p “⋆” “ignore”)
```

<!--
```agda
    fst-def : ∣ “fst” ↓ ∣
    fst-def = abs-def

    snd-def : ∣ “snd” ↓ ∣
    snd-def = abs-def

    pair-def : ∣ “pair” ↓ ∣
    pair-def = abs-def

    pair-def₂ : ∀ {a b : A} → ∣ a ↓ ∣ → ∣ b ↓ ∣ → ∣ (“pair” ⋆ a ⋆ b) ↓ ∣
    pair-def₂ {a = a} {b = b} a↓ b↓ =
      subst (λ e → ∣ e ↓ ∣) (sym (ap₂ _⋆_ (abs-eval a↓) refl ∙ (abs-eval b↓))) abs-def

```
-->

```agda
    fst-pair-eval : ∀ (a b : A) → ∣ b ↓ ∣ → “fst” ⋆ (“pair” ⋆ a ⋆ b) ≡ a
    fst-pair-eval a b b↓ =
      def-ext (∣ a ↓ ∣ × ∣ b ↓ ∣)
        (λ p↓ → ⋆-defr (⋆-defl (⋆-defr p↓)) , b↓)
        (λ a↓ → a↓ , b↓)
        (λ (a↓ , b↓) →
          “fst” ⋆ (“pair” ⋆ a ⋆ b) ≡⟨ abs-eval (pair-def₂ a↓ b↓) ⟩
          “pair” ⋆ a ⋆ b ⋆ “const” ≡⟨ abs-evalₙ (value “const” const-def ∷ value b b↓ ∷ value a a↓ ∷ []) ⟩
          “const” ⋆ a ⋆ b          ≡⟨ const-eval a b b↓ ⟩
          a ∎)

    snd-pair-eval : ∀ (a b : A) → ∣ a ↓ ∣ → “snd” ⋆ (“pair” ⋆ a ⋆ b) ≡ b
    snd-pair-eval a b a↓ =
      def-ext (∣ a ↓ ∣ × ∣ b ↓ ∣)
        (λ p↓ → a↓ , ⋆-defr (⋆-defr p↓))
        (λ b↓ → a↓ , b↓)
        (λ (a↓ , b↓) →
          “snd” ⋆ (“pair” ⋆ a ⋆ b)  ≡⟨ abs-eval (pair-def₂ a↓ b↓) ⟩
          “pair” ⋆ a ⋆ b ⋆ “ignore” ≡⟨ abs-evalₙ (value “ignore” ignore-def ∷ value b b↓ ∷ value a a↓ ∷ []) ⟩
          “ignore” ⋆ a ⋆ b          ≡⟨ ignore-eval a b a↓ ⟩
          b ∎)
```

<!--
```agda
  instance
    Defined-fst : Defined “fst”
    Defined-fst .defined = fst-def

    Defined-snd : Defined “snd”
    Defined-snd .defined = snd-def

    Defined-pair : Defined “pair”
    Defined-pair .defined = pair-def

  pair-val : Val → Val → Val
  pair-val v₁ v₂ = value (“pair” ⋆ v₁ .elt ⋆ v₂ .elt) (pair-def₂ (v₁ .def) (v₂ .def))
```
-->

```agda
  opaque
    “curry” : A
    “curry” = term (lam λ f → lam λ x → lam λ y → f “⋆” (“pair” “⋆” x “⋆” y))

    “uncurry” : A
    “uncurry” = term (lam λ f → lam λ xy → f “⋆” (“fst” “⋆” xy) “⋆” (“snd” “⋆” xy))

    curry-eval : ∀ (f a b : A) → “curry” ⋆ f ⋆ a ⋆ b ≡ f ⋆ (“pair” ⋆ a ⋆ b)
    curry-eval f a b =
      def-ext (∣ f ↓ ∣ × ∣ a ↓ ∣ × ∣ b ↓ ∣)
        (λ p↓ → ⋆-defr (⋆-defl (⋆-defl p↓)) , ⋆-defr (⋆-defl p↓) , ⋆-defr p↓)
        (λ p↓ → ⋆-defl p↓ , ⋆-defr (⋆-defl (⋆-defr p↓)) , ⋆-defr (⋆-defr p↓))
        (λ (f↓ , a↓ , b↓) → abs-evalₙ (value b b↓ ∷ value a a↓ ∷ value f f↓ ∷ []))

    uncurry-eval : ∀ (f a b : A) → “uncurry” ⋆ f ⋆ a ≡ f ⋆ (“fst” ⋆ a) ⋆ (“snd” ⋆ a)
    uncurry-eval f a b =
      def-ext (∣ f ↓ ∣ × ∣ a ↓ ∣)
        (λ p↓ → ⋆-defr (⋆-defl p↓) , ⋆-defr p↓)
        (λ p↓ → ⋆-defl (⋆-defl p↓) , ⋆-defr (⋆-defr p↓))
        (λ (f↓ , a↓) → abs-evalₙ (value a a↓ ∷ value f f↓ ∷ []))
```


### Booleans

```agda
  “true” : A
  “true” = “const”

  “false” : A
  “false” = “ignore”
```

### Coproducts

```agda
  opaque
    “inl” : A
    “inl” = term (lam λ x → “pair” “⋆” “true” “⋆” x)

    “inr” : A
    “inr” = term (lam λ x → “pair” “⋆” “false” “⋆” x)

    “elim” : A
    “elim” = term (lam λ l → lam λ r → lam λ x → (“fst” “⋆” x) “⋆” l “⋆” r “⋆” (“snd” “⋆” x))

    inl-eval : (a : A) → “inl” ⋆ a ≡ “pair” ⋆ “true” ⋆ a
    inl-eval a = def-ext ∣ a ↓ ∣ ⋆-defr ⋆-defr abs-eval

    inr-eval : (a : A) → “inr” ⋆ a ≡ “pair” ⋆ “false” ⋆ a
    inr-eval a = def-ext ∣ a ↓ ∣ ⋆-defr ⋆-defr abs-eval

    inl-def : ∣ “inl” ↓ ∣
    inl-def = abs-def

    inr-def : ∣ “inr” ↓ ∣
    inr-def = abs-def

    inl-def₁ : {a : A} → ∣ a ↓ ∣ → ∣ (“inl” ⋆ a) ↓ ∣
    inl-def₁ a↓ = subst (λ e → ∣ e ↓ ∣) (sym (inl-eval _)) (pair-def₂ const-def a↓)

    inr-def₁ : {a : A} → ∣ a ↓ ∣ → ∣ (“inr” ⋆ a) ↓ ∣
    inr-def₁ a↓ = subst (λ e → ∣ e ↓ ∣) (sym (inr-eval _)) (pair-def₂ ignore-def a↓)

    elim-def₂ : {l r : A} → ∣ l ↓ ∣ → ∣ r ↓ ∣ → ∣ (“elim” ⋆ l ⋆ r) ↓ ∣
    elim-def₂ l↓ r↓ =
      subst (λ e → ∣ e ↓ ∣) (sym (abs-evalₙ (value _ r↓ ∷ value _ l↓ ∷ []))) abs-def

    elim-inl-eval : ∀ (l r a : A) → ∣ r ↓ ∣ → “elim” ⋆ l ⋆ r ⋆ (“inl” ⋆ a) ≡ l ⋆ a
    elim-inl-eval l r a r↓ =
      def-ext (∣ l ↓ ∣ × ∣ r ↓ ∣ × ∣ a ↓ ∣)
        (λ p↓ → ⋆-defr (⋆-defl (⋆-defl p↓)) , ⋆-defr (⋆-defl p↓) , ⋆-defr (⋆-defr p↓))
        (λ la↓ → ⋆-defl la↓ , r↓ , (⋆-defr la↓))
        (λ (l↓ , r↓ , a↓) →
          “elim” ⋆ l ⋆ r ⋆ (“inl” ⋆ a)                                                ≡⟨ abs-evalₙ (value _ (inl-def₁ a↓) ∷ value r r↓ ∷ value l l↓ ∷ []) ⟩
          “fst” ⋆ ⌜ “inl” ⋆ a ⌝ ⋆ l ⋆ r ⋆ (“snd” ⋆ ⌜ “inl” ⋆ a ⌝)                     ≡⟨ ap! (inl-eval a) ⟩
          ⌜ “fst” ⋆ (“pair” ⋆ “true” ⋆ a) ⌝ ⋆ l ⋆ r ⋆ (“snd” ⋆ (“pair” ⋆ “true” ⋆ a)) ≡⟨ ap! (fst-pair-eval “true” a a↓) ⟩
          ⌜ “const” ⋆ l ⋆ r ⌝ ⋆ (“snd” ⋆ (“pair” ⋆ “true” ⋆ a))                       ≡⟨ ap! (const-eval l r r↓) ⟩
          l ⋆ ⌜ “snd” ⋆ (“pair” ⋆ “true” ⋆ a) ⌝                                       ≡⟨ ap! (snd-pair-eval “true” a const-def) ⟩
          l ⋆ a                                                                       ∎)

    elim-inr-eval : ∀ (l r a : A) → ∣ l ↓ ∣ → “elim” ⋆ l ⋆ r ⋆ (“inr” ⋆ a) ≡ r ⋆ a
    elim-inr-eval l r a l↓ =
      def-ext (∣ l ↓ ∣ × ∣ r ↓ ∣ × ∣ a ↓ ∣)
        (λ p↓ → ⋆-defr (⋆-defl (⋆-defl p↓)) , ⋆-defr (⋆-defl p↓) , ⋆-defr (⋆-defr p↓))
        (λ ra↓ → l↓ , ⋆-defl ra↓ , (⋆-defr ra↓))
        (λ (l↓ , r↓ , a↓) →
          “elim” ⋆ l ⋆ r ⋆ (“inr” ⋆ a)                                                  ≡⟨ abs-evalₙ (value _ (inr-def₁ a↓) ∷ value r r↓ ∷ value l l↓ ∷ []) ⟩
          “fst” ⋆ ⌜ “inr” ⋆ a ⌝ ⋆ l ⋆ r ⋆ (“snd” ⋆ ⌜ “inr” ⋆ a ⌝)                       ≡⟨ ap! (inr-eval a) ⟩
          ⌜ “fst” ⋆ (“pair” ⋆ “false” ⋆ a) ⌝ ⋆ l ⋆ r ⋆ (“snd” ⋆ (“pair” ⋆ “false” ⋆ a)) ≡⟨ ap! (fst-pair-eval “false” a a↓) ⟩
          ⌜ “ignore” ⋆ l ⋆ r ⌝ ⋆ (“snd” ⋆ (“pair” ⋆ “false” ⋆ a))                       ≡⟨ ap! (ignore-eval l r l↓) ⟩
          r ⋆ ⌜ “snd” ⋆ (“pair” ⋆ “false” ⋆ a) ⌝                                        ≡⟨ ap! (snd-pair-eval “false” a ignore-def) ⟩
          r ⋆ a                                                                         ∎)
```

```agda
  inl-val : Val → Val
  inl-val a .elt = “inl” ⋆ a .elt
  inl-val a .def = inl-def₁ (a .def)

  inr-val : Val → Val
  inr-val a .elt = “inr” ⋆ a .elt
  inr-val a .def = inr-def₁ (a .def)

```
