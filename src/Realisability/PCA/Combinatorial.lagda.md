<!--
```agda
open import 1Lab.Prelude

open import Data.Partial.Total
open import Data.Partial.Base
open import Data.Fin.Base hiding (_<_ ; _≤_)
open import Data.Vec.Base

open import Realisability.PCA
```
-->

```agda
module Realisability.PCA.Combinatorial where
```

# Combinatory completeness

<!--
```agda
private variable
  ℓ : Level
  A : Type ℓ
  n : Nat
```
-->

```agda
record has-ski (_%_ : ↯ A → ↯ A → ↯ A) : Type (level-of A) where
  field
    K S : ↯ A

    K↓ : ⌞ K ⌟
    S↓ : ⌞ S ⌟

    K↓₁ : ∀ {x}   → ⌞ x ⌟ → ⌞ K % x ⌟
    K-β : ∀ {x y} → ⌞ x ⌟ → ⌞ y ⌟ → (K % x) % y ≡ x

    S↓₁ : ∀ {f}     → ⌞ f ⌟                 → ⌞ S % f ⌟
    S↓₂ : ∀ {f g}   → ⌞ f ⌟ → ⌞ g ⌟         → ⌞ (S % f) % g ⌟
    S-β : ∀ {f g x} → ⌞ f ⌟ → ⌞ g ⌟ → ⌞ x ⌟ → ((S % f) % g) % x ≡ ((f % x) % (g % x))
```

```agda
module _ {A : Type ℓ} {_%_ : ↯ A → ↯ A → ↯ A} (pca : has-ski _%_) (let infixl 8 _%_; _%_ = _%_) where
  open has-ski pca
  open eval _%_

  private
    i : ↯ A
    i = (S % K) % K

    `K `S `I : ∀ {n} → Term A n
    `K = const (K , K↓)
    `S = const (S , S↓)
    `I = const (i , S↓₂ K↓ K↓)

    abs : Term A (suc n) → Term A n
    abs (var n) with fin-view n
    ... | zero  = `I
    ... | suc i = app `K (var i)
    abs (const a) = app `K (const a)
    abs (app f x) = app (app `S (abs f)) (abs x)

    abs↓ : (t : Term A (suc n)) (ρ : Vec (↯⁺ A) n) → ⌞ eval (abs t) ρ ⌟
    abs↓ (var n) ρ with fin-view n
    ... | zero  = S↓₂ K↓ K↓
    ... | suc i = K↓₁ (lookup ρ i .snd)
    abs↓ (const x) ρ = K↓₁ (x .snd)
    abs↓ (app f x) ρ = S↓₂ (abs↓ f ρ) (abs↓ x ρ)

    abs-β
      : (t : Term A (suc n)) (ρ : Vec (↯⁺ A) n) (a : ↯⁺ A)
      → eval (abs t) ρ % a .fst ≡ eval (inst t (const a)) ρ
    abs-β (var x) ρ a with fin-view x
    ... | zero  = S-β K↓ K↓ (a .snd) ∙ K-β (a .snd) (K↓₁ (a .snd))
    ... | suc i = K-β (lookup ρ i .snd) (a .snd)
    abs-β (const x) ρ a = K-β (x .snd) (a .snd)
    abs-β (app f x) ρ a =
      (S % eval (abs f) ρ % eval (abs x) ρ % a .fst)          ≡⟨ S-β (abs↓ f ρ) (abs↓ x ρ) (a .snd) ⟩
      (eval (abs f) ρ % a .fst % (eval (abs x) ρ % a .fst))   ≡⟨ ap₂ _%_ (abs-β f ρ a) (abs-β x ρ a) ⟩
      (eval (inst f (const a)) ρ % eval (inst x (const a)) ρ) ∎

  has-ski→is-pca : is-pca _%_
  has-ski→is-pca = record { abs = abs ; abs↓ = abs↓ ; abs-β = abs-β }
```
