<!--
```agda
{-# OPTIONS -vtc.display:60 #-}
open import 1Lab.Prelude

open import Data.Partial.Total
open import Data.Partial.Base
open import Data.Fin.Base hiding (_<_ ; _≤_)
open import Data.Vec.Base
```
-->

```agda
module Realisability.PCA where
```

# Partial combinatory algebras

<!--
```agda
private variable
  ℓ : Level
  A : Type ℓ
  n : Nat
```
-->

```agda
data Term (A : Type ℓ) (n : Nat) : Type (level-of A) where
  var   : Fin n → Term A n
  const : ↯⁺ A → Term A n
  app   : Term A n → Term A n → Term A n

module eval (_%_ : ↯ A → ↯ A → ↯ A) where
  eval : Term A n → Vec (↯⁺ A) n → ↯ A
  eval (var x)   ρ = lookup ρ x .fst
  eval (const x) ρ = x .fst
  eval (app f x) ρ = eval f ρ % eval x ρ

  inst : Term A (suc n) → Term A n → Term A n
  inst (var x) a with fin-view x
  ... | zero = a
  ... | suc i = var i
  inst (const a) _ = const a
  inst (app f x) a = app (inst f a) (inst x a)

  abstract
    eval-inst
      : (t : Term A (suc n)) (x : ↯⁺ A) (ρ : Vec (↯⁺ A) n)
      → eval (inst t (const x)) ρ ≡ eval t (x ∷ ρ)
    eval-inst (var i) y ρ with fin-view i
    ... | zero  = refl
    ... | suc j = refl
    eval-inst (const a) y ρ = refl
    eval-inst (app f x) y ρ = ap₂ _%_ (eval-inst f y ρ) (eval-inst x y ρ)
```

```agda
record is-pca (_%_ : ↯ A → ↯ A → ↯ A) : Type (level-of A) where
  open eval _%_ public
  field
    abs   : Term A (suc n) → Term A n
    abs↓  : (t : Term A (suc n)) (ρ : Vec (↯⁺ A) n) → ⌞ eval (abs t) ρ ⌟
    abs-β : (t : Term A (suc n)) (ρ : Vec (↯⁺ A) n) (a : ↯⁺ A)
          → eval (abs t) ρ % a .fst ≡ eval (inst t (const a)) ρ

  absₙ : (k : Nat) → Term A (k + n) → Term A n
  absₙ zero    e = e
  absₙ (suc k) e = absₙ k (abs e)

  _%ₙ_ : ∀ {n} → ↯ A → Vec (↯⁺ A) n → ↯ A
  a %ₙ []       = a
  a %ₙ (b ∷ bs) = (a %ₙ bs) % b .fst

  abstract
    abs-βₙ
      : {k n : Nat} {e : Term A (k + n)}
      → (ρ : Vec (↯⁺ A) n) (as : Vec (↯⁺ A) k)
      → (eval (absₙ k e) ρ %ₙ as) ≡ eval e (as ++ ρ)
    abs-βₙ ρ [] = refl
    abs-βₙ {e = e} ρ (x ∷ as) = ap (_% x .fst) (abs-βₙ ρ as) ∙ abs-β _ (as ++ ρ) x ∙ eval-inst e x (as ++ ρ)

record PCA-on (A : Type ℓ) : Type ℓ where
  infixl 25 _%_

  field
    has-is-set : is-set A
    _%_        : ↯ A → ↯ A → ↯ A
    has-is-pca : is-pca _%_

  open is-pca has-is-pca public

PCA : (ℓ : Level) → Type (lsuc ℓ)
PCA ℓ = Σ[ X ∈ Set ℓ ] PCA-on ∣ X ∣

module PCA {ℓ} (A : PCA ℓ) where
  open PCA-on (A .snd) public
```
