<!--
```agda
open import 1Lab.Prelude

open import Data.Int
open import Data.Nat as Nat
```
-->

```agda
module Data.Int.Divisible where
```

# Divisibility of integers {defines="divisibility-of-integers"}

We define what it means for an [[integer]] to be [[divisible]] by a
natural number, as a straightforward generalisation of the case for
natural numbers.

```agda
_∣ℤ_ : Nat → Int → Type
zero  ∣ℤ y = y ≡ 0
suc x ∣ℤ y = fibre (_*ℤ possuc x) y

infix 7 _∣ℤ_

∣ℤ-is-prop : ∀ x y → is-prop (x ∣ℤ y)
∣ℤ-is-prop zero y n k = prop!
∣ℤ-is-prop (suc x) y (n , p) (n' , q) = Σ-prop-path! (*ℤ-injectiver-possuc x n n' (p ∙ sym q))

∣ℤ-is-truncation : ∀ {x y} → (x ∣ℤ y) ≃ ∥ fibre (_*ℤ pos x) y ∥
∣ℤ-is-truncation {zero} {y} =
  prop-ext!
    (λ p → inc (y , *ℤ-zeror y ∙ sym p))
    (rec! λ x p → sym p ∙ *ℤ-zeror x )
∣ℤ-is-truncation {suc x} {y} = Equiv.to is-prop≃equiv∥-∥ (∣ℤ-is-prop (suc x) y)

∣ℤ→fibre : ∀ {x y} → x ∣ℤ y → fibre (_*ℤ pos x) y
∣ℤ→fibre {zero} wit  = 0 , sym wit
∣ℤ→fibre {suc x} wit = wit

fibre→∣ℤ : ∀ {x y} → fibre (_*ℤ pos x) y → x ∣ℤ y
fibre→∣ℤ f = Equiv.from ∣ℤ-is-truncation (inc f)

dividesℤ : ∀ {x y} (q : Int) → q *ℤ pos x ≡ y → x ∣ℤ y
dividesℤ x p = fibre→∣ℤ (x , p)

∣ℤ-zero : ∀ {x} → x ∣ℤ 0
∣ℤ-zero = dividesℤ 0 refl

∣ℤ-one : ∀ {x} → 1 ∣ℤ x
∣ℤ-one {x} = dividesℤ x (*ℤ-oner x)

m∣ℤsn→m≤sn : ∀ {x y} → ¬ (y ≡ 0) → x ∣ℤ y → x Nat.≤ abs y
m∣ℤsn→m≤sn {x} {y} nz p with ∣ℤ→fibre p
... | posz , p = absurd (nz (sym p))
... | possuc k , p = difference→≤ (k * x)
  (ap abs (sym (assign-pos (x + k * x))) ∙ ap abs p)
... | negsuc k , p = difference→≤ (k * x)
  (sym (abs-negℤ (pos (x + k * x))) ∙ ap abs (sym (assign-neg (x + k * x))) ∙ ap abs p)

∣ℤ-+ : ∀ {k n m} → k ∣ℤ n → k ∣ℤ m → k ∣ℤ (n +ℤ m)
∣ℤ-+ {zero} {n} {m} p q = ap₂ _+ℤ_ p q
∣ℤ-+ {suc k} (x , p) (y , q) = x +ℤ y , *ℤ-distribr (possuc k) x y ∙ ap₂ _+ℤ_ p q

∣ℤ-negℤ : ∀ {k n} → k ∣ℤ n → k ∣ℤ negℤ n
∣ℤ-negℤ {zero} d = ap negℤ d
∣ℤ-negℤ {suc k} (x , p) = negℤ x , *ℤ-negl x _ ∙ ap negℤ p
```
