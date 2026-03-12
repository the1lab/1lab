<!--
```agda
open import 1Lab.Prelude

open import Data.Bool.Base
open import Data.Dec.Base
open import Data.Nat.Base
open import Data.Sum

import Prim.Data.Nat as Prim
```
-->

```agda
module Data.Nat.Order where
```

# Properties of ordering on ℕ

We establish the basic properties of ordering on the natural numbers.
These are properties of the order itself, and not how it interacts with
the semiring structure. For that, see
[`Data.Nat.Properties`](Data.Nat.Properties.html). The first thing we
establish is that $x \le y$ is a [[partial order]], so it deserves the
name $\le$: It is reflexive, transitive, antisymmetric, and takes values
in propositions. In all cases, save for reflexivity, the induction
happens on the witnesses of ordering, and Agda handles inducting on the
naturals automatically.

```agda
≤-refl : ∀ {x : Nat} → x ≤ x
≤-refl {zero}  = 0≤x
≤-refl {suc x} = s≤s ≤-refl
```

<!--
```agda
≤-refl' : ∀ {x y} → .(x ≡ y) → x ≤ y
≤-refl' {zero} {zero} p = 0≤x
≤-refl' {zero} {suc y} p = absurd (zero≠suc p)
≤-refl' {suc x} {zero} p = absurd (suc≠zero p)
≤-refl' {suc x} {suc y} p = s≤s (≤-refl' (suc-inj p))

≤-reflᵢ : ∀ {x y} → .(x ≡ᵢ y) → x ≤ y
≤-reflᵢ p = ≤-refl' (Id-identity-system .to-path p)
```
-->

```agda
≤-antisym : ∀ {x y : Nat} → x ≤ y → y ≤ x → x ≡ y
≤-antisym {zero} {zero} x≤y y≤x = refl
≤-antisym {suc x} {suc y} x≤y y≤x = ap suc (≤-antisym (≤-peel x≤y) (≤-peel y≤x))
```

As a minor convenience, we prove that the constructor `s≤s`{.Agda} is an
equivalence between $x \le y$ and $(1 + x) \le (1 + y)$.

```agda
≤-ascend : ∀ {x} → x ≤ suc x
≤-ascend = ≤-sucr ≤-refl
```

<!--
```agda
private
  from-prim-< : ∀ x y → ⌞ x Prim.< y ⌟ → x < y
  from-prim-< zero (suc y) o = s≤s 0≤x
  from-prim-< (suc x) (suc y) o = s≤s (from-prim-< x y o)

  to-prim-< : ∀ x y → x < y → ⌞ x Prim.< y ⌟
  to-prim-< zero (suc y) o = oh
  to-prim-< (suc x) (suc y) o = to-prim-< x y (≤-peel o)
```
-->

### Properties of the strict order

```agda
<-≤-asym : ∀ {x y} → x < y → ¬ (y ≤ x)
<-≤-asym {suc x} {suc y} x<y y≤x = <-≤-asym (≤-peel x<y) (≤-peel y≤x)

<-asym : ∀ {x y} → x < y → ¬ (y < x)
<-asym {suc x} {suc y} x<y y<x = <-≤-asym x<y (<-weaken y<x)

<-not-equal : ∀ {x y} → x < y → x ≠ y
<-not-equal x<y x=y = <-≤-asym x<y (≤-refl' (sym x=y))

<-irrefl : ∀ {x y} → x ≡ y → ¬ (x < y)
<-irrefl x=y x<y = <-not-equal x<y x=y

≤-strengthen : ∀ {x y} → x ≤ y → (x ≡ y) ⊎ (x < y)
≤-strengthen {zero} {zero} x≤y = inl refl
≤-strengthen {zero} {suc y} x≤y = inr (s≤s 0≤x)
≤-strengthen {suc x} {suc y} x≤y with ≤-strengthen (≤-peel x≤y)
... | inl eq = inl (ap suc eq)
... | inr le = inr (s≤s le)

<-from-≤ : ∀ {x y} → x ≠ y → x ≤ y → x < y
<-from-≤ x≠y x≤y with ≤-strengthen x≤y
... | inl x=y = absurd (x≠y x=y)
... | inr x<y = x<y
```

### Linearity

Furthermore, `_≤_`{.Agda} is decidable, and weakly total:

<!--
```agda
module _ where private
```
-->

```agda
  ≤-dec : (x y : Nat) → Dec (x ≤ y)
  ≤-dec zero zero = yes 0≤x
  ≤-dec zero (suc y) = yes 0≤x
  ≤-dec (suc x) zero = no λ { () }
  ≤-dec (suc x) (suc y) with ≤-dec x y
  ... | yes x≤y = yes (s≤s x≤y)
  ... | no ¬x≤y = no (¬x≤y ∘ ≤-peel)

≤-is-weakly-total : ∀ x y → ¬ (x ≤ y) → y ≤ x
≤-is-weakly-total zero    zero    _    = 0≤x
≤-is-weakly-total zero    (suc y) ¬0≤s = absurd (¬0≤s 0≤x)
≤-is-weakly-total (suc x) zero    _    = 0≤x
≤-is-weakly-total (suc x) (suc y) ¬s≤s = s≤s $
  ≤-is-weakly-total x y λ z → ¬s≤s (s≤s z)
```

<!--
```agda
<-from-not-≤ : ∀ x y → ¬ (x ≤ y) → y < x
<-from-not-≤ zero    zero    x    = absurd (x 0≤x)
<-from-not-≤ zero    (suc y) ¬0≤s = absurd (¬0≤s 0≤x)
<-from-not-≤ (suc x) zero    _    = s≤s 0≤x
<-from-not-≤ (suc x) (suc y) ¬s≤s = s≤s $
  <-from-not-≤ x y λ z → ¬s≤s (s≤s z)

≤-from-not-< : ∀ x y → ¬ (x < y) → y ≤ x
≤-from-not-< zero zero p = 0≤x
≤-from-not-< zero (suc y) p = absurd (p (s≤s 0≤x))
≤-from-not-< (suc x) zero p = 0≤x
≤-from-not-< (suc x) (suc y) p = s≤s (≤-from-not-< x y (p ∘ s≤s))

<-trans : ∀ x y z → x < y → y < z → x < z
<-trans x (suc y) (suc z) x<y y<z = ≤-trans x<y (<-weaken y<z)

≤-uncap : ∀ m n → m ≠ suc n → m ≤ suc n → m ≤ n
≤-uncap zero n p m≤n+1 = 0≤x
≤-uncap (suc m) (suc n) p m≤n+1 = s≤s (≤-uncap m n (p ∘ ap suc) (≤-peel m≤n+1))
≤-uncap (suc zero) zero p m≤n+1 = absurd (p refl)
```
-->

<!--
```agda
≤-dec : (x y : Nat) → Dec (x ≤ y)
≤-dec x y with oh? (x ≤? y)
... | yes x≤y = yes (lift x≤y)
... | no ¬x≤y = no (¬x≤y ∘ _≤_.lower)

instance
  Dec-≤ : ∀ {x y} → Dec (x ≤ y)
  Dec-≤ = ≤-dec _ _
```
-->

We also have that a successor is never smaller than the number it
succeeds:

```agda
¬sucx≤x : (x : Nat) → ¬ (suc x ≤ x)
¬sucx≤x (suc x) 1+x≤x = ¬sucx≤x x (≤-peel 1+x≤x)
```

We can do proofs on pairs of natural numbers by splitting into cases of
their strict ordering:

```agda
≤-split : ∀ (x y : Nat) → (x < y) ⊎ (y < x) ⊎ (x ≡ y)
≤-split x y with ≤-dec (suc x) y
≤-split x y | yes x<y = inl x<y
≤-split x y | no x≥y with ≤-dec (suc y) x
≤-split x y | no x≥y | yes y<x = inr (inl y<x)
≤-split x y | no x≥y | no y≥x  = inr (inr (go x y x≥y y≥x)) where
  go : ∀ x y → ¬ (suc x ≤ y) → ¬ (suc y ≤ x) → x ≡ y
  go zero zero p q          = refl
  go zero (suc zero) p q    = absurd (p (s≤s 0≤x))
  go zero (suc (suc y)) p q = absurd (p (s≤s 0≤x))
  go (suc zero) zero p q    = absurd (q (s≤s 0≤x))
  go (suc (suc x)) zero p q = absurd (q (s≤s 0≤x))
  go (suc x) (suc y) p q    = ap suc (go x y (λ { a → p (s≤s a) }) λ { a → q (s≤s a) })
```

## Nat is a lattice

An interesting tidbit about the ordering on $\NN$ is that it is, in some
sense, generated by the max operator: We have $x \le y$ iff $max(x,y) =
y$. It can also be generated by the min operator, but we don't establish
that here (it is a more general fact about
[lattices](Order.Lattice.html)).

```agda
≤-iff-max : ∀ {x y} → (x ≤ y) ≃ (y ≡ max x y)
≤-iff-max = prop-ext! to from where
  to : ∀ {x y} → x ≤ y → y ≡ max x y
  to {0} {zero} x≤y = refl
  to {0} {suc y} x≤y = refl
  to {suc x} {suc y} x≤y = ap suc (to (≤-peel x≤y))

  from : ∀ {x y} → y ≡ max x y → x ≤ y
  from {zero} p = 0≤x
  from {suc x} {zero} p = absurd (zero≠suc p)
  from {suc x} {suc y} p = s≤s (from (suc-inj p))
```

## Well-ordering {defines="N-is-well-ordered"}

In classical mathematics, the well-ordering principle states that every
nonempty subset of the natural numbers has a minimal element. In
constructive mathematics, there are subsets of $\bb{N}$ which only have
a minimal elements if excluded middle holds. The LEM-agnostic statement
is that every [[inhabited|propositional truncation]] [_complemented_]
subset of the natural numbers has a minimal element. Note that for a
complemented subset, inhabitation is the same as nonemptiness, but we
prefer the stronger phrasing since it makes the proof one step shorter.

[_complemented_]: Data.Power.Complemented.html

The "subset" part only comes in at the start: To get out from under the
truncation, we need the fact that minimal solutions are unique. Given a
minimal solution $(n, p)$ and one $(k, q')$, we have that $n = k$ since
both are minimal (so $k \le n$ and $n \le k$), but we do not^[We're
implicitly appealing to path induction to reduce this to the case where
$p, q : P(n)$] automatically have that $p = q$.

```agda
minimal-solution : ∀ {ℓ} (P : Nat → Type ℓ) → Type _
minimal-solution P = Σ[ n ∈ Nat ] (P n × (∀ k → P k → n ≤ k))

minimal-solution-unique
  : ∀ {ℓ} {P : Nat → Prop ℓ}
  → is-prop (minimal-solution λ x → ∣ P x ∣)
minimal-solution-unique (n , pn , n-min) (k , pk , k-min) =
  Σ-prop-path! (≤-antisym (n-min _ pk) (k-min _ pn))
```

The step of the code that actually finds a minimal solution does not
need $P$ to be a predicate: we only need that for actually searching for
an inhabited subset.

```agda
min-suc
  : ∀ {ℓ} {P : Nat → Type ℓ}
  → ∀ n → ¬ P 0
  → (∀ k → P (suc k) → n ≤ k)
  → ∀ k → P k → suc n ≤ k
min-suc n ¬p0 nmins zero pk           = absurd (¬p0 pk)
min-suc zero ¬p0 nmins (suc k) psk    = s≤s 0≤x
min-suc (suc n) ¬p0 nmins (suc k) psk = s≤s (nmins k psk)

ℕ-minimal-solution
  : ∀ {ℓ} (P : Nat → Type ℓ)
  → (∀ n → Dec (P n))
  → (n : Nat) → P n
  → minimal-solution P
ℕ-minimal-solution P decp zero p = 0 , p , λ k _ → 0≤x
ℕ-minimal-solution P decp (suc n) p = case decp zero of λ where
  (yes p0) → 0 , p0 , λ k _ → 0≤x
  (no ¬p0) →
    let (a , pa , x) = ℕ-minimal-solution (P ∘ suc) (decp ∘ suc) n p
      in suc a , pa , min-suc {P = P} a ¬p0 x

ℕ-well-ordered
  : ∀ {ℓ} {P : Nat → Prop ℓ}
  → (∀ n → Dec ∣ P n ∣)
  → ∃[ n ∈ Nat ] ∣ P n ∣
  → Σ[ n ∈ Nat ] (∣ P n ∣ × (∀ k → ∣ P k ∣ → n ≤ k))
ℕ-well-ordered {P = P} P-dec wit = ∥-∥-rec (minimal-solution-unique {P = P})
  (λ { (n , p) → ℕ-minimal-solution _ P-dec n p }) wit
```
