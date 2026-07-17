

<!--
```agda
open import 1Lab.Type using (⊥)

open import Cat.Diagram.Coproduct
open import Cat.Diagram.Initial
open import Cat.Prelude

open import Data.Set.Truncation
open import Data.Id.Base
open import Data.Sum

open import Order.Base

import Order.Reasoning as Pr

open is-coproduct
open Coproduct
open Initial
```
-->

```agda
module Order.Instances.Coproduct where
```

# Coproducts of posets {defines="binary-coproduct-of-posets"}

If we're given two [[partially ordered sets]] $P, Q$, then there is a
universal way of equipping their [[coproduct|sum type]] (at the level of
sets) with a partial order, which results in the [[categorical
coproduct|coproduct]] in the category $\Pos$.

<!--
```agda
module _ {o o' ℓ ℓ'} (P : Poset o ℓ) (Q : Poset o' ℓ') where
  private
    module P = Pr P
    module Q = Pr Q
```
-->

The ordering is defined by recursion, and it's uniquely specified by
saying that it is the coproduct of orders, and that each coprojection is
an order embedding. We compute:

```agda
    sum-≤ : ⌞ P ⌟ ⊎ ⌞ Q ⌟ → ⌞ P ⌟ ⊎ ⌞ Q ⌟ → Type (ℓ ⊔ ℓ')
    sum-≤ (inl x) (inl y) = Lift ℓ' (x P.≤ y)
    sum-≤ (inl x) (inr y) = Lift _ ⊥
    sum-≤ (inr x) (inl y) = Lift _ ⊥
    sum-≤ (inr x) (inr y) = Lift ℓ (x Q.≤ y)
```

<details>
<summary>
A very straightforward case-bash shows that this is actually a partial
order. After we've established that everything is in a particular
summand, each obligation is something we inherit from the underlying
orders $P$ and $Q$.
</summary>

```agda
    abstract
      sum-≤-thin : ∀ {x y} → is-prop (sum-≤ x y)
      sum-≤-thin {inl x} {inl y} = hlevel 1
      sum-≤-thin {inr x} {inr y} = hlevel 1

      sum-≤-refl : ∀ {x} → sum-≤ x x
      sum-≤-refl {inl x} = lift P.≤-refl
      sum-≤-refl {inr x} = lift Q.≤-refl

      sum-≤-trans : ∀ {x y z} → sum-≤ x y → sum-≤ y z → sum-≤ x z
      sum-≤-trans {inl x} {inl y} {inl z} (lift p) (lift q) = lift (P.≤-trans p q)
      sum-≤-trans {inr x} {inr y} {inr z} (lift p) (lift q) = lift (Q.≤-trans p q)

      sum-≤-antisym : ∀ {x y} → sum-≤ x y → sum-≤ y x → x ≡ y
      sum-≤-antisym {inl x} {inl y} (lift p) (lift q) = ap inl (P.≤-antisym p q)
      sum-≤-antisym {inr x} {inr y} (lift p) (lift q) = ap inr (Q.≤-antisym p q)
```

</details>

```agda
  _⊎ᵖ_ : Poset (o ⊔ o') (ℓ ⊔ ℓ')
  _⊎ᵖ_ .Poset.Ob        = P.Ob ⊎ Q.Ob
  _⊎ᵖ_ .Poset._≤_       = sum-≤
  _⊎ᵖ_ .Poset.≤-thin    = sum-≤-thin
  _⊎ᵖ_ .Poset.≤-refl    = sum-≤-refl
  _⊎ᵖ_ .Poset.≤-trans   = sum-≤-trans
  _⊎ᵖ_ .Poset.≤-antisym = sum-≤-antisym

  infixr 15 _⊎ᵖ_
```

<!--
```agda
module _ {o o' ℓ} {P : Poset o ℓ} {Q : Poset o' ℓ} where
```
-->

As usual, we have two (monotone) coprojections $P \to P \uplus Q$ and $Q
\to P \uplus Q$; and, if we have maps $P \to R$ and $Q \to R$, we can
define a map out of the coproduct by cases:

```agda
  inlᵖ : Monotone P (P ⊎ᵖ Q)
  inlᵖ .hom        = inl
  inlᵖ .pres-≤ x≤y = lift x≤y

  inrᵖ : Monotone Q (P ⊎ᵖ Q)
  inrᵖ .hom        = inr
  inrᵖ .pres-≤ x≤y = lift x≤y

  matchᵖ : ∀ {o ℓ} {R : Poset o ℓ} → Monotone P R → Monotone Q R → Monotone (P ⊎ᵖ Q) R
  matchᵖ f g .hom (inl x) = f · x
  matchᵖ f g .hom (inr x) = g · x
  matchᵖ f g .pres-≤ {inl x} {inl y} (lift α) = f .pres-≤ α
  matchᵖ f g .pres-≤ {inr x} {inr y} (lift β) = g .pres-≤ β
```

A straightforward calculation shows that this really is the coproduct in
$\Pos$.

```agda
Posets-has-coproducts : ∀ {o ℓ} → has-coproducts (Posets o ℓ)
Posets-has-coproducts P Q .coapex = P ⊎ᵖ Q
Posets-has-coproducts P Q .ι₁ = inlᵖ
Posets-has-coproducts P Q .ι₂ = inrᵖ
Posets-has-coproducts P Q .has-is-coproduct .is-coproduct.[_,_] = matchᵖ
Posets-has-coproducts P Q .has-is-coproduct .[]∘ι₁ = ext λ _ → refl
Posets-has-coproducts P Q .has-is-coproduct .[]∘ι₂ = ext λ _ → refl
Posets-has-coproducts P Q .has-is-coproduct .unique α β = ext λ where
  (inl x) → sym α ·ₚ x
  (inr x) → sym β ·ₚ x
```

As a related fact, we can show that the empty poset is the [[initial
object]] in $\Pos$.

```agda
Posets-initial : ∀ {o ℓ} → Initial (Posets o ℓ)
Posets-initial .bot = 𝟘ᵖ
Posets-initial .has⊥ P .centre .hom    ()
Posets-initial .has⊥ P .centre .pres-≤ ()
Posets-initial .has⊥ P .paths f = ext λ ()
```
