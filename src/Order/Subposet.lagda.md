<!--
```agda
open import Cat.Prelude

open import Order.Diagram.Bottom
open import Order.Diagram.Join
open import Order.Diagram.Meet
open import Order.Diagram.Lub
open import Order.Diagram.Top
open import Order.Morphism
open import Order.Base

import Order.Reasoning
```
-->

```agda
module Order.Subposet where
```

# Subposets {defines=subposet}

Let $A$ be a poset, and $P : A \to \prop$ be a predicate on $A$. We
can form a **subposet** of $A$ by restricting to the elements of $A$
where $P$ holds.

```agda
module _ {o ℓ} (A : Poset o ℓ) where
  open Order.Reasoning A

  Subposet : ∀ {ℓ'} → (P : Ob → Prop ℓ') → Poset (o ⊔ ℓ') ℓ
  Subposet P .Poset.Ob = ∫ₚ P
  Subposet P .Poset._≤_ (a , _) (b , _) = a ≤ b
  Subposet P .Poset.≤-thin = ≤-thin
  Subposet P .Poset.≤-refl = ≤-refl
  Subposet P .Poset.≤-trans = ≤-trans
  Subposet P .Poset.≤-antisym p q = Σ-prop-path! (≤-antisym p q)
```

Every subposet includes into the original order it was constructed
from, and this inclusion is an [[order embedding]].

```agda
module _ {o ℓ ℓ'} {A : Poset o ℓ} (P : ⌞ A ⌟ → Prop ℓ') where
  open Order.Reasoning A

  subposet-inc : Monotone (Subposet A P) A
  subposet-inc .hom = fst
  subposet-inc .pres-≤ p = p

  subposet-inc-is-order-embedding
    : is-order-embedding (Subposet A P) A (apply subposet-inc)
  subposet-inc-is-order-embedding = _ , id-equiv

module _ {o ℓ ℓ'} {A : Poset o ℓ} {P : ⌞ A ⌟ → Prop ℓ'} where
  open Order.Reasoning A

  subposet-inc-inj : injective (apply (subposet-inc {A = A} P))
  subposet-inc-inj p = Σ-prop-path! p
```

## Joins and Meets in Subposets

If $A$ has joins or meets, and $P$ is closed under those joins and
meets, then the subposet induced by $P$ also has those joins and meets.

```agda
  open is-meet
  open is-join
  open is-lub

  subposet-has-top
    : ∀ {x} (px : x ∈ P) → is-top A x → is-top (Subposet A P) (x , px)
  subposet-has-top px x-top (y , _) = x-top y

  subposet-has-bottom
    : ∀ {x} (px : x ∈ P) → is-bottom A x → is-bottom (Subposet A P) (x , px)
  subposet-has-bottom px x-bottom (y , _) = x-bottom y

  subposet-has-meet
    : ∀ {x y z} (px : x ∈ P) (py : y ∈ P) (pz : z ∈ P)
    → is-meet A x y z → is-meet (Subposet A P) (x , px) (y , py) (z , pz)
  subposet-has-meet px py pz z-meet .meet≤l = z-meet .meet≤l
  subposet-has-meet px py pz z-meet .meet≤r = z-meet .meet≤r
  subposet-has-meet px py pz z-meet .greatest (lb , _) = z-meet .greatest lb

  subposet-has-join
    : ∀ {x y z} (px : x ∈ P) (py : y ∈ P) (pz : z ∈ P)
    → is-join A x y z → is-join (Subposet A P) (x , px) (y , py) (z , pz)
  subposet-has-join px py pz z-join .l≤join = z-join .l≤join
  subposet-has-join px py pz z-join .r≤join = z-join .r≤join
  subposet-has-join px py pz z-join .least (lb , _) = z-join .least lb

  subposet-has-lub
    : ∀ {ℓᵢ} {I : Type ℓᵢ} {k : I → Ob} {x : Ob} (pk : ∀ i → k i ∈ P) (px : x ∈ P)
    → is-lub A k x → is-lub (Subposet A P) (λ i → k i , pk i) (x , px)
  subposet-has-lub pk px has-lub .fam≤lub i = has-lub .fam≤lub i
  subposet-has-lub pk px has-lub .least ub fam≤ub =
    has-lub .least (ub .fst) fam≤ub
```

<!--
```agda
  subposet-top : (has-top : Top A) → Top.top has-top ∈ P → Top (Subposet A P)
  subposet-top has-top top∈P .Top.top = Top.top has-top , top∈P
  subposet-top has-top top∈P .Top.has-top =
    subposet-has-top  top∈P (Top.has-top has-top)

  subposet-bottom
    : (has-bottom : Bottom A) → Bottom.bot has-bottom ∈ P → Bottom (Subposet A P)
  subposet-bottom has-bottom bottom∈P .Bottom.bot = Bottom.bot has-bottom , bottom∈P
  subposet-bottom has-bottom bottom∈P .Bottom.has-bottom =
    subposet-has-bottom bottom∈P (Bottom.has-bottom has-bottom)

  subposet-meets
    : (has-meets : Has-meets A)
    → (meet∈P : ∀ {x y} → x ∈ P → y ∈ P → Meet.glb (has-meets x y) ∈ P)
    → ∀ {x y} px py → Meet (Subposet A P) (x , px) (y , py)
  subposet-meets has-meets meet∈P {x} {y} x∈P y∈P .Meet.glb =
    Meet.glb (has-meets x y) , meet∈P x∈P y∈P
  subposet-meets has-meets meet∈P {x} {y} x∈P y∈P .Meet.has-meet =
    subposet-has-meet x∈P y∈P (meet∈P x∈P y∈P) (Meet.has-meet (has-meets x y))

  subposet-joins
    : (has-joins : Has-joins A)
    → (join∈P : ∀ {x y} → x ∈ P → y ∈ P → Join.lub (has-joins x y) ∈ P)
    → ∀ {x y} px py → Join (Subposet A P) (x , px) (y , py)
  subposet-joins has-joins join∈P {x} {y} x∈P y∈P .Join.lub =
    Join.lub (has-joins x y) , join∈P x∈P y∈P
  subposet-joins has-joins join∈P {x} {y} x∈P y∈P .Join.has-join =
    subposet-has-join x∈P y∈P (join∈P x∈P y∈P) (Join.has-join (has-joins x y))
```
-->
