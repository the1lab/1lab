<!--
```agda
open import Cat.Prelude

open import Data.Power

open import Order.Instances.Props
open import Order.Diagram.Glb
open import Order.Diagram.Lub
open import Order.Semilattice.Meet
open import Order.Semilattice.Join
open import Order.Base

import Order.Reasoning as Pr
```
-->

```agda
module Order.Instances.Pointwise where
```

# The pointwise ordering

The product of a family of [[partially ordered sets]] $\prod_{i : I} P_i$ is a
poset, for any index type $I$ which we might choose! There might be other ways
of making $\prod_{i : I} P_i$ into a poset, of course, but the canonical way
we're talking about here is the **pointwise ordering** on $\prod_{i : I} P_i$,
where $f \le g$ iff $f(x) \le g(x)$ for all $x$.

[partially ordered sets]: Order.Base.html

```agda
Pointwise : ∀ {ℓ ℓₐ ℓᵣ} (I : Type ℓ) (P : I → Poset ℓₐ ℓᵣ)
  → Poset (ℓ ⊔ ℓₐ) (ℓ ⊔ ℓᵣ)
Pointwise I P = po where
  open module PrP {i : I} = Pr (P i)

  po : Poset _ _
  po .Poset.Ob = (i : I) → ⌞ P i ⌟
  po .Poset._≤_ f g = ∀ x → f x ≤ g x
  po .Poset.≤-thin = hlevel!
  po .Poset.≤-refl x = ≤-refl
  po .Poset.≤-trans f≤g g≤h x = ≤-trans (f≤g x) (g≤h x)
  po .Poset.≤-antisym f≤g g≤f = funext λ x → ≤-antisym (f≤g x) (g≤f x)
```

A very important particular case of the pointwise ordering is the poset
of subsets of a fixed type, which has underlying set $A \to \Omega$.

```agda
Subsets : ∀ {ℓ} → Type ℓ → Poset ℓ ℓ
Subsets A = Pointwise A (λ _ → Props)
```

Another important case: when your domain is not an arbitrary type but
another poset, you might want to consider the full subposet of $P \to Q$
consisting of the monotone maps:

```agda
Poset[_,_] : ∀ {ℓₒ ℓᵣ ℓₒ' ℓᵣ'}
         → Poset ℓₒ ℓᵣ
         → Poset ℓₒ' ℓᵣ'
         → Poset (ℓₒ ⊔ ℓᵣ ⊔ ℓₒ' ⊔ ℓᵣ') (ℓₒ ⊔ ℓᵣ')
Poset[_,_] P Q = po where
  open Pr Q

  po : Poset _ _
  po .Poset.Ob = Monotone P Q
  po .Poset._≤_ f g = ∀ (x : ⌞ P ⌟) → f # x ≤ g # x
  po .Poset.≤-thin = hlevel!
  po .Poset.≤-refl _ = ≤-refl
  po .Poset.≤-trans f≤g g≤h x = ≤-trans (f≤g x) (g≤h x)
  po .Poset.≤-antisym f≤g g≤f = ext (λ x → ≤-antisym (f≤g x) (g≤f x))
```

# Meets and Joins

```agda
module _ {o ℓ ℓ'} {A : Type ℓ'} {P : A → Poset o ℓ} where

  Pointwise-has-top : (∀ a → Top (P a)) → Top (Pointwise A P)
  Pointwise-has-top P-top .Top.top a = Top.top (P-top a)
  Pointwise-has-top P-top .Top.has-top f a = Top.has-top (P-top a) (f a)

  Pointwise-has-bot : (∀ a → Bottom (P a)) → Bottom (Pointwise A P)
  Pointwise-has-bot P-bot .Bottom.bot a = Bottom.bot (P-bot a)
  Pointwise-has-bot P-bot .Bottom.has-bottom f a = Bottom.has-bottom (P-bot a) (f a)

  Pointwise-has-meets
    : (∀ a x y → Meet (P a) x y)
    → ∀ f g → Meet (Pointwise A P) f g
  Pointwise-has-meets P-meet f g .Meet.glb a =
    Meet.glb (P-meet a (f a) (g a))
  Pointwise-has-meets P-meet f g .Meet.has-meet .is-meet.meet≤l a =
    Meet.meet≤l (P-meet a (f a) (g a))
  Pointwise-has-meets P-meet f g .Meet.has-meet .is-meet.meet≤r a =
    Meet.meet≤r (P-meet a (f a) (g a))
  Pointwise-has-meets P-meet f g .Meet.has-meet .is-meet.greatest lb lb≤f lb≤g a =
    Meet.greatest (P-meet a (f a) (g a)) (lb a) (lb≤f a) (lb≤g a)

  Pointwise-has-joins
    : (∀ a x y → Join (P a) x y)
    → ∀ f g → Join (Pointwise A P) f g
  Pointwise-has-joins P-join f g .Join.lub a =
    Join.lub (P-join a (f a) (g a))
  Pointwise-has-joins P-join f g .Join.has-join .is-join.l≤join a =
    Join.l≤join (P-join a (f a) (g a))
  Pointwise-has-joins P-join f g .Join.has-join .is-join.r≤join a =
    Join.r≤join (P-join a (f a) (g a))
  Pointwise-has-joins P-join f g .Join.has-join .is-join.least ub f≤ub g≤ub a =
    Join.least (P-join a (f a) (g a)) (ub a) (f≤ub a) (g≤ub a)

  Pointwise-has-glbs
    : ∀ {ℓ} {I : Type ℓ}
    → (∀ a → (k : I → ⌞ P a ⌟) → Glb (P a) k)
    → ∀ (k : I → (a : A) → ⌞ P a ⌟) → Glb (Pointwise A P) k
  Pointwise-has-glbs P-glb k .Glb.glb a = Glb.glb (P-glb a λ i → k i a)
  Pointwise-has-glbs P-glb k .Glb.has-glb .is-glb.glb≤fam i a =
    Glb.glb≤fam (P-glb a λ j → k j a) i
  Pointwise-has-glbs P-glb k .Glb.has-glb .is-glb.greatest lb lb≤k a =
    Glb.greatest (P-glb a (λ i → k i a)) (lb a) (λ i → lb≤k i a)

  Pointwise-has-lubs
    : ∀ {ℓ} {I : Type ℓ}
    → (∀ a →  (k : I → ⌞ P a ⌟) → Lub (P a) k)
    → ∀ (k : I → (a : A) → ⌞ P a ⌟) → Lub (Pointwise A P) k
  Pointwise-has-lubs P-lub k .Lub.lub a = Lub.lub (P-lub a λ i → k i a)
  Pointwise-has-lubs P-lub k .Lub.has-lub .is-lub.fam≤lub i a =
    Lub.fam≤lub (P-lub a λ j → k j a) i
  Pointwise-has-lubs P-lub k .Lub.has-lub .is-lub.least ub k≤ub a =
    Lub.least (P-lub a (λ i → k i a)) (ub a) (λ i → k≤ub i a)
```

<!--
```agda
  open is-meet-semilattice
  open is-join-semilattice

  Pointwise-is-meet-slat
    : (∀ a → is-meet-semilattice (P a))
    → is-meet-semilattice (Pointwise A P)
  Pointwise-is-meet-slat meet-slat .has-meets x y =
    Pointwise-has-meets (λ a → has-meets (meet-slat a)) x y
  Pointwise-is-meet-slat meet-slat .has-top =
    Pointwise-has-top (λ a → has-top (meet-slat a))

  Pointwise-is-join-slat
    : (∀ a → is-join-semilattice (P a))
    → is-join-semilattice (Pointwise A P)
  Pointwise-is-join-slat join-slat .has-joins x y =
    Pointwise-has-joins (λ a → has-joins (join-slat a)) x y
  Pointwise-is-join-slat join-slat .has-bottom =
    Pointwise-has-bot (λ a → has-bottom (join-slat a))

Subsets-is-meet-slat : ∀ {ℓ} {A : Type ℓ} → is-meet-semilattice (Subsets A)
Subsets-is-meet-slat = Pointwise-is-meet-slat (λ _ → Props-is-meet-slat)

Subsets-is-join-slat : ∀ {ℓ} {A : Type ℓ} → is-join-semilattice (Subsets A)
Subsets-is-join-slat = Pointwise-is-join-slat (λ _ → Props-is-join-slat)
```
-->

Every subset is a least upper bound of singleton sets.

```agda
subset-singleton-lub
  : ∀ {ℓ} {A : Type ℓ}
  → (P : A → Ω)
  → is-lub (Subsets A) {I = ∫ₚ P} (singleton ⊙ fst) P
subset-singleton-lub P .is-lub.fam≤lub (x , x∈P) y □x=y =
  □-rec! (λ x=y → subst (_∈ P) x=y x∈P) □x=y
subset-singleton-lub P .is-lub.least ub sing≤ub x x∈P =
  sing≤ub (x , x∈P) x (inc refl)
```
