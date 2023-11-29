<!--
```agda
open import Cat.Prelude

open import Order.Instances.Props
open import Order.Diagram.Glb
open import Order.Diagram.Lub
open import Order.Displayed
open import Order.Base

import Order.Reasoning as Pr
```
-->

```agda
module Order.Instances.Pointwise where
```

# The pointwise ordering

If $(B, \le)$ is a [[partially ordered set]], then so is $A \to B$, for
any type $A$ which we might choose! There might be other ways of making
$A \to B$ into a poset, of course, but the canonical way we're talking
about here is the **pointwise ordering** on $A \to B$, where $f \le g$
iff $f(x) \le g(x)$ for all $x$.

```agda
Pointwise : ∀ {ℓ ℓₐ ℓᵣ} → Type ℓ → Poset ℓₐ ℓᵣ → Poset (ℓ ⊔ ℓₐ) (ℓ ⊔ ℓᵣ)
Pointwise A B = po where
  open Pr B

  po : Poset _ _
  po .Poset.Ob = A → ⌞ B ⌟
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
Subsets A = Pointwise A Props
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
module _ {o ℓ ℓ'} {A : Type ℓ'} {P : Poset o ℓ} where
  open Pr P

  Pointwise-has-top : Top P → Top (Pointwise A P) 
  Pointwise-has-top P-top .Top.top _ = Top.top P-top
  Pointwise-has-top P-top .Top.has-top f x =
    Top.has-top P-top (f x)

  Pointwise-has-bot : Bottom P → Bottom (Pointwise A P)
  Pointwise-has-bot P-bot .Bottom.bot _ = Bottom.bot P-bot
  Pointwise-has-bot P-bot .Bottom.has-bottom f x =
    Bottom.has-bottom P-bot (f x)

  Pointwise-has-meets
    : (∀ x y → Meet P x y)
    → ∀ f g → Meet (Pointwise A P) f g
  Pointwise-has-meets P-meet f g .Meet.glb x =
    Meet.glb (P-meet (f x) (g x))
  Pointwise-has-meets P-meet f g .Meet.has-meet .is-meet.meet≤l x =
    Meet.meet≤l (P-meet (f x) (g x))
  Pointwise-has-meets P-meet f g .Meet.has-meet .is-meet.meet≤r x =
    Meet.meet≤r (P-meet (f x) (g x))
  Pointwise-has-meets P-meet f g .Meet.has-meet .is-meet.greatest lb lb≤f lb≤g x =
    Meet.greatest (P-meet (f x) (g x)) (lb x) (lb≤f x) (lb≤g x)

  Pointwise-has-joins
    : (∀ x y → Join P x y)
    → ∀ f g → Join (Pointwise A P) f g
  Pointwise-has-joins P-join f g .Join.lub x =
    Join.lub (P-join (f x) (g x))
  Pointwise-has-joins P-join f g .Join.has-join .is-join.l≤join x =
    Join.l≤join (P-join (f x) (g x))
  Pointwise-has-joins P-join f g .Join.has-join .is-join.r≤join x =
    Join.r≤join (P-join (f x) (g x))
  Pointwise-has-joins P-join f g .Join.has-join .is-join.least ub f≤ub g≤ub x =
    Join.least (P-join (f x) (g x)) (ub x) (f≤ub x) (g≤ub x)

  Pointwise-has-glbs
    : ∀ {ℓ} {I : Type ℓ}
    → (∀ (k : I → ⌞ P ⌟) → Glb P k)
    → ∀ (k : I → A → ⌞ P ⌟) → Glb (Pointwise A P) k
  Pointwise-has-glbs P-glb k .Glb.glb x = Glb.glb (P-glb λ i → k i x)
  Pointwise-has-glbs P-glb k .Glb.has-glb .is-glb.glb≤fam i x =
    Glb.glb≤fam (P-glb λ j → k j x) i
  Pointwise-has-glbs P-glb k .Glb.has-glb .is-glb.greatest lb lb≤k x =
    Glb.greatest (P-glb (λ i → k i x)) (lb x) (λ i → lb≤k i x)

  Pointwise-has-lubs
    : ∀ {ℓ} {I : Type ℓ}
    → (∀ (k : I → ⌞ P ⌟) → Lub P k)
    → ∀ (k : I → A → ⌞ P ⌟) → Lub (Pointwise A P) k
  Pointwise-has-lubs P-lub k .Lub.lub x = Lub.lub (P-lub λ i → k i x)
  Pointwise-has-lubs P-lub k .Lub.has-lub .is-lub.fam≤lub i x =
    Lub.fam≤lub (P-lub λ j → k j x) i
  Pointwise-has-lubs P-lub k .Lub.has-lub .is-lub.least ub k≤ub x =
    Lub.least (P-lub (λ i → k i x)) (ub x) (λ i → k≤ub i x)
```
