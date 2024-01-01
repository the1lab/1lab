<!--
```agda
open import 1Lab.Reflection.Marker

open import Cat.Diagram.Product.Indexed
open import Cat.Morphism
open import Cat.Prelude

open import Data.Power
open import Data.Bool

open import Order.Instances.Product
open import Order.Semilattice.Join
open import Order.Semilattice.Meet
open import Order.Instances.Props
open import Order.Diagram.Bottom
open import Order.Diagram.Join
open import Order.Diagram.Meet
open import Order.Diagram.Glb
open import Order.Diagram.Lub
open import Order.Diagram.Top
open import Order.Univalent
open import Order.Base

import Order.Reasoning as Pr

open is-indexed-product
open Indexed-product
open Inverses
```
-->

```agda
module Order.Instances.Pointwise where
```

# The pointwise ordering {defines="pointwise-ordering"}

The product of a family of [[partially ordered sets]] $\prod_{i : I} P_i$ is a
poset, for any index type $I$ which we might choose! There might be other ways
of making $\prod_{i : I} P_i$ into a poset, of course, but the canonical way
we're talking about here is the **pointwise ordering** on $\prod_{i : I} P_i$,
where $f \le g$ iff $f(x) \le g(x)$ for all $x$.

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

tupleᵖ
  : ∀ {ℓ ℓₐ ℓₐ' ℓᵣ ℓᵣ'} {I : Type ℓ} {P : I → Poset ℓₐ ℓᵣ} {R : Poset ℓₐ' ℓᵣ'}
  → (∀ i → Monotone R (P i))
  → Monotone R (Pointwise I P)
tupleᵖ f .hom x i = f i # x
tupleᵖ f .pres-≤ x≤y i = f i .pres-≤ x≤y

prjᵖ
  : ∀ {ℓ ℓₐ ℓᵣ} {I : Type ℓ} {P : I → Poset ℓₐ ℓᵣ} (i : I)
  → Monotone (Pointwise I P) (P i)
prjᵖ i .hom f      = f i
prjᵖ i .pres-≤ f≤g = f≤g i
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
Poset[_,_]
  : ∀ {ℓₒ ℓᵣ ℓₒ' ℓᵣ'}
  → (P : Poset ℓₒ ℓᵣ) (Q : Poset ℓₒ' ℓᵣ')
  → Poset (ℓₒ ⊔ ℓᵣ ⊔ ℓₒ' ⊔ ℓᵣ') (ℓₒ ⊔ ℓᵣ')
Poset[_,_] P Q = po module Poset[_,_] where
  open Pr Q

  po : Poset _ _
  po .Poset.Ob      = Monotone P Q
  po .Poset._≤_ f g = ∀ (x : ⌞ P ⌟) → f # x ≤ g # x

  po .Poset.≤-thin   = hlevel!
  po .Poset.≤-refl _ = ≤-refl

  po .Poset.≤-trans   f≤g g≤h x = ≤-trans (f≤g x) (g≤h x)
  po .Poset.≤-antisym f≤g g≤f   = ext λ x → ≤-antisym (f≤g x) (g≤f x)
```

Using `Pointwise`{.Agda} we can show that $\Pos$ has all indexed products:

```agda
Posets-has-indexed-products
  : ∀ {o ℓ ℓ'}
  → has-indexed-products (Posets (o ⊔ ℓ') (ℓ ⊔ ℓ')) ℓ'
Posets-has-indexed-products F = mk where
  mk : Indexed-product (Posets _ _) _
  mk .ΠF = Pointwise _ F
  mk .π  = prjᵖ
  mk .has-is-ip .tuple   = tupleᵖ
  mk .has-is-ip .commute = trivial!
  mk .has-is-ip .unique f g = ext λ y i → g i #ₚ y
```

## Binary products are a special case of indexed products

```agda
×≡Pointwise-bool : ∀ {o ℓ} (P Q : Poset o ℓ) → P ×ᵖ Q ≡ Pointwise Bool (if_then P else Q)
×≡Pointwise-bool P Q = Poset-path λ where
  .to   → tupleᵖ (Bool-elim _ fstᵖ sndᵖ)
  .from → pairᵖ (prjᵖ true) (prjᵖ false)
  .inverses .invl → ext λ where
    x true → refl
    x false → refl
  .inverses .invr → ext λ _ → refl , refl
```

# Meets and Joins

<!--
```agda
module _ {o ℓ ℓ'} {A : Type ℓ'} {P : A → Poset o ℓ} where
```
-->

```agda
  open Top

  Pointwise-has-top : (∀ a → Top (P a)) → Top (Pointwise A P)
  Pointwise-has-top P-top .top a = P-top a .top
  Pointwise-has-top P-top .has-top f a = P-top a .has-top (f a)

  open Bottom

  Pointwise-has-bot : (∀ a → Bottom (P a)) → Bottom (Pointwise A P)
  Pointwise-has-bot P-bot .bot a = P-bot a .bot
  Pointwise-has-bot P-bot .has-bottom f a = P-bot a .has-bottom (f a)

  open is-meet
  open Meet

  Pointwise-has-meets : (∀ a → Has-meets (P a)) → Has-meets (Pointwise A P)
  Pointwise-has-meets P-meet f g .glb a =
    P-meet a (f a) (g a) .glb
  Pointwise-has-meets P-meet f g .has-meet .meet≤l a =
    P-meet a (f a) (g a) .Meet.meet≤l
  Pointwise-has-meets P-meet f g .has-meet .meet≤r a =
    P-meet a (f a) (g a) .Meet.meet≤r
  Pointwise-has-meets P-meet f g .has-meet .greatest lb lb≤f lb≤g a =
    P-meet a (f a) (g a) .Meet.greatest (lb a) (lb≤f a) (lb≤g a)

  open is-join
  open Join

  Pointwise-has-joins : (∀ a → Has-joins (P a)) → Has-joins (Pointwise A P)
  Pointwise-has-joins P-join f g .lub a = P-join a (f a) (g a) .lub
  Pointwise-has-joins P-join f g .has-join .l≤join a =
    P-join a (f a) (g a) .Join.l≤join
  Pointwise-has-joins P-join f g .has-join .r≤join a =
    P-join a (f a) (g a) .Join.r≤join
  Pointwise-has-joins P-join f g .has-join .least ub f≤ub g≤ub a =
    P-join a (f a) (g a) .Join.least (ub a) (f≤ub a) (g≤ub a)

  open is-glb
  open Glb

  Pointwise-has-glbs
    : ∀ {ℓ} {I : Type ℓ}
    → (∀ a (k : I → _) → Glb (P a) k)
    → (k : (i : I) (a : A) → ⌞ P a ⌟) → Glb (Pointwise A P) k
  Pointwise-has-glbs P-glb k .glb a = P-glb a (λ i → k i a) .glb
  Pointwise-has-glbs P-glb k .has-glb .glb≤fam i a =
    P-glb a (λ j → k j a) .Glb.glb≤fam i
  Pointwise-has-glbs P-glb k .has-glb .greatest lb lb≤k a =
    P-glb a (λ i → k i a) .Glb.greatest (lb a) λ i → lb≤k i a

  open is-lub
  open Lub

  Pointwise-has-lubs
    : ∀ {ℓ} {I : Type ℓ}
    → (∀ a → (k : I → ⌞ P a ⌟) → Lub (P a) k)
    → ∀ (k : I → (a : A) → ⌞ P a ⌟) → Lub (Pointwise A P) k
  Pointwise-has-lubs P-lub k .lub a = P-lub a (λ i → k i a) .lub
  Pointwise-has-lubs P-lub k .has-lub .fam≤lub i a =
    P-lub a (λ j → k j a) .Lub.fam≤lub i
  Pointwise-has-lubs P-lub k .has-lub .least ub k≤ub a =
    P-lub a (λ i → k i a) .Lub.least (ub a) (λ i → k≤ub i a)
```

<!--
```agda
  open is-meet-semilattice

  Pointwise-is-meet-slat
    : (∀ a → is-meet-semilattice (P a))
    → is-meet-semilattice (Pointwise A P)
  Pointwise-is-meet-slat meet-slat .has-meets x y =
    Pointwise-has-meets (λ a → meet-slat a .has-meets) x y
  Pointwise-is-meet-slat meet-slat .has-top =
    Pointwise-has-top (λ a → meet-slat a .has-top)

  open is-join-semilattice

  Pointwise-is-join-slat
    : (∀ a → is-join-semilattice (P a))
    → is-join-semilattice (Pointwise A P)
  Pointwise-is-join-slat join-slat .has-joins x y =
    Pointwise-has-joins (λ a → join-slat a .has-joins) x y
  Pointwise-is-join-slat join-slat .has-bottom =
    Pointwise-has-bot (λ a → join-slat a .has-bottom)

Subsets-is-meet-slat : ∀ {ℓ} {A : Type ℓ} → is-meet-semilattice (Subsets A)
Subsets-is-meet-slat = Pointwise-is-meet-slat (λ _ → Props-is-meet-slat)

Subsets-is-join-slat : ∀ {ℓ} {A : Type ℓ} → is-join-semilattice (Subsets A)
Subsets-is-join-slat = Pointwise-is-join-slat (λ _ → Props-is-join-slat)
```
-->

Every subset is a least upper bound of singleton sets.

```agda
subset-singleton-lub
  : ∀ {ℓ} {A : Type ℓ} (P : A → Ω)
  → is-lub (Subsets A) {I = ∫ₚ P} (singleton ⊙ fst) P
subset-singleton-lub P .is-lub.fam≤lub (x , x∈P) y □x=y =
  □-rec! (λ x=y → subst (_∈ P) x=y x∈P) □x=y
subset-singleton-lub P .is-lub.least ub sing≤ub x x∈P =
  sing≤ub (x , x∈P) x (inc refl)
```
