<!--
```agda
open import Cat.Prelude

open import Data.Power hiding (_∩_ ; _∪_)

open import Order.Instances.Pointwise
open import Order.Semilattice.Join
open import Order.Semilattice.Meet
open import Order.Instances.Props
open import Order.Diagram.Bottom
open import Order.Diagram.Join
open import Order.Diagram.Meet
open import Order.Diagram.Glb
open import Order.Diagram.Lub
open import Order.Diagram.Top
open import Order.Base
```
-->

```agda
module Order.Instances.Pointwise.Diagrams where
```

# Pointwise joins and meets

This module establishes that joins and meets are a _pointwise_
construction, in the following sense: Suppose that $f_i$, $g_i$, and
$h_i$ are families of elements $I \to P$ with $(P, \le)$ a poset, such
that, for all $i$, we have $h_i = f_i \land g_i$^[In the code, this
means that `is-meet`{.Agda} holds, but we will abuse this "functional"
notation for clarity.], then $h = f \land g$ when $I \to P$ is given the
[pointwise ordering].

[pointwise ordering]: Order.Instances.Pointwise.html

```agda
module _ {ℓₒ ℓᵣ ℓᵢ} {I : Type ℓᵢ} {P : I → Poset ℓₒ ℓᵣ} where
  private module P {i} = Poset (P i)

  is-top-pointwise
    : ∀ {t} (pt : ∀ i → is-top (P i) (t i))
    → is-top (Pointwise I P) t
  is-top-pointwise pt fam i = pt i (fam i)

  has-top-pointwise
    : (∀ i → Top (P i))
    → Top (Pointwise I P)
  has-top-pointwise pt .Top.top i = pt i .Top.top
  has-top-pointwise pt .Top.has-top = is-top-pointwise λ i → pt i .Top.has-top

  is-bottom-pointwise
    : ∀ {b} (pt : ∀ i → is-bottom (P i) (b i))
    → is-bottom (Pointwise I P) b
  is-bottom-pointwise pb fam i = pb i (fam i)

  has-bottom-pointwise
    : (∀ i → Bottom (P i))
    → Bottom (Pointwise I P)
  has-bottom-pointwise pt .Bottom.bot i = pt i .Bottom.bot
  has-bottom-pointwise pt .Bottom.has-bottom =
    is-bottom-pointwise λ i → pt i .Bottom.has-bottom

  is-meet-pointwise
    : ∀ {f g h} (pms : ∀ i → is-meet (P i) (f i) (g i) (h i))
    → is-meet (Pointwise I P) f g h
  is-meet-pointwise pwise .is-meet.meet≤l i = pwise i .is-meet.meet≤l
  is-meet-pointwise pwise .is-meet.meet≤r i = pwise i .is-meet.meet≤r
  is-meet-pointwise pwise .is-meet.greatest lb' lb'<f lb'<g i =
    pwise i .is-meet.greatest (lb' i) (lb'<f i) (lb'<g i)

  is-join-pointwise
    : ∀ {f g h} (pjs : ∀ i → is-join (P i) (f i) (g i) (h i))
    → is-join (Pointwise I P) f g h
  is-join-pointwise pwise .is-join.l≤join i = pwise i .is-join.l≤join
  is-join-pointwise pwise .is-join.r≤join i = pwise i .is-join.r≤join
  is-join-pointwise pwise .is-join.least lb' lb'<f lb'<g i =
    pwise i .is-join.least (lb' i) (lb'<f i) (lb'<g i)
```

With a couple more variables, we see that the results above are a
special case of both arbitrary lubs and glbs being pointwise:

```agda
module
  _ {ℓₒ ℓᵣ ℓᵢ ℓⱼ} {I : Type ℓᵢ} {J : Type ℓⱼ} {P : J → Poset ℓₒ ℓᵣ}
    (F : I → (j : J) → ⌞ P j ⌟)
    (m : (j : J) → ⌞ P j ⌟)
  where

  is-lub-pointwise
    : (∀ j → is-lub (P j) (λ i → F i j) (m j))
    → is-lub (Pointwise J P) F m
  is-lub-pointwise pwise .is-lub.fam≤lub i j = pwise j .is-lub.fam≤lub i
  is-lub-pointwise pwise .is-lub.least ub' fi<ub' j =
    pwise j .is-lub.least (ub' j) λ i → fi<ub' i j

  is-glb-pointwise
    : (∀ j → is-glb (P j) (λ i → F i j) (m j))
    → is-glb (Pointwise J P) F m
  is-glb-pointwise pwise .is-glb.glb≤fam i j = pwise j .is-glb.glb≤fam i
  is-glb-pointwise pwise .is-glb.greatest ub' fi<ub' j =
    pwise j .is-glb.greatest (ub' j) λ i → fi<ub' i j
```

<!--
```agda
module _ {ℓₒ ℓᵣ ℓᵢ} {I : Type ℓᵢ} {P : I → Poset ℓₒ ℓᵣ} where
  open is-meet-semilattice

  Pointwise-is-meet-slat
    : (∀ a → is-meet-semilattice (P a))
    → is-meet-semilattice (Pointwise I P)
  Pointwise-is-meet-slat meets ._∩_ x y i = meets i ._∩_ (x i) (y i)
  Pointwise-is-meet-slat meets .∩-meets x y = is-meet-pointwise λ a →
    meets a .∩-meets (x a) (y a)
  Pointwise-is-meet-slat meets .has-top = has-top-pointwise λ a →
    meets a .has-top

  open is-join-semilattice

  Pointwise-is-join-slat
    : (∀ a → is-join-semilattice (P a))
    → is-join-semilattice (Pointwise I P)
  Pointwise-is-join-slat joins ._∪_ x y i = joins i ._∪_ (x i) (y i)
  Pointwise-is-join-slat joins .∪-joins x y = is-join-pointwise λ a →
    joins a .∪-joins (x a) (y a)
  Pointwise-is-join-slat joins .has-bottom = has-bottom-pointwise λ a →
    joins a .has-bottom

Subsets-is-meet-slat : ∀ {ℓ} {A : Type ℓ} → is-meet-semilattice (Subsets A)
Subsets-is-meet-slat = Pointwise-is-meet-slat λ _ → Props-is-meet-slat

Subsets-is-join-slat : ∀ {ℓ} {A : Type ℓ} → is-join-semilattice (Subsets A)
Subsets-is-join-slat = Pointwise-is-join-slat λ _ → Props-is-join-slat
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
