<!--
```agda
open import Cat.Prelude

open import Order.Instances.Pointwise
open import Order.Diagram.Glb
open import Order.Diagram.Lub
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
module
  _ {ℓₒ ℓᵣ ℓᵢ} {I : Type ℓᵢ} (P : Poset ℓₒ ℓᵣ)
    (f g h : I → ⌞ P ⌟)
  where

  is-meet-pointwise
    : (∀ i → is-meet P (f i) (g i) (h i))
    → is-meet (Pointwise I P) f g h
  is-meet-pointwise pwise .is-meet.meet≤l i = pwise i .is-meet.meet≤l
  is-meet-pointwise pwise .is-meet.meet≤r i = pwise i .is-meet.meet≤r
  is-meet-pointwise pwise .is-meet.greatest lb' lb'<f lb'<g i =
    pwise i .is-meet.greatest (lb' i) (lb'<f i) (lb'<g i)

  is-join-pointwise
    : (∀ i → is-join P (f i) (g i) (h i))
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
  _ {ℓₒ ℓᵣ ℓᵢ ℓⱼ} {I : Type ℓᵢ} {J : Type ℓⱼ}
    (P : Poset ℓₒ ℓᵣ)
    (F : I → J → ⌞ P ⌟)
    (m : J → ⌞ P ⌟)
  where

  is-lub-pointwise
    : (∀ j → is-lub P (λ i → F i j) (m j))
    → is-lub (Pointwise J P) F m
  is-lub-pointwise pwise .is-lub.fam≤lub i j = pwise j .is-lub.fam≤lub i
  is-lub-pointwise pwise .is-lub.least ub' fi<ub' j =
    pwise j .is-lub.least (ub' j) λ i → fi<ub' i j

  is-glb-pointwise
    : (∀ j → is-glb P (λ i → F i j) (m j))
    → is-glb (Pointwise J P) F m
  is-glb-pointwise pwise .is-glb.glb≤fam i j = pwise j .is-glb.glb≤fam i
  is-glb-pointwise pwise .is-glb.greatest ub' fi<ub' j =
    pwise j .is-glb.greatest (ub' j) λ i → fi<ub' i j
```
