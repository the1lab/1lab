---
description: |
  Comma categories as a displayed category.
---
<!--
```agda
open import Cat.Displayed.Cartesian
open import Cat.Instances.Product
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Functor.Reasoning
import Cat.Reasoning
```
-->
```agda
module Cat.Displayed.Instances.Comma where
```

# Comma categories as a two-sided displayed category

We can neatly organize [[comma categories]] $F \downarrow G$
of functors $F : \cA \to \cC, G : \cB \to \cC$ as [[displayed categories]]
over $\cA \times \cB$.

<!--
```agda
module _
  {ao bo co ah bh ch}
  {A : Precategory ao ah}
  {B : Precategory bo bh}
  {C : Precategory co ch}
  (F : Functor A C) (G : Functor B C)
  where
  private
    module A = Precategory A
    module B = Precategory B
    module C = Cat.Reasoning C
    module F = Cat.Functor.Reasoning F
    module G = Cat.Functor.Reasoning G
  open Displayed
```
-->

An object in $F \downarrow G$ over $(a, b)$ is given by a morphism
$\cC(F(a), G(b))$, and a morphism between some $h : \cC(F(a), G(x))$
and $\cC(F(b), G(y))$ over $f : \cA(a, b)$ and $g : \cB(x, y)$ is
a proof that $k \circ F(f) = G(g) \circ h$.

```agda
  _↓_ : Displayed (A ×ᶜ B) ch ch
  _↓_ .Ob[_] (a , b) = C.Hom (F.₀ a) (G.₀ b)
  _↓_ .Hom[_] (f , g) h k = k C.∘ F.₁ f ≡ G.₁ g C.∘ h
```

Identities arise from the fact that $h \circ F(id) = G(id) \circ h$,
and composites are given by pasting squares.

```agda
  _↓_ .id' = C.elimr F.F-id ∙ C.introl G.F-id
  _↓_ ._∘'_ p q = F.popl p ∙ sym (G.shuffler (sym q))
```

<details>
<summary>The type of displayed morphisms is a proposition, so all equations
hold trivially.
</summary>
```agda
  _↓_ .Hom[_]-set _ _ _ = hlevel 2
  _↓_ .idr' _ = prop!
  _↓_ .idl' _ = prop!
  _↓_ .assoc' _ _ _ = prop!
```
</details>

<!--
[TODO: Reed M, 20/08/2024] This is a 2-sided fibration.
-->

## The displayed category of arrows {defines="arrow-category"}

The displayed arrow category $\cC^{\to}$ is the displayed comma category
$Id \downarrow Id$. If we unfold the definition, we will see that the
type of objects of $\cC^{\to}$ over $a, b : \cC$ is just morphisms $\cC(a,b)$,
and the type of displayed morphisms is given by proofs that squares of
morphisms commute.

```agda
module _
  {o ℓ}
  (C : Precategory o ℓ)
  where

  Arrows : Displayed (C ×ᶜ C) ℓ ℓ
  Arrows = Id ↓ Id
```
