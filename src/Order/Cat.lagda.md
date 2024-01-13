<!--
```agda
open import Cat.Instances.StrictCat
open import Cat.Instances.Functor
open import Cat.Prelude

open import Order.Base

import Order.Reasoning
```
-->

```agda
module Order.Cat where
```

# Posets as categories

We have already remarked a [[poset]] is a special kind of [[category]].
This module actually formalises that connection by constructing a
[[fully faithful functor]] from the category of posets into the
[[category of strict categories]]. The construction of a category from a
poset is entirely unsurprising, but it is lengthy, thus ending up in
this module.

```agda
poset→category : ∀ {ℓ ℓ'} → Posets.Ob → Precategory ℓ ℓ'
poset→category P = cat module poset-to-category where
  module P = Poset P
  open Precategory

  cat : Precategory _ _
  cat .Ob      = P.Ob
  cat .Hom     = P._≤_
  cat .id      = P.≤-refl
  cat ._∘_ f g = P.≤-trans g f
  cat .idr f   = P.≤-thin _ _
  cat .idl f   = P.≤-thin _ _
  cat .assoc f g h = P.≤-thin _ _
  cat .Hom-set x y = is-prop→is-set P.≤-thin

{-# DISPLAY poset-to-category.cat P = poset→category P #-}
```

Our functor into $\strcat$ is similarly easy to describe: Monotonicity
of a map _is_ functoriality when preservation of composites is
automatic.

```agda
open Functor
Posets↪Strict-cats : ∀ {ℓ ℓ'} → Functor (Posets ℓ ℓ') (Strict-cats ℓ ℓ')
Posets↪Strict-cats .F₀ P = poset→category P , Poset.Ob-is-set P

Posets↪Strict-cats .F₁ f .F₀ = f .hom
Posets↪Strict-cats .F₁ f .F₁ = f .pres-≤
Posets↪Strict-cats .F₁ {y = y} f .F-id    = Poset.≤-thin y _ _
Posets↪Strict-cats .F₁ {y = y} f .F-∘ g h = Poset.≤-thin y _ _

Posets↪Strict-cats .F-id    = Functor-path (λ _ → refl) λ _ → refl
Posets↪Strict-cats .F-∘ f g = Functor-path (λ _ → refl) λ _ → refl
```
