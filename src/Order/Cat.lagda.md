<!--
```agda
open import Cat.Instances.StrictCat
open import Cat.Instances.Functor
open import Cat.Prelude

open import Order.Base

import Cat.Reasoning

import Order.Reasoning

open Precategory
open Poset
```
-->

```agda
module Order.Cat where
```

# Posets as categories {defines="posets-as-categories"}

We have already remarked a [[poset]] is a special kind of [[category]]: a
*thin* [[univalent category]], i.e. one that has propositional $\hom$ sets.

```agda
is-thin : ∀ {ℓ ℓ'} → Precategory ℓ ℓ' → Type (ℓ ⊔ ℓ')
is-thin C = ∀ x y → is-prop (C .Hom x y)
```

This module actually formalises that connection by constructing a
[[fully faithful functor]] from the category of posets into the
[[category of strict categories]]. The construction of a category from a
poset is entirely unsurprising, but it is lengthy, thus ending up in
this module.

```agda
poset→category : ∀ {ℓ ℓ'} → Poset ℓ ℓ' → Precategory ℓ ℓ'
poset→category P = cat module poset-to-category where
  module P = Poset P

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

poset→thin : ∀ {ℓ ℓ'} (P : Poset ℓ ℓ') → is-thin (poset→category P)
poset→thin P _ _ = P.≤-thin where module P = Poset P

poset→univalent : ∀ {ℓ ℓ'} (P : Poset ℓ ℓ') → is-category (poset→category P)
poset→univalent P = set-identity-system (λ _ _ → ≅-is-prop P.≤-thin)
  λ is → P.≤-antisym (is .to) (is .from)
  where
    module P = Poset P
    open Cat.Reasoning (poset→category P)
```

Our functor into $\strcat$ is similarly easy to describe: Monotonicity
of a map _is_ functoriality when preservation of composites is
automatic.

```agda
open Functor

monotone→functor
  : ∀ {o ℓ o' ℓ'} {P : Poset o ℓ} {Q : Poset o' ℓ'}
  → Monotone P Q → Functor (poset→category P) (poset→category Q)
monotone→functor f .F₀ = f .hom
monotone→functor f .F₁ = f .pres-≤
monotone→functor f .F-id = prop!
monotone→functor f .F-∘ _ _ = prop!

Posets↪Strict-cats : ∀ {ℓ ℓ'} → Functor (Posets ℓ ℓ') (Strict-cats ℓ ℓ')
Posets↪Strict-cats .F₀ P = poset→category P , Poset.Ob-is-set P
Posets↪Strict-cats .F₁ f = monotone→functor f
Posets↪Strict-cats .F-id    = Functor-path (λ _ → refl) λ _ → refl
Posets↪Strict-cats .F-∘ f g = Functor-path (λ _ → refl) λ _ → refl
```

More generally, to give a functor into a thin category, it suffices to give the
action on objects and morphisms: the laws hold automatically.

```agda
module
  _ {oc od ℓc ℓd} {C : Precategory oc ℓc} {D : Precategory od ℓd}
    (D-thin : is-thin D)
  where

  thin-functor
    : (f : C .Ob → D .Ob)
    → (f₁ : ∀ {x y} → C .Hom x y → D .Hom (f x) (f y))
    → Functor C D
  thin-functor f f₁ .F₀ = f
  thin-functor f f₁ .F₁ = f₁
  thin-functor f f₁ .F-id = D-thin _ _ _ _
  thin-functor f f₁ .F-∘ _ _ = D-thin _ _ _ _
```

## Thin categories as posets

We can go in the other direction as well: a thin univalent category
gives rise to a poset with the same set of objects and $a \leq b$ if
and only if there is a morphism $a \to b$.

```agda
thin→poset
  : ∀ {ℓ ℓ'} (C : Precategory ℓ ℓ')
  → is-thin C
  → is-category C
  → Poset ℓ ℓ'
thin→poset C thin cat = pos where
  module C = Cat.Reasoning C

  pos : Poset _ _
  pos .Ob = C.Ob
  pos ._≤_ = C.Hom
  pos .≤-thin = thin _ _
  pos .≤-refl = C.id
  pos .≤-trans f g = g C.∘ f
  pos .≤-antisym f f⁻¹ = cat .to-path $
    C.make-iso f f⁻¹ (thin _ _ _ _) (thin _ _ _ _)
```
