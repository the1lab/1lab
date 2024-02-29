<!--
```agda
open import Cat.Groupoid
open import Cat.Morphism
open import Cat.Prelude

open import Order.Cat

open Precategory
open Functor
```
-->

```agda
module Cat.Instances.Congruence where
```

# Congruences as groupoids {defines="congruences-as-groupoids"}

Just as [[posets]] can be seen [[as *thin* categories|posets as categories]],
[[congruences]] can be seen as thin *[[groupoids|pregroupoid]]*: categories
in which every morphism is invertible and any two parallel morphisms are equal.

```agda
module _ {ℓ ℓ'} {A : Type ℓ} (R : Congruence A ℓ') where
  open Congruence R

  congruence→category : Precategory _ _
  congruence→category .Ob = A
  congruence→category .Hom = _∼_
  congruence→category .Hom-set _ _ = is-prop→is-set (has-is-prop _ _)
  congruence→category .id = reflᶜ
  congruence→category ._∘_ f g = g ∙ᶜ f
  congruence→category .idr _ = has-is-prop _ _ _ _
  congruence→category .idl _ = has-is-prop _ _ _ _
  congruence→category .assoc _ _ _ = has-is-prop _ _ _ _

  congruence→thin : is-thin congruence→category
  congruence→thin = has-is-prop

  congruence→groupoid : is-pregroupoid congruence→category
  congruence→groupoid f = make-invertible _ (symᶜ f)
    (has-is-prop _ _ _ _) (has-is-prop _ _ _ _)
```

To give a [[functor]] into a congruence *qua* category, it suffices to give a
function into $A$ such that the source and target of every morphism have
related images.

```agda
  congruence-functor
    : ∀ {o ℓ} {C : Precategory o ℓ}
    → (f : C .Ob → A)
    → (∀ {x y} → C .Hom x y → f x ∼ f y)
    → Functor C congruence→category
  congruence-functor = thin-functor congruence→thin
```
