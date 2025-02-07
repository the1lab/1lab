<!--
```agda
open import Cat.Instances.Shape.Terminal
open import Cat.Prelude

open import Data.Sum

open Precategory
open Functor
```
-->

```agda
module Cat.Instances.Shape.Join where
```

# Join of categories

The **join** $\cC \star \cD$ of two categories is the category
obtained by "bridging" the disjoint union $\cC \coprod \cD$ with a
_unique_ morphism between each object of $\cC$ and each object of $\cD$.

```agda
module _ {o ℓ o' ℓ'} (C : Precategory o ℓ) (D : Precategory o' ℓ') where
  private
    module C = Precategory C
    module D = Precategory D

  ⋆Ob : Type (o ⊔ o')
  ⋆Ob = C.Ob ⊎ D.Ob

  ⋆Hom : (A B : ⋆Ob) → Type (ℓ ⊔ ℓ')
  ⋆Hom (inl x) (inl y) = Lift ℓ' (C.Hom x y)
  ⋆Hom (inl x) (inr y) = Lift (ℓ ⊔ ℓ') ⊤
  ⋆Hom (inr x) (inl y) = Lift (ℓ ⊔ ℓ') ⊥
  ⋆Hom (inr x) (inr y) = Lift ℓ (D.Hom x y)

  ⋆compose : ∀ {A B C : ⋆Ob} → ⋆Hom B C → ⋆Hom A B → ⋆Hom A C
  ⋆compose {inl x} {inl y} {inl z} (lift f) (lift g) = lift (f C.∘ g)
  ⋆compose {inl x} {inl y} {inr z} (lift f) (lift g) = lift tt
  ⋆compose {inl x} {inr y} {inr z} (lift f) (lift g) = lift tt
  ⋆compose {inr x} {inr y} {inr z} (lift f) (lift g) = lift (f D.∘ g)

  _⋆_ : Precategory _ _
  _⋆_ .Ob = ⋆Ob
  _⋆_ .Hom = ⋆Hom
  _⋆_ .Hom-set x y = iss x y where
    iss : ∀ x y → is-set (⋆Hom x y)
    iss (inl x) (inl y) = hlevel 2
    iss (inl x) (inr y) _ _ p q i j = lift tt
    iss (inr x) (inr y) = hlevel 2
  _⋆_ .id {inl x} = lift C.id
  _⋆_ .id {inr x} = lift D.id
  _⋆_ ._∘_ = ⋆compose
  _⋆_ .idr {inl x} {inl y} (lift f) = ap lift (C.idr f)
  _⋆_ .idr {inl x} {inr y} (lift f) = refl
  _⋆_ .idr {inr x} {inr y} (lift f) = ap lift (D.idr f)
  _⋆_ .idl {inl x} {inl y} (lift f) = ap lift (C.idl f)
  _⋆_ .idl {inl x} {inr y} (lift f) = refl
  _⋆_ .idl {inr x} {inr y} (lift f) = ap lift (D.idl f)
  _⋆_ .assoc {inl w} {inl x} {inl y} {inl z} (lift f) (lift g) (lift h) = ap lift (C.assoc f g h)
  _⋆_ .assoc {inl w} {inl x} {inl y} {inr z} (lift f) (lift g) (lift h) = refl
  _⋆_ .assoc {inl w} {inl x} {inr y} {inr z} (lift f) (lift g) (lift h) = refl
  _⋆_ .assoc {inl w} {inr x} {inr y} {inr z} (lift f) (lift g) (lift h) = refl
  _⋆_ .assoc {inr w} {inr x} {inr y} {inr z} (lift f) (lift g) (lift h) = ap lift (D.assoc f g h)

module _ {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'} where
  ⋆-inl : Functor C (C ⋆ D)
  ⋆-inl .F₀ = inl
  ⋆-inl .F₁ = lift
  ⋆-inl .F-id = refl
  ⋆-inl .F-∘ f g = refl

  ⋆-inr : Functor D (C ⋆ D)
  ⋆-inr .F₀ = inr
  ⋆-inr .F₁ = lift
  ⋆-inr .F-id = refl
  ⋆-inr .F-∘ f g = refl

module _ {oc ℓc od ℓd oe ℓe}
  {C : Precategory oc ℓc} {D : Precategory od ℓd} {E : Precategory oe ℓe}
  where

  ⋆-mapl : Functor C D → Functor (C ⋆ E) (D ⋆ E)
  ⋆-mapl F .F₀ = ⊎-mapl (F .F₀)
  ⋆-mapl F .F₁ {inl x} {inl y} (lift f) = lift (F .F₁ f)
  ⋆-mapl F .F₁ {inl x} {inr y} _ = _
  ⋆-mapl F .F₁ {inr x} {inr y} (lift f) = lift f
  ⋆-mapl F .F-id {inl x} = ap lift (F .F-id)
  ⋆-mapl F .F-id {inr x} = refl
  ⋆-mapl F .F-∘ {inl x} {inl y} {inl z} f g = ap lift (F .F-∘ _ _)
  ⋆-mapl F .F-∘ {inl x} {inl y} {inr z} f g = refl
  ⋆-mapl F .F-∘ {inl x} {inr y} {inr z} f g = refl
  ⋆-mapl F .F-∘ {inr x} {inr y} {inr z} f g = refl

  ⋆-mapr : Functor D E → Functor (C ⋆ D) (C ⋆ E)
  ⋆-mapr F .F₀ = ⊎-mapr (F .F₀)
  ⋆-mapr F .F₁ {inl x} {inl y} (lift f) = lift f
  ⋆-mapr F .F₁ {inl x} {inr y} _ = _
  ⋆-mapr F .F₁ {inr x} {inr y} (lift f) = lift (F .F₁ f)
  ⋆-mapr F .F-id {inl x} = refl
  ⋆-mapr F .F-id {inr x} = ap lift (F .F-id)
  ⋆-mapr F .F-∘ {inl x} {inl y} {inl z} f g = refl
  ⋆-mapr F .F-∘ {inl x} {inl y} {inr z} f g = refl
  ⋆-mapr F .F-∘ {inl x} {inr y} {inr z} f g = refl
  ⋆-mapr F .F-∘ {inr x} {inr y} {inr z} f g = ap lift (F .F-∘ _ _)
```

## Adjoining a terminal object {defines="adjoined-terminal-object"}

Given a category $\cJ$, we can freely adjoin a [[terminal object]] to $\cJ$ by taking
the join $\cJ^\triangleright = \cJ \star \top$ with the [[terminal category]].

```agda
_▹ : ∀ {o ℓ} → Precategory o ℓ → Precategory o ℓ
J ▹ = J ⋆ ⊤Cat

module _ {o ℓ} {J : Precategory o ℓ} where
  ▹-in : Functor J (J ▹)
  ▹-in = ⋆-inl

  ▹-join : Functor (J ▹ ▹) (J ▹)
  ▹-join .F₀ (inl (inl j)) = inl j
  ▹-join .F₀ (inl (inr _)) = inr _
  ▹-join .F₀ (inr _) = inr _
  ▹-join .F₁ {inl (inl x)} {inl (inl y)} (lift f) = f
  ▹-join .F₁ {inl (inl x)} {inl (inr y)} f = _
  ▹-join .F₁ {inl (inl x)} {inr y} f = _
  ▹-join .F₁ {inl (inr x)} {inl (inr y)} f = _
  ▹-join .F₁ {inl (inr x)} {inr y} f = _
  ▹-join .F₁ {inr x} {inr y} f = _
  ▹-join .F-id {inl (inl x)} = refl
  ▹-join .F-id {inl (inr x)} = refl
  ▹-join .F-id {inr x} = refl
  ▹-join .F-∘ {inl (inl x)} {inl (inl y)} {inl (inl z)} f g = refl
  ▹-join .F-∘ {inl (inl x)} {inl (inl y)} {inl (inr z)} f g = refl
  ▹-join .F-∘ {inl (inl x)} {inl (inl y)} {inr z} f g = refl
  ▹-join .F-∘ {inl (inl x)} {inl (inr y)} {inl (inr z)} f g = refl
  ▹-join .F-∘ {inl (inl x)} {inl (inr y)} {inr z} f g = refl
  ▹-join .F-∘ {inl (inl x)} {inr y} {inr z} f g = refl
  ▹-join .F-∘ {inl (inr x)} {inl (inr y)} {inl (inr z)} f g = refl
  ▹-join .F-∘ {inl (inr x)} {inl (inr y)} {inr z} f g = refl
  ▹-join .F-∘ {inl (inr x)} {inr y} {inr z} f g = refl
  ▹-join .F-∘ {inr x} {inr y} {inr z} f g = refl
```
