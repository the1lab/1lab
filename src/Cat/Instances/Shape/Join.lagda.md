<!--
```agda
open import Cat.Prelude

open import Data.Sum
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
    open Precategory

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
    iss (inl x) (inl y) = hlevel!
    iss (inl x) (inr y) _ _ p q i j = lift tt
    iss (inr x) (inr y) = hlevel!
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
```
