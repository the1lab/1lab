```agda
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Reasoning as CR

module Cat.Displayed.Total {o ℓ o′ ℓ′} {B : Precategory o ℓ}
                        (E : Displayed B o′ ℓ′) where

open Displayed E
open CR B
```

# The Total Category of a Displayed Category

So far, we've been thinking of displayed categories as "categories of
structures" over some base category. However, it's often useful to
consider a more "bundled up" notion of structure, where the carrier and
the structure are considered as a singular object. For instance, if we
consider the case of algebraic structures, we often want to think about
"a monoid" as a singular thing, as opposed to structure imposed atop
some set.

Constructing the total category does exactly this. The objects
are pairs of an object from the base, an object from the displayed
category that lives over it.

Note that we use a sigma type here instead of a record for technical
reasons: this makes it simpler to work with algebraic structures.

```agda
Total : Type (o ⊔ o′)
Total = Σ[ Carrier ∈ Ob ] Ob[ Carrier ]
```

The situation is similar for morphisms: we bundle up a morphism from the
base category along with a morphism that lives above it.

```agda

record TotalHom (X Y : Total) : Type (ℓ ⊔ ℓ′) where
  constructor total-hom
  field
    hom       : Hom (X .fst) (Y .fst)
    preserves : Hom[ hom ] (X .snd) (Y .snd)

open TotalHom
```

As is tradition, we need to prove some silly lemmas showing that
the bundled morphisms form an hset, and another characterizing
the paths between morphisms.

```agda
total-hom-set : ∀ (X Y : Total) → isSet (TotalHom X Y)
total-hom-set X Y =
  isHLevel-retract 2 TotalHom-Refold TotalHom-Unfold (λ x → refl) TotalHom′-isSet
  where
    TotalHom′ : Type _
    TotalHom′ = Σ[ hom ∈ Hom (X .fst) (Y .fst) ]
                Hom[ hom ] (X .snd) (Y .snd)

    TotalHom-Refold : TotalHom′ → TotalHom X Y 
    TotalHom-Refold (h , p) = total-hom h p

    TotalHom-Unfold : TotalHom X Y → TotalHom′
    TotalHom-Unfold t = t .hom , t .preserves

    TotalHom′-isSet : isSet TotalHom′
    TotalHom′-isSet =
      isHLevelΣ 2 (Hom-set _ _)
                  λ f → Hom[ f ]-set _ _

total-hom-path : ∀ {X Y : Total} {f g : TotalHom X Y}
                 → (p : f .hom ≡ g .hom) → f .preserves ≡[ p ] g .preserves → f ≡ g
total-hom-path p p′ i .hom = p i
total-hom-path {f = f} {g = g} p p′ i .preserves = p′ i
```

With all that in place, we can construct the total category!

```agda
∫ : Precategory (o ⊔ o′) (ℓ ⊔ ℓ′)
∫ .Precategory.Ob = Total
∫ .Precategory.Hom = TotalHom
∫ .Precategory.Hom-set = total-hom-set
∫ .Precategory.id = total-hom id id′
∫ .Precategory._∘_ f g = total-hom (f .hom ∘ g .hom) (f .preserves ∘′ g .preserves)
∫ .Precategory.idr _ = total-hom-path (idr _) (idr′ _)
∫ .Precategory.idl _ = total-hom-path (idl _) (idl′ _)
∫ .Precategory.assoc _ _ _ = total-hom-path (assoc _ _ _) (assoc′ _ _ _)
```
