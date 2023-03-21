```agda
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Morphism as DM
import Cat.Reasoning as CR

module Cat.Displayed.Total
  {o ℓ o′ ℓ′} {B : Precategory o ℓ} (E : Displayed B o′ ℓ′) where

open Displayed E
open DM E
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
record Total-hom (X Y : Total) : Type (ℓ ⊔ ℓ′) where
  constructor total-hom
  field
    hom       : Hom (X .fst) (Y .fst)
    preserves : Hom[ hom ] (X .snd) (Y .snd)

open Total-hom
```

<!--
```agda
private unquoteDecl eqv = declare-record-iso eqv (quote Total-hom)
```
-->

As is tradition, we need to prove some silly lemmas showing that
the bundled morphisms form an hset, and another characterizing
the paths between morphisms.

```agda
total-hom-is-set : ∀ (X Y : Total) → is-set (Total-hom X Y)
total-hom-is-set X Y = Iso→is-hlevel 2 eqv $
  Σ-is-hlevel 2 (hlevel 2) (λ a → Hom[ _ ]-set _ _)

total-hom-path : ∀ {X Y : Total} {f g : Total-hom X Y}
               → (p : f .hom ≡ g .hom) → f .preserves ≡[ p ] g .preserves → f ≡ g
total-hom-path p p′ i .hom = p i
total-hom-path {f = f} {g = g} p p′ i .preserves = p′ i
```

<!--
```agda
total-hom-pathp
  : ∀ {X X′ Y Y′ : Total} {f : Total-hom X Y} {g : Total-hom X′ Y′}
  → (p : X ≡ X′) (q : Y ≡ Y′)
  → (r : PathP (λ z → Hom (p z .fst) (q z .fst)) (f .hom) (g .hom))
  → PathP (λ z → Hom[ r z ] (p z .snd) (q z .snd)) (f .preserves) (g .preserves)
  → PathP (λ i → Total-hom (p i) (q i)) f g
total-hom-pathp p q r s i .hom = r i
total-hom-pathp p q r s i .preserves = s i
```
-->

With all that in place, we can construct the total category!

```agda
∫ : Precategory (o ⊔ o′) (ℓ ⊔ ℓ′)
∫ .Precategory.Ob = Total
∫ .Precategory.Hom = Total-hom
∫ .Precategory.Hom-set = total-hom-is-set
∫ .Precategory.id .hom = id
∫ .Precategory.id .preserves = id′
∫ .Precategory._∘_ f g .hom = f .hom ∘ g .hom
∫ .Precategory._∘_ f g .preserves = f .preserves ∘′ g .preserves
∫ .Precategory.idr _ = total-hom-path (idr _) (idr′ _)
∫ .Precategory.idl _ = total-hom-path (idl _) (idl′ _)
∫ .Precategory.assoc _ _ _ = total-hom-path (assoc _ _ _) (assoc′ _ _ _)
```

<!--
```agda
πᶠ : Functor ∫ B
πᶠ .Functor.F₀ = fst
πᶠ .Functor.F₁ = Total-hom.hom
πᶠ .Functor.F-id = refl
πᶠ .Functor.F-∘ f g = refl
```
-->

## Morphisms in the total category

Isomorphisms in the total category of $E$ consist of pairs of
isomorphisms in $B$ and $E$.

```agda
private module ∫E = CR ∫

total-iso→iso : ∀ {x y} → x ∫E.≅ y → x .fst ≅ y .fst
total-iso→iso f = make-iso
    (∫E._≅_.to f .hom)
    (∫E._≅_.from f .hom)
    (ap hom $ ∫E._≅_.invl f)
    (ap hom $ ∫E._≅_.invr f)

total-iso→iso[] : ∀ {x y} → (f : x ∫E.≅ y) → x .snd ≅[ total-iso→iso f ] y .snd
total-iso→iso[] f = make-iso[ total-iso→iso f ]
    (∫E._≅_.to f .preserves)
    (∫E._≅_.from f .preserves)
    (ap preserves $ ∫E._≅_.invl f)
    (ap preserves $ ∫E._≅_.invr f)
```
