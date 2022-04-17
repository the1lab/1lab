```agda
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Reasoning as CR

module Cat.Displayed.Instances.Slice {o ℓ} (B : Precategory o ℓ) where

open Displayed
open CR B
```

# Slices as a Displayed Category

There is a canonical way of viewing any category as displayed over
itself. Recall that the best way to think about displayed categories is
adding extra structure over each of the objects of the base. Here, we
only really have one natural choice of extra structure for objects:
morphisms into that object!

```agda
record Slice (x : Ob) : Type (o ⊔ ℓ) where
  constructor slice
  field
    over  : Ob
    index : Hom over x

open Slice
```

As a point of intuition: the name `Slice` should evoke the feeling of
"slicing up" `over`. If we restrict ourselves to Set, we can view a map
`over → x` as a partition of `over` into `x` different fibres. In other
words, this provides an x-indexed collection of sets. This view of
viewing slices as means of indexing is a very fruitful one, and should
be something that you keep in the back of your head.

Now, the morphisms:

```agda
record Slice-hom {x y} (f : Hom x y)
                (px : Slice x) (py : Slice y) : Type (o ⊔ ℓ) where
  constructor slice-hom
  private
    module px = Slice px
    module py = Slice py
  field
    to     : Hom px.over py.over
    commute : f ∘ px.index ≡ py.index ∘ to

open Slice-hom
```

<!--
```agda
private unquoteDecl eqv = declare-record-iso eqv (quote Slice-hom)
```
-->

Going back to our intuition of "slices as a means of indexing", a
morphism of slices performs a sort of reindexing operation. The morphism
in the base performs our re-indexing, and then we ensure that we have
some morphism between the indexed collections that preserves indexing,
relative to the re-indexing operation.

## Slice Lemmas

Before we show this thing is a displayed category, we need to prove some
lemmas.  These are extremely unenlightening, so the reader should feel
free to skip these (and probably ought to!).

```agda
module _ {x y} {f g : Hom x y} {px : Slice x} {py : Slice y}
         {f′ : Slice-hom f px py} {g′ : Slice-hom g px py} where
```

Paths of slice morphisms are determined by paths between the base
morphisms, and paths between the "upper" morphisms.

```agda
  Slice-pathp : (p : f ≡ g) → (f′ .to ≡ g′ .to) → PathP (λ i → Slice-hom (p i) px py) f′ g′
  Slice-pathp p p′ i .to = p′ i
  Slice-pathp p p′ i .commute =
    is-prop→pathp
      (λ i → Hom-set _ _ (p i ∘ px .index) (py .index ∘ (p′ i)))
      (f′ .commute)
      (g′ .commute)
      i
```

```agda
module _ {x y} (f : Hom x y) (px : Slice x) (py : Slice y) where
  Slice-is-set : is-set (Slice-hom f px py)
  Slice-is-set = is-hlevel≃ 2 (Iso→Equiv eqv e⁻¹) (hlevel 2)
    where open HLevel-instance
```

## Pulling it all together

Now that we have all the ingredients, the proof that this is all a
displayed category follows rather easily. It's useful to reinforce what
we've actually done here though!  We can think of morphisms into some
object `x` as "structures on `x`", and then commuting squares as
"structures over morphisms".

```agda
Slices : Displayed B (o ⊔ ℓ) (o ⊔ ℓ)
Slices .Ob[_] = Slice
Slices .Hom[_] = Slice-hom
Slices .Hom[_]-set = Slice-is-set
Slices .id′ = slice-hom id id-comm-sym
Slices ._∘′_ {x = x} {y = y} {z = z} {f = f} {g = g} px py =
  slice-hom (px .to ∘ py .to) $
    (f ∘ g) ∘ x .index          ≡⟨ pullr (py .commute) ⟩
    f ∘ (index y ∘ py .to)      ≡⟨ extendl (px .commute) ⟩
    z .index ∘ (px .to ∘ py .to) ∎
Slices .idr′ {f = f} f′ = Slice-pathp (idr f) (idr (f′ .to))
Slices .idl′ {f = f} f′ = Slice-pathp (idl f) (idl (f′ .to))
Slices .assoc′ {f = f} {g = g} {h = h} f′ g′ h′ =
  Slice-pathp (assoc f g h) (assoc (f′ .to) (g′ .to) (h′ .to))
```

