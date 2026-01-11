<!--
```agda
open import Cat.Displayed.Instances.DisplayedFamilies
open import Cat.Displayed.Functor.Adjoint
open import Cat.Displayed.Instances.Slice
open import Cat.Displayed.Functor
open import Cat.Displayed.Base
open import Cat.Prelude
```
-->

```agda
module Cat.Displayed.InternalSum
  {o ℓ o' ℓ'} {B : Precategory o ℓ} (E : Displayed B o' ℓ')  where
```

<!--
```agda
open Precategory B
```
-->

# Internal sums

As has been noted before, fibrations are an excellent setting for studying
logical and type-theoretic phenomena. Internal sums are an example of this;
serving as the categorical analog of Sigma types.

To begin our definition, we first need a notion of a family internal to
a fibration: this is handled by the [fibration of displayed families].
We say that a fibration $\cE$ has **internal sums** if the constant
displayed family functor has a [[fibred left adjoint]].

[fibration of displayed families]: Cat.Displayed.Instances.DisplayedFamilies.html

```agda
record Internal-sum : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ')
  where
  no-eta-equality
  field
    ∐F : Vertical-functor (Disp-family E) E
    ∐F-fibred : is-fibred-functor ∐F
    ∐F⊣ConstFam : ∐F ⊣↓ ConstDispFam E
```
