<!--
```agda
open import Cat.Displayed.Instances.DisplayedFamilies
open import Cat.Instances.Shape.Interval using (Arr)
open import Cat.Displayed.Composition
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Adjoint
open import Cat.Displayed.Functor
open import Cat.Instances.Slice
open import Cat.Displayed.Base
open import Cat.Prelude
```
-->

```agda
module Cat.Displayed.InternalSum
  {o ℓ o′ ℓ′} {B : Precategory o ℓ} (E : Displayed B o′ ℓ′)  where

open Precategory B
open Displayed E

open import Cat.Displayed.Instances.Slice B
open import Cat.Displayed.Total
```

# Internal Sums

As has been noted before, fibrations are an excellent setting for studying
logical and type-theoretic phenomena. Internal sums are an example of this;
serving as the categorical analog of Sigma types.

To begin our definition, we first need a notion of a family internal to
a fibration: this is handled by the [fibration of displayed families].
We say that a fibration $\cE$ has **internal sums** if the constant
displayed family functor has a [fibred left adjoint].

[fibration of displayed families]: Cat.Displayed.Instances.DisplayedFamilies.html
[fibred left adjoint]: Cat.Displayed.Adjoint.html

```agda
record Internal-sum : Type (o ⊔ ℓ ⊔ o′ ⊔ ℓ′)
  where
  no-eta-equality
  field
    ∐ : Vertical-fibred-functor (Disp-family E) E
    adjunction : ∐ ⊣f↓ ConstDispFamVf E
```
