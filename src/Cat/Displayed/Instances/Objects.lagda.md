<!--
```agda
open import Cat.Displayed.Cartesian.Right
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Functor
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Displayed.Instances.Objects
  {o ℓ o' ℓ'} {B : Precategory o ℓ}
  (E : Displayed B o' ℓ')
  where
```

<!--
```agda
open Cat.Reasoning B
open Displayed E
open Cartesian-morphism
open Vertical-fibred-functor
open Vertical-functor
```
-->

# The fibration of objects

Let $\cE \liesover \cB$ be a fibration. Its **fibration of objects** is
the [wide subcategory] spanned by the [[cartesian morphisms]]. The idea
behind the name is that we've kept all the objects in $\cE$, but removed
all the interesting morphisms: all we've kept are the ones that witness
changes-of-base.

[wide subcategory]: Cat.Functor.WideSubcategory.html

```agda
Objects : Displayed B o' (o ⊔ ℓ ⊔ o' ⊔ ℓ')
Objects .Displayed.Ob[_] x = Ob[ x ]
Objects .Displayed.Hom[_] f x' y'   = Cartesian-morphism E f x' y'
Objects .Displayed.Hom[_]-set _ _ _ = Cartesian-morphism-is-set E
Objects .Displayed.id'  = idcart E
Objects .Displayed._∘'_ = _∘cart_ E
Objects .Displayed.idr' _       = Cartesian-morphism-pathp E (idr' _)
Objects .Displayed.idl' _       = Cartesian-morphism-pathp E (idl' _)
Objects .Displayed.assoc' _ _ _ = Cartesian-morphism-pathp E (assoc' _ _ _)
```

We have an evident forgetful [fibred] functor from the object fibration
back to $\cE$.

[fibred]: Cat.Displayed.Functor.html

```agda
Objects-forget : Vertical-fibred-functor Objects E
Objects-forget .vert .F₀' x = x
Objects-forget .vert .F₁' f' = f' .hom'
Objects-forget .vert .F-id' = refl
Objects-forget .vert .F-∘' = refl
Objects-forget .F-cartesian f' _ = f' .cartesian
```


<!--
```agda
private module Objects = Displayed Objects
```
-->

Since the object fibration only has Cartesian morphisms from $\cE$, we
can prove that it consists entirely of Cartesian maps. This is not
immediate, since to include the "universal" map, we must prove that it
too is Cartesian; but that follows from the pasting law for Cartesian
squares.

```agda
Objects-cartesian
  : ∀ {x y x' y'} {f : Hom x y} (f' : Cartesian-morphism E f x' y')
  → is-cartesian Objects f f'
Objects-cartesian f' = cart where
  open is-cartesian

  cart : is-cartesian _ _ _
  cart .universal m h' = cart-paste E f' h'
  cart .commutes m h' =
    Cartesian-morphism-pathp E (f' .cartesian .commutes m (h' .hom'))
  cart .unique m' p =
    Cartesian-morphism-pathp E (f' .cartesian .unique (hom' m') (ap hom' p))
```

If $E$ is a fibration, then its fibration of objects is a a [right
fibration], by the preceding result. This means the fibres of the object
fibration are groupoids.

[right fibration]: Cat.Displayed.Cartesian.Right.html

```agda
Objects-fibration : Cartesian-fibration E → Cartesian-fibration Objects
Objects-fibration fib .Cartesian-fibration.has-lift f y' = cart-lift where
  open Cartesian-fibration fib

  cart-lift : Cartesian-lift Objects f y'
  cart-lift .Cartesian-lift.x' = has-lift.x' f y'
  cart-lift .Cartesian-lift.lifting .hom' = has-lift.lifting f y'
  cart-lift .Cartesian-lift.lifting .cartesian = has-lift.cartesian f y'
  cart-lift .Cartesian-lift.cartesian = Objects-cartesian _

Objects-right-fibration : Cartesian-fibration E → Right-fibration Objects
Objects-right-fibration fib .Right-fibration.is-fibration = Objects-fibration fib
Objects-right-fibration fib .Right-fibration.cartesian = Objects-cartesian
```

## The core of a fibration

The fibration of objects is the relative analog of the [core] of a
category, sharing its universal property.  Rather than a groupoid,
suppose we have a right fibration $\cR$ and a [[fibred functor]] $F : \cR
\to \cE$: to complete the analogy, we show $F$ factors through $\cE$'s
fibration of objects.

[core]: Cat.Instances.Core.html

<!--
```agda
module _
  {or ℓr} {R : Displayed B or ℓr}
  (R-right : Right-fibration R)
  where
  private
    open Vertical-fibred-functor
    module R-right = Right-fibration R-right
```
-->

```agda
  Objects-universal
    : (F : Vertical-fibred-functor R E)
    → Vertical-fibred-functor R Objects
  Objects-universal F .vert .F₀' x = F .F₀' x
  Objects-universal F .vert .F₁' f' .hom' = F .F₁' f'
  Objects-universal F .vert .F₁' f' .cartesian =
    F .F-cartesian f' (R-right.cartesian f')
  Objects-universal F .vert .F-id' =
    Cartesian-morphism-pathp E (F .F-id')
  Objects-universal F .vert .F-∘' =
    Cartesian-morphism-pathp E (F .F-∘')
  Objects-universal F .F-cartesian f' cart =
    Objects-cartesian _

  Objects-factors
    : (F : Vertical-fibred-functor R E)
    → F ≡ Objects-forget Vf∘ Objects-universal F
  Objects-factors F =
    Vertical-fibred-functor-path (λ _ → refl) (λ _ → refl)
```

<!-- [TODO: Reed M, 06/05/2023] This is actually part of a biadjunction
between the bicategory of right fibrations over B and the category
of fibrations over B.
-->
