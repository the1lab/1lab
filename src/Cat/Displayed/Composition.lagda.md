<!--
```agda
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Functor
open import Cat.Displayed.Total
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Reasoning as DR
```
-->

```agda
module Cat.Displayed.Composition where
```

# Composition of displayed categories

A [[displayed category]] $\cE$ over $\cB$ is equivalent to the data
of a functor into $\cB$; the forward direction of this equivalence is
witnessed by the [[total category]] of $\cE$, along with the canonical
projection functor from the total category into $\cB$. This suggests
that we ought to be able to compose displayed categories. That is,
if $\cE$ is displayed over $\cB$, and $\cF$ is displayed over
$\int \cE$, then we can construct a new category $\cE \cdot \cF$
displayed over $\cB$ that contains the data of both $\cE$ and
$\cF$.

To actually construct the composite, we bundle up the data of
$\cE$ and $\cF$ into pairs, so an object in $\cE \cdot \cF$
over $X : \cB$ consists of a pair objects of $X' : \cE$ over $X$,
and $X'' : \cF$ over $X$ and $X'$. Morphisms are defined similarly,
as do equations.

```agda
_D∘_ : ∀ {o ℓ o' ℓ' o'' ℓ''}
       → {ℬ : Precategory o ℓ}
       → (ℰ : Displayed ℬ o' ℓ') → (ℱ : Displayed (∫ ℰ) o'' ℓ'')
       → Displayed ℬ (o' ⊔ o'') (ℓ' ⊔ ℓ'')
_D∘_ {ℬ = ℬ} ℰ ℱ = disp where
  module ℰ = Displayed ℰ
  module ℱ = Displayed ℱ

  disp : Displayed ℬ _ _
  Displayed.Ob[ disp ] X =
    Σ[ X' ∈ ℰ.Ob[ X ] ] ℱ.Ob[ X , X' ]
  Displayed.Hom[ disp ] f X Y =
    Σ[ f' ∈ ℰ.Hom[ f ] (X .fst) (Y .fst) ] ℱ.Hom[ total-hom f f' ] (X .snd) (Y .snd)
  Displayed.Hom[ disp ]-set f x y =
    Σ-is-hlevel 2 (ℰ.Hom[ f ]-set (x .fst) (y .fst)) λ f' →
    ℱ.Hom[ total-hom f f' ]-set (x .snd) (y .snd)
  disp .Displayed.id' =
    ℰ.id' , ℱ.id'
  disp .Displayed._∘'_ f' g' =
    (f' .fst ℰ.∘' g' .fst) , (f' .snd ℱ.∘' g' .snd)
  disp .Displayed.idr' f' =
    ℰ.idr' (f' .fst) ,ₚ ℱ.idr' (f' .snd)
  disp .Displayed.idl' f' =
    ℰ.idl' (f' .fst) ,ₚ ℱ.idl' (f' .snd)
  disp .Displayed.assoc' f' g' h' =
    (ℰ.assoc' (f' .fst) (g' .fst) (h' .fst)) ,ₚ (ℱ.assoc' (f' .snd) (g' .snd) (h' .snd))
```

We also obtain a [[displayed functor]] from $\cE \cdot \cF$ to $\cE$
that projects out the data of $\cE$ from the composite.

```agda
πᵈ : ∀ {o ℓ o' ℓ' o'' ℓ''}
    → {ℬ : Precategory o ℓ}
    → {ℰ : Displayed ℬ o' ℓ'} {ℱ : Displayed (∫ ℰ) o'' ℓ''}
    → Displayed-functor (ℰ D∘ ℱ) ℰ Id
πᵈ .Displayed-functor.F₀' = fst
πᵈ .Displayed-functor.F₁' = fst
πᵈ .Displayed-functor.F-id' = refl
πᵈ .Displayed-functor.F-∘' = refl
```

## Composition of fibrations

As one may expect, the composition of fibrations is itself a fibration.


<!--
```agda
module _
  {o ℓ o' ℓ' o'' ℓ''}
  {ℬ : Precategory o ℓ}
  {ℰ : Displayed ℬ o' ℓ'} {ℱ : Displayed (∫ ℰ) o'' ℓ''}
  where

  open Precategory ℬ
```
-->

The idea of the proof is that we can take lifts of lifts, and in fact,
this is exactly how we construct the liftings.

```agda
  fibration-∘
    : Cartesian-fibration ℰ → Cartesian-fibration ℱ
    → Cartesian-fibration (ℰ D∘ ℱ)
  fibration-∘ ℰ-fib ℱ-fib = ℰ∘ℱ-fib where
```

<!--
```agda
    open Cartesian-lift

    module ℰ where
      open Cartesian-fibration ℰ ℰ-fib public
      open Displayed ℰ public

    module ℱ where
      open Cartesian-fibration ℱ ℱ-fib public
      open Displayed ℱ public
      open DR ℱ public
```
-->

```agda
    ℰ∘ℱ-fib : Cartesian-fibration (ℰ D∘ ℱ)
    ℰ∘ℱ-fib f (y' , y'') = f-lift where

      f-lift : Cartesian-lift (ℰ D∘ ℱ) f (y' , y'')
      f-lift .x' = f ℰ.^* y' , total-hom f (ℰ.π* f y') ℱ.^* y''
      f-lift .lifting = ℰ.π* f y' , ℱ.π* (total-hom f (ℰ.π* f y')) y''

```

However, showing that the constructed lift is cartesian is somewhat more
subtle. The issue is that when we go to construct the universal map,
we are handed an $h'$ displayed over $f \cdot m$, and also an $h''$
displayed over $f \cdot m, h'$, which is not a composite definitionally.
However, it is *propositionally* a composite, as is witnessed by
`ℰ-lift .commutes`, so we can use the generalized propositional functions
of `ℱ-lift` to construct the universal map, and show that it is indeed
universal.

```agda
      f-lift .cartesian .is-cartesian.universal m (h' , h'') =
        ℰ.π*.universal m h' ,
        ℱ.π*.universal' (total-hom-path ℰ refl (ℰ.π*.commutes m h')) h''
      f-lift .cartesian .is-cartesian.commutes m h' =
        ℰ.π*.commutes m (h' .fst) ,ₚ
        ℱ.π*.commutesp _ (h' .snd)
      f-lift .cartesian .is-cartesian.unique m' p =
        ℰ.π*.unique (m' .fst) (ap fst p) ,ₚ
        ℱ.π*.uniquep _ _
          (total-hom-path ℰ refl (ℰ.π*.commutes _ _))
          (m' .snd)
          (ap snd p)
```
