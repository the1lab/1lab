<!--
```agda
open import Cat.Displayed.Cartesian
open import Cat.Instances.Functor
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Reasoning as Dr
import Cat.Displayed.Solver as Ds
```
-->

```agda
module
  Cat.Displayed.Instances.Pullback
    {o ℓ o' ℓ' o'' ℓ''}
    {X : Precategory o ℓ} {B : Precategory o' ℓ'}
    (F : Functor X B)
    (E : Displayed B o'' ℓ'')
  where
```

# Pullback of a displayed category {defines=pullback-fibration}

If we have a category $E$ [[displayed over|displayed category]] $B$,
then a functor $F : X \to B$ defines a (contravariant) "change-of-base"
action, resulting in a category $F^*(E)$ displayed over $X$.

<!--
```agda
private
  module X = Precategory X
  module B = Precategory B
  module E = Displayed E

open Functor F
open Displayed
open Dr E
```
-->

The reason for this contravariance is the following: A category
displayed over $X$ must have a $X$-indexed space of objects; But our
category $E$ has a $B$-indexed space of objects. Fortunately, $F$ gives
us a map $x \mapsto F_0(x)$ which allows us to convert our $X$-indices
to $B$-indices. The same goes for indexing the displayed $\hom$-sets.

```agda
Change-of-base : Displayed X o'' ℓ''
Change-of-base .Ob[_] x      = E.Ob[ F₀ x ]
Change-of-base .Hom[_] f x y = E.Hom[ F₁ f ] x y
Change-of-base .Hom[_]-set f = E.Hom[ F₁ f ]-set
Change-of-base .id'          = hom[ sym F-id ] E.id'
Change-of-base ._∘'_ f' g'   = hom[ sym (F-∘ _ _) ] (f' E.∘' g')
```

Proving that the pullback $F^*(E)$ is indeed a displayed category is a
bit trickier than it might seem --- we must adjust the identity and
composites in $E$ by the paths witnessing functoriality of $F$, and this
really throws a spanner in the works --- but the handy [displayed
category reasoning combinators][dr] are here to help.

[dr]: Cat.Displayed.Reasoning.html

```agda
Change-of-base .idr' {f = f} f' = to-pathp $
  hom[] (hom[ F-∘ _ _ ]⁻ (f' E.∘' hom[ F-id ]⁻ _)) ≡⟨ hom[]⟩⟨ smashr _ _ ⟩
  hom[] (hom[] (f' E.∘' E.id'))                    ≡⟨ Ds.disp! E ⟩
  f'                                               ∎

Change-of-base .idl' f' = to-pathp $
  hom[] (hom[ F-∘ _ _ ]⁻ (hom[ F-id ]⁻ _ E.∘' f')) ≡⟨ hom[]⟩⟨ smashl _ _ ⟩
  hom[] (hom[] (E.id' E.∘' f'))                    ≡⟨ Ds.disp! E ⟩
  f'                                               ∎

Change-of-base .assoc' f' g' h' = to-pathp $
  hom[ ap F₁ _ ] (hom[ F-∘ _ _ ]⁻ (f' E.∘' hom[ F-∘ _ _ ]⁻ (g' E.∘' h')))   ≡⟨ hom[]⟩⟨ smashr _ _ ⟩
  hom[] (hom[] (f' E.∘' g' E.∘' h'))                                        ≡⟨ Ds.disp! E ⟩
  hom[ sym (F-∘ _ _) ] (hom[ sym (F-∘ _ _) ] (f' E.∘' g') E.∘' h')          ∎
```

## As a fibration

If $\cE$ is a [[cartesian fibration]], then the base change of $\cE$
along $F$ is also cartesian. To prove this, observe that the object and
hom spaces of `Change-of-base`{.Agda} contain the same data as $\cE$,
just restricted to objects and morphisms in the image of $F$. This means
that we still have cartesian lifts of all morphisms in $\cX$: we
just have to perform the lifting of $F f$.

```agda
Change-of-base-fibration : Cartesian-fibration E → Cartesian-fibration Change-of-base
Change-of-base-fibration fib .Cartesian-fibration.has-lift f FY' = cart-lift
  where
    open Cartesian-lift (Cartesian-fibration.has-lift fib (F₁ f) FY')

    cart-lift : Cartesian-lift Change-of-base f FY'
    cart-lift .Cartesian-lift.x' = x'
    cart-lift .Cartesian-lift.lifting = lifting
    cart-lift .Cartesian-lift.cartesian .is-cartesian.universal m h' =
      universal (F .Functor.F₁ m) (hom[ F-∘ f m ] h')
    cart-lift .Cartesian-lift.cartesian .is-cartesian.commutes m h' =
      hom[ F-∘ f m ]⁻ (lifting E.∘' universal (F₁ m) (hom[ F-∘ f m ] h')) ≡⟨ ap hom[ F-∘ f m ]⁻ (commutes _ _) ⟩
      hom[ F-∘ f m ]⁻ (hom[ F-∘ f m ] h')                                 ≡⟨ Ds.disp! E ⟩
      h'                                                                  ∎
    cart-lift .Cartesian-lift.cartesian .is-cartesian.unique {m = m} {h' = h'} m' p =
      unique m' $
        lifting E.∘' m'                                    ≡⟨ Ds.disp! E ⟩
        hom[ F-∘ f m ] (hom[ F-∘ f m ]⁻ (lifting E.∘' m')) ≡⟨ ap hom[ F-∘ f m ] p ⟩
        hom[ F-∘ f m ] h' ∎
```
