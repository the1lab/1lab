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
Change-of-base .Displayed.Ob[_] x      = E.Ob[ F₀ x ]
Change-of-base .Displayed.Hom[_] f x y = E.Hom[ F₁ f ] x y
Change-of-base .Displayed.Hom[_]-set f = E.Hom[ F₁ f ]-set
Change-of-base .Displayed.id'          = hom[ sym F-id ] E.id'
Change-of-base .Displayed._∘'_ f' g'   = hom[ sym (F-∘ _ _) ] (f' E.∘' g')
```

Proving that the pullback $F^*(E)$ is indeed a displayed category is a
bit trickier than it might seem --- we must adjust the identity and
composites in $E$ by the paths witnessing functoriality of $F$, and this
really throws a spanner in the works --- but the handy [displayed
category reasoning combinators][dr] are here to help.

[dr]: Cat.Displayed.Reasoning.html

```agda
Change-of-base .Displayed.idr' {f = f} f' = to-pathp[] $
  hom[] (hom[ F-∘ _ _ ]⁻ (f' E.∘' hom[ F-id ]⁻ _)) ≡⟨ hom[]⟩⟨ smashr _ _ ⟩
  hom[] (hom[] (f' E.∘' E.id'))                    ≡⟨ Ds.disp! E ⟩
  f'                                               ∎

Change-of-base .Displayed.idl' f' = to-pathp[] $
  hom[] (hom[ F-∘ _ _ ]⁻ (hom[ F-id ]⁻ _ E.∘' f')) ≡⟨ hom[]⟩⟨ smashl _ _ ⟩
  hom[] (hom[] (E.id' E.∘' f'))                    ≡⟨ Ds.disp! E ⟩
  f'                                               ∎

Change-of-base .Displayed.assoc' f' g' h' = to-pathp[] $
  hom[ ap F₁ _ ] (hom[ F-∘ _ _ ]⁻ (f' E.∘' hom[ F-∘ _ _ ]⁻ (g' E.∘' h')))   ≡⟨ hom[]⟩⟨ smashr _ _ ⟩
  hom[] (hom[] (f' E.∘' g' E.∘' h'))                                        ≡⟨ Ds.disp! E ⟩
  hom[ sym (F-∘ _ _) ] (hom[ sym (F-∘ _ _) ] (f' E.∘' g') E.∘' h')          ∎
```

<!--
```agda
Change-of-base .Displayed.hom[_] p f' = hom[ ap F₁ p ] f'
Change-of-base .Displayed.coh[_] p f' = coh[ ap F₁ p ] f'
```
-->

## As a fibration

If $\cE$ is a [[cartesian fibration]], then the base change of $\cE$
along $F$ is also cartesian. To prove this, observe that the object and
hom spaces of `Change-of-base`{.Agda} contain the same data as $\cE$,
just restricted to objects and morphisms in the image of $F$. This means
that we still have cartesian lifts of all morphisms in $\cX$: we
just have to perform the lifting of $F f$.

```agda
Change-of-base-fibration : Cartesian-fibration E → Cartesian-fibration Change-of-base
Change-of-base-fibration fib f FY' = f-cart-lift where
  open Cartesian-fibration E fib

  f-cart-lift : Cartesian-lift Change-of-base f FY'
  f-cart-lift .Cartesian-lift.x' = F₁ f ^* FY'
  f-cart-lift .Cartesian-lift.lifting = π* (F₁ f) FY'
  f-cart-lift .Cartesian-lift.cartesian .is-cartesian.universal m h' =
    π*.universal (F₁ m) (hom[ F-∘ f m ] h')
  f-cart-lift .Cartesian-lift.cartesian .is-cartesian.commutes m h' =
    hom[ F-∘ f m ]⁻ (π* (F₁ f) FY' E.∘' π*.universal (F₁ m) (hom[ F-∘ f m ] h')) ≡⟨ ap hom[ F-∘ f m ]⁻ (π*.commutes _ _) ⟩
    hom[ F-∘ f m ]⁻ (hom[ F-∘ f m ] h')                                          ≡⟨ Ds.disp! E ⟩
    h'                                                                           ∎
  f-cart-lift .Cartesian-lift.cartesian .is-cartesian.unique {m = m} {h' = h'} m' p =
    π*.unique m' $
      π* (F₁ f) FY' E.∘' m'                                    ≡⟨ Ds.disp! E ⟩
      hom[ F-∘ f m ] (hom[ F-∘ f m ]⁻ (π* (F₁ f) FY' E.∘' m')) ≡⟨ ap hom[ F-∘ f m ] p ⟩
      hom[ F-∘ f m ] h'                                        ∎
```
