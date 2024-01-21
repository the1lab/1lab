<!--
```agda
open import Cat.Functor.Properties
open import Cat.Instances.Product
open import Cat.Functor.Closed
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Functor.Hom {o h} (C : Precategory o h) where
```

# The Hom functor {defines="hom-functor"}

We prove that the assignment of $\hom$-sets in a `Precategory`{.Agda}
$\cC$ is a `functor`{.Agda}, specifically a bifunctor from $\cC\op
\times \cC$ to $\Sets$. The action of $(f, h)$ on a morphism $g$ is
given by $h \circ g \circ f$; Since $f$ is acting by precomposition, the
first coordinate is contravariant ($\cC\op$).

<!--
```agda
open import Cat.Reasoning C
open Functor
open _=>_
private variable
  a b : Ob
```
-->

```agda
Hom[-,-] : Functor ((C ^op) ×ᶜ C) (Sets h)
Hom[-,-] .F₀ (a , b) = el (Hom a b) (Hom-set a b)
Hom[-,-] .F₁ (f , h) g = h ∘ g ∘ f
Hom[-,-] .F-id = funext λ x → ap (_ ∘_) (idr _) ∙ idl _
Hom[-,-] .F-∘ (f , h) (f' , h') = funext λ where
  g → (h ∘ h') ∘ g ∘ f' ∘ f ≡⟨ cat! C ⟩
      h ∘ (h' ∘ g ∘ f') ∘ f ∎
```

We also can define "partially applied" versions of the hom functor:
```agda
Hom[_,-] : Ob → Functor C (Sets h)
Hom[ x ,-] .F₀ y = el (Hom x y) (Hom-set x y)
Hom[ x ,-] .F₁ f g = f ∘ g
Hom[ x ,-] .F-id = funext (λ f → idl f)
Hom[ x ,-] .F-∘ f g = funext λ h → sym (assoc f g h)
```

## The Yoneda embedding {defines="yoneda-embedding"}

Abstractly and nonsensically, one could say that the Yoneda embedding
`よ`{.Agda} is the [exponential transpose] of `flipping`{.Agda
ident=Flip} the `Hom[-,-]`{.Agda} [bifunctor]. However, this
construction generates _awful_ terms, so in the interest of
computational efficiency we build up the functor explicitly.

[exponential transpose]: Cat.Functor.Closed.html
[bifunctor]: Cat.Functor.Bifunctor.html

```agda
module _ where private
  よ : Functor C (Cat[ C ^op , Sets h ])
  よ = Curry Flip where
    open import
      Cat.Functor.Bifunctor {C = C ^op} {D = C} {E = Sets h} Hom[-,-]
```

We can describe the object part of this functor as taking an object $c$
to the functor $\hom(-,c)$ of map into $c$, with the transformation
$\hom(x,y) \to \hom(x,z)$ given by precomposition.

```agda
よ₀ : Ob → Functor (C ^op) (Sets h)
よ₀ c .F₀ x    = el (Hom x c) (Hom-set _ _)
よ₀ c .F₁ f    = _∘ f
よ₀ c .F-id    = funext idr
よ₀ c .F-∘ f g = funext λ h → assoc _ _ _

```

We also define a synonym for よ₀ to better line up with the covariant
direction.

```agda
Hom[-,_] : Ob → Functor (C ^op) (Sets h)
Hom[-,_] x = よ₀ x
```

<!--
```agda
Hom-from : Ob → Functor C (Sets h)
Hom-from = Hom[_,-]

Hom-into : Ob → Functor (C ^op) (Sets h)
Hom-into = よ₀
```
-->


The morphism part takes a map $f$ to the transformation given by
postcomposition; This is natural because we must show $f \circ x \circ g
= (f \circ x) \circ g$, which is given by associativity in $C$.

```agda
よ₁ : Hom a b → よ₀ a => よ₀ b
よ₁ f .η _ g            = f ∘ g
よ₁ f .is-natural x y g = funext λ x → assoc f x g
```

The other category laws from $\cC$ ensure that this assignment of
natural transformations is indeed functorial:

```agda
よ : Functor C Cat[ C ^op , Sets h ]
よ .F₀      = よ₀
よ .F₁      = よ₁
よ .F-id    = Nat-path λ _ i g → idl g i
よ .F-∘ f g = Nat-path λ _ i h → assoc f g h (~ i)
```


The morphism mapping `よ₁`{.Agda} has an inverse, given by evaluating the
natural transformation with the identity map; Hence, the Yoneda
embedding functor is [[fully faithful]].

```agda
よ-is-fully-faithful : is-fully-faithful よ
よ-is-fully-faithful = is-iso→is-equiv isom where
  open is-iso

  isom : is-iso よ₁
  isom .inv nt = nt .η _ id
  isom .rinv nt = ext λ c g →
    happly (sym (nt .is-natural _ _ _)) _ ∙ ap (nt .η c) (idl g)
  isom .linv _ = idr _
```

## The covariant yoneda embedding

One common point of confusion is why category theorists prefer
presheaves over covariant functors into $\Sets$. One key reason is that
the yoneda embedding into presheaves is **covariant**, whereas the
embedding into functors $\cC \to \Sets$ is **contravariant**. This
makes the covariant yoneda embedding much less pleasant to work with,
though we define it anyways for posterity.

```agda
よcov₁ : Hom a b → Hom-from b => Hom-from a
よcov₁ f .η _ g = g ∘ f
よcov₁ f .is-natural x y g = funext λ x → sym (assoc g x f)

よcov : Functor (C ^op) Cat[ C , Sets h ]
よcov .F₀ = Hom-from
よcov .F₁ = よcov₁
よcov .F-id = ext λ _ g → idr g
よcov .F-∘ f g = ext λ _ h → (assoc h g f)
```

As expected, the covariant yoneda embedding is also fully faithful.

```agda
よcov-is-fully-faithful : is-fully-faithful よcov
よcov-is-fully-faithful = is-iso→is-equiv isom where
  open is-iso

  isom : is-iso よcov₁
  isom .inv nt = nt .η _ id
  isom .rinv nt = ext λ c g →
    sym (nt .is-natural _ _ _) $ₚ _ ∙ ap (nt .η c) (idr g)
  isom .linv _ = idl _
```
