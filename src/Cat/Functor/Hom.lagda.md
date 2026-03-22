<!--
```agda
open import Cat.Functor.Properties
open import Cat.Functor.Bifunctor
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
Hom[-,-] : Bifunctor (C ^op) C (Sets h)
Hom[-,-] = make-bifunctor record where
  F₀ X Y = el! (Hom X Y)

  lmap     f = _∘ f
  lmap-∘ f g = ext λ h → assoc _ _ _
  lmap-id    = ext λ h → idr _

  rmap     f = f ∘_
  rmap-∘ f g = ext λ h → sym (assoc _ _ _)
  rmap-id    = ext λ h → idl _

  lrmap  f g = ext λ h → sym (assoc _ _ _)
```

We also can define "partially applied" versions of the hom functor:
```agda
Hom[_,-] : Ob → Functor C (Sets h)
Hom[_,-] = Bifunctor.Right Hom[-,-]
```

## The Yoneda embedding

[exponential transpose]: Cat.Functor.Closed.html
[bifunctor]: Cat.Functor.Bifunctor.html

:::{.definition .commented-out #yoneda-embedding}
The **Yoneda embedding** $\yo : \cC \to \psh(\cC)$ from a
[[precategory]] $\cC$ into its category of [[presheaves]] $\psh(\cC)$ is
the functor
$$
\yo(c) = \cC(-, c)
$$
which assigns to each object the partially applied $\hom$-functor of
morphisms into that object.
:::

```agda
よ : Bifunctor C (C ^op) (Sets h)
よ = Flip Hom[-,-]
```

We can describe the object part of this functor as taking an object $c$
to the functor $\hom(-,c)$ of map into $c$, with the transformation
$\hom(x,y) \to \hom(x,z)$ given by precomposition.

```agda
open Functor よ renaming (F₀ to よ₀) public
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

The morphism mapping `よ₁`{.Agda} has an inverse, given by evaluating the
natural transformation with the identity map; Hence, the Yoneda
embedding functor is [[fully faithful]].

```agda
よ-is-fully-faithful : is-fully-faithful よ
よ-is-fully-faithful = is-iso→is-equiv λ where
  .is-iso.from nt → nt .η _ id
  .is-iso.rinv nt → ext λ c g →
    nt .η _ id ∘ g   ≡⟨ sym (nt .is-natural _ _ _) $ₚ _ ⟩
    nt .η c (id ∘ g) ≡⟨ ap (nt .η c) (idl g) ⟩
    nt .η c g        ∎
  .is-iso.linv _  → idr _
```

<!--
```agda
よ-is-faithful : is-faithful よ
よ-is-faithful = ff→faithful {F = よ} (よ-is-fully-faithful)
```
-->

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
よcov-is-fully-faithful = is-iso→is-equiv λ where
  .is-iso.from nt → nt .η _ id
  .is-iso.rinv nt → ext λ c g → sym (nt .is-natural _ _ _) $ₚ _ ∙ ap (nt .η c) (idr g)
  .is-iso.linv h  → idl h
```

<!--
```agda
よcov-is-faithful : is-faithful よcov
よcov-is-faithful = ff→faithful {F = よcov} (よcov-is-fully-faithful)
```
-->
