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

<!--
```agda
open import Cat.Reasoning C
open Functor
open _=>_
private variable
  a b : Ob
```
-->

The assignment of $\hom$-sets in a [[precategory]] $\cC$, thought of as
a function of two arguments valued in [[sets]], extends naturally to a
[[bifunctor]] $\cC\op \to \cC \to \Sets$. A morphism $a \to b$ acts on
the left by *pre*composition, $\hom(b,x) \to \hom(a,x)$, and on the right by
*post*compoosition, $\hom(x,a) \to \hom(x,b)$.

```agda
Hom[-,-] : Bifunctor (C ^op) C (Sets h)
Hom[-,-] = make-bifunctor record where
  F₀ X Y = el! (Hom X Y)

  lmap     f = _∘ f
  rmap     f = f ∘_
```

Both functoriality constraints, as well as the interchange law
`lrmap`{.Agda}, boil down to the category laws.

```agda
  lmap-∘ f g = ext λ h →
    h ∘ g ∘ f   ≡⟨ assoc _ _ _ ⟩
    (h ∘ g) ∘ f ∎
  lmap-id    = ext λ h → idr _

  rmap-∘ f g = ext λ h → sym (assoc _ _ _)
  rmap-id    = ext λ h → idl _

  lrmap  f g = ext λ h → sym (assoc _ _ _)
```

As a bifunctor, $\hom(-,-)$ has associated partial applications on
either side. We use the intuitive names `Hom-from`{.Agda} and
`Hom-into`{.Agda}, instead of directional names referring to "left" and
"right".

```agda
open Bifunctor Hom[-,-] public using ()
  renaming (Left to Hom-into)

open Functor Hom[-,-] public using ()
  renaming (F₀ to Hom-from)
```

## The Yoneda embedding

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

Since $\hom(-,-)$ is a functor $\cC\op \to [\cC, \Sets]$, it flips to
give a functor $\cC \to [\cC\op,\Sets]$: this is $\cC$'s [[Yoneda
embedding]].

```agda
よ : Bifunctor C (C ^op) (Sets h)
よ = Flip Hom[-,-]

open Functor よ renaming (F₀ to よ₀) using () public
```

<!--
```agda
_ : ∀ {X} → Hom-into X ≡ よ₀ X
_ = refl
```
-->

The action of `よ`{.Agda} on morphisms has an inverse, given by
evaluating the natural transformation with the identity map; Hence, the
Yoneda embedding functor is [[fully faithful]].

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
$\hom(-,-)$ functor, thought of as an embedding into functors $\cC \to
\Sets$ is **contravariant**. This makes the "covariant Yoneda embedding"
much less pleasant to work with, though we define it anyways for
posterity.

```agda
よcov : Functor (C ^op) Cat[ C , Sets h ]
よcov = Hom[-,-]
```

As expected, the covariant yoneda embedding is also fully faithful.

```agda
Hom[-,-]-is-fully-faithful : is-fully-faithful Hom[-,-]
Hom[-,-]-is-fully-faithful = is-iso→is-equiv λ where
  .is-iso.from nt → nt .η _ id
  .is-iso.rinv nt → ext λ c g → sym (nt .is-natural _ _ _) $ₚ _ ∙ ap (nt .η c) (idr g)
  .is-iso.linv h  → idl h
```

<!--
```agda
Hom[-,-]-is-faithful : is-faithful Hom[-,-]
Hom[-,-]-is-faithful = ff→faithful {F = Hom[-,-]} (Hom[-,-]-is-fully-faithful)
```
-->
