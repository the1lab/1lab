---
description: |
  We make precise the difference between dependent sum types and
  existential quantifiers. In particular, we show that the "image" of a
  function, but defined with Σ rather than ∃, fails to be different from
  the domain of the function.
---
<!--
```
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type
```
-->

```agda
module 1Lab.Counterexamples.Sigma where
```

# Σ is not ∃

Defined normally, the _image_ of a function $f : X \to Y$ is the subset
of $Y$ given by the elements $y : Y$ for which _there exists_ an element
$x : X$ with $f(x) = y$. In set theoretical notation: $\rm{im}(f) = \{ y
\in Y | \exists x \in X, f(x) = y \}$.

It is a commonly held misunderstanding that when translating such a
definition into type theory, both subsets and existential quantifiers
should be read as specific cases of the dependent sum, `Σ`{.Agda} -
perhaps using "subset" to mean "`Σ` for which the type family is
valued in [[propositions]]". Indeed, the first projection out of these
is an [[embedding]], so this translation is accurate **for subsets**.

However, let's see what happens when we naïvely translate the definition
of image above:

```agda
private variable
  ℓ : Level
  A B : Type ℓ

image : (A → B) → Type _
image {A = A} {B = B} f = Σ[ y ∈ B ] Σ[ x ∈ A ] (f x ≡ y)
```

The definition above, which could be called "Curry-Howard image", does
not accurately represent the image of a function: $\rm{image}(f) \simeq
A$, independent of $f$:

```agda
image≃domain : {f : A → B} → image f ≃ A
image≃domain {f = f} = Iso→Equiv the-iso where
  the-iso : Iso _ _
  the-iso .fst (y , x , p) = x
  the-iso .snd .is-iso.inv x = f x , x , refl
  the-iso .snd .is-iso.rinv x = refl
  the-iso .snd .is-iso.linv (y , x , p) i = p i , x , λ j → p (i ∧ j)
```

This is a direct cubical interpretation of the following argument, which
goes through in any theory with J[^2]:

> First, observe that we can reorder `Σ[ y ∈ B ] Σ[ x ∈ A ] (f x ≡ y)`
into `Σ[ x ∈ A ] Σ[ y ∈ B ] (f x ≡ y)`. By path induction, the type `Σ[
y ∈ B ] (f x ≡ y)` is contractible (it is a singleton), leaving us with
something isomorphic to `Σ[ x ∈ A ] *`, which is evidently isomorphic to
`A`.

Hence we have, for example, that the "image" of the canonical function
`Bool → ⊤` is isomorphic to `Bool`{.Agda}:

```agda
ignore-bool : Bool → ⊤
ignore-bool _ = tt

woops : image ignore-bool ≃ Bool
woops = image≃domain
```

[^2]: In fact, note that if we reorder `p i, x, λ j → p (i ∧ j)` we get
`x, p i, λ j → p (i ∧ j)`, which is exactly the proof term which
establishes [[contractibility of singletons|path induction]].
