---
description: |
  Strong projective objects.
---
<!--
```agda
open import Cat.Functor.Morphism
open import Cat.Functor.Hom
open import Cat.Prelude

open import Data.Set.Surjection

import Cat.Diagram.Projective
import Cat.Morphism.StrongEpi
import Cat.Reasoning
```
-->
```agda
module Cat.Diagram.Projective.Strong
  {o ℓ}
  (C : Precategory o ℓ)
  where
```

<!--
```agda
open Cat.Diagram.Projective C
open Cat.Morphism.StrongEpi C
open Cat.Reasoning C
```
-->

# Strong projective objects

:::{.definition #strong-projective-object alias="strong-projective"}
Let $\cC$ be a precategory. An object $P : \cC$ is a
**strong projective object** if it has the left-lifting property against
[[strong epimorphisms]].

More explicitly, $P$ is a strong projective object if for every
morphism $p : P \to Y$ and strong epi $e : X \epi Y$, there merely exists
a $s : P \to X$ such that $e \circ s = p$, as in the following diagram:

~~~{.quiver}
\begin{tikzcd}
  && X \\
  \\
  P && Y
  \arrow["e", two heads, from=1-3, to=3-3]
  \arrow["\exists", dashed, from=3-1, to=1-3]
  \arrow["p"', from=3-1, to=3-3]
\end{tikzcd}
~~~
:::

```agda
is-strong-projective : (P : Ob) → Type _
is-strong-projective P =
  ∀ {X Y} (p : Hom P Y) (e : Hom X Y)
  → is-strong-epi e
  → ∃[ s ∈ Hom P X ] (e ∘ s ≡ p)
```

::: warning
Being a strong projective object is actually a weaker condition than
being a [[projective object]]: strong projectives only need to lift
against strong epis, whereas projectives need to lift against *all* epis.
:::

```agda
projective→strong-projective
  : ∀ {P}
  → is-projective P
  → is-strong-projective P
projective→strong-projective pro p e e-strong =
  pro p (record { mor = e ; epic = e-strong .fst })
```

## A functorial definition

Like their non-strong counterparts, we can give a functorial definition of
strong projectives. In particular, an object $P : \cC$ is a strong projective
if and only if the $\hom$-functor $\cC(P,-)$ preserves strong epimorphisms.

```agda
preserves-strong-epis→strong-projective
  : ∀ {P}
  → preserves-strong-epis (Hom-from C P)
  → is-strong-projective P

strong-projective→preserves-strong-epis
  : ∀ {P}
  → is-strong-projective P
  → preserves-strong-epis (Hom-from C P)
```

<details>
<summary>These proofs are essentially the same as the corresponding
ones for projective objects, so we omit the details.
</summary>
```agda
preserves-strong-epis→strong-projective {P = P} hom-epi {X = X} {Y = Y} p e e-strong =
  epi→surjective (el! (Hom P X)) (el! (Hom P Y))
    (e ∘_)
    (λ {c} → hom-epi e-strong .fst {c = c})
    p

strong-projective→preserves-strong-epis {P = P} pro {X} {Y} {f = f} f-strong =
    surjective→strong-epi (el! (Hom P X)) (el! (Hom P Y)) (f ∘_) $ λ p →
    pro p f f-strong
```
</details>
