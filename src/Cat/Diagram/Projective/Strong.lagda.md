---
description: |
  Strong projective objects.
---
<!--
```agda
open import Cat.Diagram.Coproduct.Copower
open import Cat.Diagram.Coproduct.Indexed
open import Cat.Functor.Morphism
open import Cat.Morphism.Class
open import Cat.Morphism.Lifts
open import Cat.Diagram.Zero
open import Cat.Functor.Hom
open import Cat.Prelude

open import Data.Set.Projective
open import Data.Set.Surjection
open import Data.Dec

import Cat.Diagram.Separator.Strong
import Cat.Morphism.Strong.Epi
import Cat.Diagram.Projective
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
open Cat.Morphism.Strong.Epi C
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
  \arrow["\exists s", dashed, from=3-1, to=1-3]
  \arrow["p"', from=3-1, to=3-3]
\end{tikzcd}
~~~
:::

```agda
is-strong-projective : (P : Ob) → Type _
is-strong-projective P = Lifts C P StrongEpis
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
projective→strong-projective pro e e-strong p =
  pro e (e-strong .fst) p
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
preserves-strong-epis→strong-projective {P = P} hom-epi {X} {Y} e e-strong p =
  epi→surjective (el! (Hom P X)) (el! (Hom P Y))
    (e ∘_) (λ {c} → hom-epi e-strong .fst {c = c}) p

strong-projective→preserves-strong-epis {P = P} pro {X} {Y} {f = f} f-strong =
  surjective→strong-epi (el! (Hom P X)) (el! (Hom P Y)) (f ∘_) $ λ p →
    pro f f-strong p
```
</details>

## Closure of strong projectives

Like projective objects, strong projectives are closed under coproducts
indexed by [[set-projective]] types and retracts.

```agda
indexed-coproduct-strong-projective
  : ∀ {κ} {Idx : Type κ}
  → {P : Idx → Ob} {∐P : Ob} {ι : ∀ i → Hom (P i) ∐P}
  → is-set-projective Idx ℓ
  → (∀ i → is-strong-projective (P i))
  → is-indexed-coproduct C P ι
  → is-strong-projective ∐P

retract→strong-projective
  : ∀ {R P}
  → is-strong-projective P
  → (s : Hom R P)
  → has-retract s
  → is-strong-projective R
```

<details>
<summary>These proofs are more or less identical to the corresponding
ones for projective objects.
</summary>

```agda
indexed-coproduct-strong-projective {P = P} {ι = ι} Idx-pro P-pro coprod {X} {Y} e e-strong p = do
  s ← Idx-pro
    (λ i → Σ[ sᵢ ∈ Hom (P i) X ] (e ∘ sᵢ ≡ p ∘ ι i)) (λ i → hlevel 2)
    (λ i → P-pro i e e-strong (p ∘ ι i))
  pure (match (λ i → s i .fst) , unique₂ (λ i → pullr commute ∙ s i .snd))
  where open is-indexed-coproduct coprod

retract→strong-projective P-pro s r e e-strong p = do
  (t , t-factor) ← P-pro e e-strong (p ∘ r .retract)
  pure (t ∘ s , pulll t-factor ∙ cancelr (r .is-retract))
```

</details>

Moreover, if $\cC$ has a [[zero object]] and a strong projective
coproduct $\coprod_{I} P_i$ indexed by a [[discrete]] type, then
each component of the coproduct is a strong projective.

```agda
zero+indexed-coproduct-strong-projective→strong-projective
  : ∀ {κ} {Idx : Type κ} ⦃ Idx-Discrete : Discrete Idx ⦄
  → {P : Idx → Ob} {∐P : Ob} {ι : ∀ i → Hom (P i) ∐P}
  → Zero C
  → is-indexed-coproduct C P ι
  → is-strong-projective ∐P
  → ∀ i → is-strong-projective (P i)
```

<details>
<summary>Following the general theme, the proof is identical
to the non-strong case.
</summary>

```agda
zero+indexed-coproduct-strong-projective→strong-projective {ι = ι} z coprod ∐P-pro i =
  retract→strong-projective ∐P-pro (ι i) $
  zero→ι-has-retract C coprod z i
```

</details>

## Enough strong projectives

A category $\cC$ is said to have **enough strong projectives** if for
object $X : \cC$ there is some strong epi $P \epi X$ with $P$ strong projective.
We will refer to these projectives as **projective presentations**
of $X$.

Note that there are two variations on this condition: one where
there *merely* exists a strong projective presentation for every $X$, and
another where those presentations are provided as structure. We prefer
to work with the latter, as it tends to be less painful to work with.

```agda
record Strong-projectives : Type (o ⊔ ℓ) where
  field
    Pro : Ob → Ob
    present : ∀ {X} → Hom (Pro X) X
    present-strong-epi : ∀ {X} → is-strong-epi (present {X})
    projective : ∀ {X} → is-strong-projective (Pro X)
```

<!--
```agda
module _ (coprods : (Idx : Set ℓ) → has-coproducts-indexed-by C ∣ Idx ∣)
  where
  open Cat.Diagram.Separator.Strong C coprods
  open Copowers coprods
```
-->

If $\cC$ has set-indexed coproducts, and $P_i$ is a [[strong separating family]]
with each $P_i$ a strong projective, then $\cC$ has enough strong projectives
if $\Sigma(i : Idx) (\cC(P_i, X))$ is a set-projective type.

```agda
  strong-projective-separating-faily→strong-projectives
    : ∀ {Idx : Set ℓ} {Pᵢ : ∣ Idx ∣ → Ob}
    → (∀ X → is-set-projective (Σ[ i ∈ ∣ Idx ∣ ] (Hom (Pᵢ i) X)) ℓ)
    → (∀ i → is-strong-projective (Pᵢ i))
    → is-strong-separating-family Idx Pᵢ
    → Strong-projectives
```

The hypotheses of this theorem basically give the game away: by definition,
there is a strong epimorphism $\coprod_{\Sigma(i : I) \cC(P_i, X)} S_i \to X$
for every $X$. Moreover, $\Sigma(i : I) \cC(P_i, X)$ is set-projective,
so the corresponding coproduct is a strong projective.

```agda
  strong-projective-separating-faily→strong-projectives
    {Idx} {Pᵢ} Idx-pro Pᵢ-pro strong-sep = strong-projectives where
    open Strong-projectives

    strong-projectives : Strong-projectives
    strong-projectives .Pro X = ∐! (Σ[ i ∈ ∣ Idx ∣ ] (Hom (Pᵢ i) X)) (Pᵢ ⊙ fst)
    strong-projectives .present {X = X} =
      ∐!.match (Σ[ i ∈ ∣ Idx ∣ ] (Hom (Pᵢ i) X)) (Pᵢ ⊙ fst) snd
    strong-projectives .present-strong-epi = strong-sep
    strong-projectives .projective {X = X} = indexed-coproduct-strong-projective
      (Idx-pro X) (Pᵢ-pro ⊙ fst)
      (∐!.has-is-ic (Σ[ i ∈ ∣ Idx ∣ ] (Hom (Pᵢ i) X)) (Pᵢ ⊙ fst))
```
