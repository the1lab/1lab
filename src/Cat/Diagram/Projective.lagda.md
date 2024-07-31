---
description: |
  Projective objects.
---
<!--
```agda
open import Cat.Diagram.Coproduct.Indexed
open import Cat.Diagram.Coproduct
open import Cat.Functor.Morphism
open import Cat.Diagram.Initial
open import Cat.Diagram.Zero
open import Cat.Functor.Hom
open import Cat.Groupoid
open import Cat.Prelude

open import Data.Set.Projective
open import Data.Set.Surjection
open import Data.Dec

import Cat.Reasoning
```
-->
```agda
module Cat.Diagram.Projective
  {o ℓ}
  (C : Precategory o ℓ)
  where
```

<!--
```agda
open Cat.Reasoning C
```
-->

# Projective objects

:::{.definition #projective-object alias="projective"}
Let $\cC$ be a precategory. An object $P : \cC$ is **projective**
if for every morphism $p : P \to Y$ and [[epimorphism]] $e : X \epi Y$,
there merely exists a $s : P \to X$ such that $e \circ s = p$, as in the
following diagram:

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

More concisely, $P$ is projective if it has the left-lifting property
relative to epimorphisms in $\cC$.
:::

```agda
is-projective : (P : Ob) → Type _
is-projective P =
  ∀ {X Y} (p : Hom P Y) (e : X ↠ Y)
  → ∃[ s ∈ Hom P X ] (e .mor ∘ s ≡ p)
```

If we take the perspective of generalized elements, then a projective
object $P$ lets us pick a $P$-element of $X$ from the preimage $e^{-1}(y)$
of a $P$-element $y : Y$ along every $e : X \epi Y$. This endows $\cC$ with
an internal $P$-relative version of the [[axiom of choice]].

This intuition can be made more precise by noticing that every
object of $\cC$ is projective if and only if every epimorphism (merely)
splits. For the forward direction, let $e : X \epi Y$ have a section
$s : Y \to X$, and note that $s \circ p$ factorizes $p$ through $e$.

```agda
epis-split→all-projective
  : (∀ {X Y} → (e : X ↠ Y) → ∥ has-section (e .mor) ∥)
  → ∀ {P} → is-projective P
epis-split→all-projective epi-split p e = do
  s ← epi-split e
  pure (s .section ∘ p , cancell (s .is-section))
  where open has-section
```

Conversely, given an epi $X \epi Y$, we can factorize $\id : Y \to Y$
to get our desired section $s : Y \to X$.

```agda
all-projective→epis-split
  : (∀ {P} → is-projective P)
  → ∀ {X Y} → (e : X ↠ Y) → ∥ has-section (e .mor) ∥
all-projective→epis-split pro e = do
  (s , p) ← pro id e
  pure (make-section s p)
```

This suggests that projective objects are quite hard to come by
in constructive foundations! For the most part, this is true:
constructively, the category of sets has very few projectives[^1], and
many categories inherit their epimorphisms from $\Sets$. However,
it is still possible to have projectives if epis in $\cC$ are extremely
structured, or there are very few maps out of some $P$.

[^1]: In fact, it is consistent that [the only projective sets are the finite sets]!

[the only projective sets are the finite sets]: Data.Set.Projective.html#taboos

<!-- [TODO: Reed M, 26/07/2024]
  Link to stuff about projective modules when that gets written.
-->

For instance, observe that every epi splits in a [[pregroupoid]],
so every every object in a pregroupoid must be projective.

```agda
pregroupoid→all-projective
  : is-pregroupoid C
  → ∀ {P} → is-projective P
pregroupoid→all-projective pregroupoid =
  epis-split→all-projective λ e →
    pure (invertible→to-has-section (pregroupoid (e .mor)))
```

Likewise, if $\cC$ has an [[initial object]] $\bot : \cC$, then
$\bot$ is projective, as there is a unique map out of $\bot$.

```agda
module _ (initial : Initial C) where
  open Initial initial

  initial-projective : is-projective bot
  initial-projective p e = pure (¡ , ¡-unique₂ (e .mor ∘ ¡) p)
```

## A functorial definition

Some authors prefer to define projective objects via a functorial
approach. In particular, an object $P : \cC$ is projective if and only
if the $\hom$-functor $\cC(P,-)$ preserves epimorphisms.

For the forward direction, recall that in $\Sets$, [[epis are surjective]].
This means that if $e : X \epi Y$ is an epi in $\cC$, then
$e \circ - : \cC(P,X) \to \cC(P,Y)$ is surjective, as $\cC(P,-)$ preserves
epis. This directly gives us the factorization we need!

```agda
preserves-epis→projective
  : ∀ {P}
  → preserves-epis (Hom-from C P)
  → is-projective P
preserves-epis→projective {P = P} hom-epi {X = X} {Y = Y} p e =
  epi→surjective (el! (Hom P X)) (el! (Hom P Y))
    (e .mor ∘_)
    (λ {c} → hom-epi (e .epic) {c = c})
    p
```

For the reverse direciton, let $P$ be projective, $f : X \epi Y$ be an epi,
and $g, h : \cC(P, X) \to A$ be a pair of functions into an arbitrary
set $A$ such that $g(f \circ s) = h(f \circ s)$ for any $s : \cC(P, X)$.
To show that $\cC(P,-)$ preserves epis, we must show that $g = h$, which
follows directly from the existence of a lift for every $\cC(P,X)$.

```agda
projective→preserves-epis
  : ∀ {P}
  → is-projective P
  → preserves-epis (Hom-from C P)
projective→preserves-epis pro {f = f} f-epi g h p =
  ext λ k →
    rec!
      (λ s s-section →
        g k       ≡˘⟨ ap g s-section ⟩
        g (f ∘ s) ≡⟨ p $ₚ s ⟩
        h (f ∘ s) ≡⟨ ap h s-section ⟩
        h k       ∎)
      (pro k (record { epic = f-epi }))
```

## Closure of projectives

Projective objects are equipped with a mapping-out property, so they
tend to interact nicely with other constructions that also have a
mapping-out property. For instance, f $P$ and $Q$ are both projective,
then their [[coproduct]] $P + Q$ is projective (if it exists).

```agda
coproduct-projective
  : ∀ {P Q P+Q} {ι₁ : Hom P P+Q} {ι₂ : Hom Q P+Q}
  → is-projective P
  → is-projective Q
  → is-coproduct C ι₁ ι₂
  → is-projective P+Q
coproduct-projective {ι₁ = ι₁} {ι₂ = ι₂} P-pro Q-pro coprod p e = do
  (s₁ , s₁-factor) ← P-pro (p ∘ ι₁) e
  (s₂ , s₂-factor) ← Q-pro (p ∘ ι₂) e
  pure $
    [ s₁ , s₂ ] ,
    unique₂
      (pullr []∘ι₁ ∙ s₁-factor) (pullr []∘ι₂ ∙ s₂-factor)
      refl refl
  where open is-coproduct coprod
```

We can extend this result to [[indexed coproducts]], provided that
the indexing type is [[set projective]].

```agda
indexed-coproduct-projective
  : ∀ {κ} {Idx : Type κ}
  → {P : Idx → Ob} {∐P : Ob} {ι : ∀ i → Hom (P i) ∐P}
  → is-set-projective Idx ℓ
  → (∀ i → is-projective (P i))
  → is-indexed-coproduct C P ι
  → is-projective ∐P
indexed-coproduct-projective {P = P} {ι = ι} Idx-pro P-pro coprod {X = X} {Y = Y} p e = do
  s ← Idx-pro
        (λ i → Σ[ sᵢ ∈ Hom (P i) X ] (e .mor ∘ sᵢ ≡ p ∘ ι i)) (λ i → hlevel 2)
        (λ i → P-pro i (p ∘ ι i) e)
  pure (match (λ i → s i .fst) , unique₂ (λ i → pullr commute ∙ s i .snd))
  where open is-indexed-coproduct coprod
```

Note that this projectivity requirement is required: if projective objects
were closed under arbitrary coproducts, then we would immediately be able
to prove the [[axiom of choice]]: the singleton set is both a projective
object and a [[dense separator]] in $\Sets$, so closure under arbitrary
coproducts would mean that every set is projective, which is precisely
the axiom of choice.

Putting coproducts aside for a moment, note that projectives are closed
under retracts. This follows by a straightforward bit of algebra.

```agda
retract→projective
  : ∀ {R P}
  → is-projective P
  → (s : Hom R P)
  → has-retract s
  → is-projective R
retract→projective P-pro s r p e = do
  (t , t-factor) ← P-pro (p ∘ r .retract) e
  pure (t ∘ s , pulll t-factor ∙ cancelr (r .is-retract))
```

A nice consequence of this is that if $\cC$ has a [[zero object]] and
a projective coproduct $\coprod_{I} P_i$ indexed by a [[discrete]] type,
then each component of the coproduct is also projective.

```agda
zero+indexed-coproduct-projective→projective
  : ∀ {κ} {Idx : Type κ} ⦃ Idx-Discrete : Discrete Idx ⦄
  → {P : Idx → Ob} {∐P : Ob} {ι : ∀ i → Hom (P i) ∐P}
  → Zero C
  → is-indexed-coproduct C P ι
  → is-projective ∐P
  → ∀ i → is-projective (P i)
```

This follows immediately from the fact that if $\cC$ has a zero object
and $\coprod_{I} P_i$ is indexed by a discrete type, then each coproduct
inclusion has a retract.

```agda
zero+indexed-coproduct-projective→projective {ι = ι} z coprod ∐P-pro i =
  retract→projective ∐P-pro (ι i) $
  zero→ι-has-retract C coprod z i
```

## Enough projectives

A category $\cC$ is said to have **enough projectives** if for
object $X : \cC$ there is some $P \epi X$ with $P$ projective.
We will refer to these projectives as **projective presentations**
of $X$.

Note that there are two variations on this condition: one where
there *merely* exists a projective presentation for every $X$, and
another where those presentations are provided as structure. We prefer
to work with the latter, as it tends to be less painful to work with.

```agda
record Projectives : Type (o ⊔ ℓ) where
  field
    Pro : Ob → Ob
    present : ∀ {X} → Pro X ↠ X
    projective : ∀ {X} → is-projective (Pro X)
```
