```agda
open import 1Lab.Prelude

open import Data.Sum

module Data.Power where
```

<!--
```agda
private variable
  ℓ : Level
  X : Type ℓ
```
-->

# Power Sets

The **power set** of a type $X$ is the collection of all maps from $X$
into the universe of `propositional types`{.Agda ident=nType}. Since
the universe of all $n$-types is a $(n+1)$-type (by
`isHLevel-nType`{.Agda}), and function types have the same h-level as
their codomain (by `isHLevel→`{.Agda}), the power set of a type $X$ is
always `a set`{.Agda ident=isSet}. We denote the power set of $X$ by
$\mathbb{P}(X)$.

```agda
ℙ : Type ℓ → Type (lsuc ℓ)
ℙ X = X → nType _ 1

isSet-ℙ : isSet (ℙ X)
isSet-ℙ = isHLevel→ 2 (isHLevel-nType 1)
```

The **membership** relation is defined by applying the predicate and
projecting the underlying type of the proposition: We say that $x$ is an
element of $P$ if $P(x)$ is inhabited.

```agda
_∈_ : X → ℙ X → Type _
x ∈ P = fst (P x)
```

The **subset** relation is defined as is done traditionally: If $x \in
X$ implies $x \in Y$, for $X, Y : \mathbb{P}(T)$, then $X \subseteq Y$.

```agda
_⊆_ : ℙ X → ℙ X → Type _
X ⊆ Y = ∀ x → x ∈ X → x ∈ Y
```

By function and propositional extensionality, two subsets of $X$ are
equal when they contain the same elements, i.e., they assign identical
propositions to each inhabitant of $X$.

```agda
ℙ-ext : {A B : ℙ X}
      → A ⊆ B → B ⊆ A → A ≡ B
ℙ-ext {A = A} {B = B} A⊆B B⊂A = funext λ x →
  nType-ua {n = 1} (propExt (A x .snd) (B x .snd) (A⊆B x) (B⊂A x))
```

## Lattice Structure

The type $\mathbb{P}(X)$ has a lattice structure, with the order given
by `subset inclusion`{.Agda ident=_⊆_}. We call the meets
**`intersections`{.Agda ident=_∩_}** and the joins **`unions`{.Agda
ident=_∪_}**.

```agda
maximal : ℙ X
maximal _ = Lift _ ⊤ , λ x y i → lift tt

minimal : ℙ X
minimal _ = Lift _ ⊥ , λ x → absurd (Lift.lower x)

_∩_ : ℙ X → ℙ X → ℙ X
(A ∩ B) x = (A x .fst × B x .fst) , isHLevel× 1 (A x .snd) (B x .snd)
```

Note that in the definition of `union`{.Agda ident=_∪_}, we must
`truncate`{.Agda ident=∥_∥} the `coproduct`{.Agda ident=⊎}, since there
is nothing which guarantees that A and B are disjoint subsets.

```agda
_∪_ : ℙ X → ℙ X → ℙ X
(A ∪ B) x = ∥ A x .fst ⊎ B x .fst ∥ , squash
```
