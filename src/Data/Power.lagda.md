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
into the universe of `propositional types`{.Agda ident=n-Type}. Since
the universe of all $n$-types is a $(n+1)$-type (by
`n-Type-is-hlevel`{.Agda}), and function types have the same h-level as
their codomain (by `fun-is-hlevel`{.Agda}), the power set of a type $X$ is
always `a set`{.Agda ident=is-set}. We denote the power set of $X$ by
$\bb{P}(X)$.

```agda
ℙ : Type ℓ → Type (lsuc ℓ)
ℙ X = X → n-Type _ 1

ℙ-is-set : is-set (ℙ X)
ℙ-is-set = hlevel 2
```

The **membership** relation is defined by applying the predicate and
projecting the underlying type of the proposition: We say that $x$ is an
element of $P$ if $P(x)$ is inhabited.

```agda
_∈_ : X → ℙ X → Type _
x ∈ P = ∣ P x ∣
```

The **subset** relation is defined as is done traditionally: If $x \in
X$ implies $x \in Y$, for $X, Y : \bb{P}(T)$, then $X \subseteq Y$.

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
  n-ua {n = 1} (prop-ext (A x .is-tr) (B x .is-tr) (A⊆B x) (B⊂A x))
```

## Lattice Structure

The type $\bb{P}(X)$ has a lattice structure, with the order given
by `subset inclusion`{.Agda ident=_⊆_}. We call the meets
**`intersections`{.Agda ident=_∩_}** and the joins **`unions`{.Agda
ident=_∪_}**.

```agda
maximal : ℙ X
maximal _ = Lift _ ⊤ , λ x y i → lift tt

minimal : ℙ X
minimal _ = Lift _ ⊥ , λ x → absurd (Lift.lower x)

_∩_ : ℙ X → ℙ X → ℙ X
(A ∩ B) x = (∣ A x ∣ × ∣ B x ∣) , ×-is-hlevel 1 (A x .is-tr) (B x .is-tr)
```

Note that in the definition of `union`{.Agda ident=_∪_}, we must
`truncate`{.Agda ident=∥_∥} the `coproduct`{.Agda ident=⊎}, since there
is nothing which guarantees that A and B are disjoint subsets.

```agda
_∪_ : ℙ X → ℙ X → ℙ X
(A ∪ B) x = ∥ ∣ A x ∣ ⊎ ∣ B x ∣ ∥ , squash
```
