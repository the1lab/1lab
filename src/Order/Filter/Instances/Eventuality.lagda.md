---
description: |
  Eventuality filters.
---

<!--
```agda
open import Cat.Prelude

open import Data.Power using (ℙ)

open import Order.Instances.Pointwise.Diagrams
open import Order.Instances.Pointwise
open import Order.Semilattice.Meet
open import Order.Directed
open import Order.Filter
open import Order.Base
```
-->

```agda
module Order.Filter.Instances.Eventuality where
```

# Eventuality filters

When working with sequences $\NN \to X$, it is common to find predicates
that are true on almost every element of the sequence, but fail on a finite
number of counterexamples. Mathematicians typically call such predicates or
"almost always" or "eventually true" in the sequence.

As a concrete example, recall that a sequence $x_n : \NN \to \RR$ converges
to some $x : \RR$ if for every $0 < \eps$, there exists some $n_0 : \NN$ such that
for every further $n \geq n_0$, we have $| x - x_n | < \eps$. Ignoring constructivity concerns
for the moment, can re-phrase this definition in the language of
eventually true predicates by observing that a sequence converges if and only
if there are a finite number of $x_i$ where $| x - x_i | \geq \eps$.
In other words, a sequence converges if and only if the predicate
$\lambda x_i.\ | x - x_i| < \eps : \RR \to \Omega$ is eventually true in the sequence $x_n$.

Intuitively, for a fixed sequence $x_n : \NN \to X$ in a type $X$, we ought to
think about the subsets $A \subseteq X$ where $x \in A$ is eventually true in $x_n$
as somehow being "large" subsets of $X$. We can make this intuition precise by showing
that this collection of subsets forms a [[filter]] on the power set of $X$.

However, we must first address the constructivity concerns that we previously
ignored. There are two main problems that we must address:

1. our definition of eventually true involves negation, which is a constructive
   red flag; and
2. restricting ourselves to [[natural number]]-indexed sequences will cause
   problems with countable [[choice|axiom-of-choice]] later down the line[^2].

[^2]: There are other topological reasons to generalize beyond sequences, but the
  the topological content of constructive logic means that these problems with sequences
  have the same root cause. Similar situations arise when looking at $\omega$-CPOs and
  [[DCPOs]], so this pattern of "sequences do not suffice" is common enough to make
  it worth avoiding from the get-go.


We can resolve this first issue by replacing our definition of "$\phi$ is eventually
always true in $x_n$" with one that directly copies the structure of
sequential convergence, EG:

$$
\exists (n_0 : \NN). \forall (n : \NN). n \geq n_0 \to \varphi(x_n)
$$

To solve the second issue, we can generalize from sequences to **nets**.

:::{.definition #net-in-a-type}
A **net** in a type $X$ consists of a function $D \to X$ from a
[[upwards directed set]] $D$.
:::

The natural numbers are upwards directed with respect to their canonical ordering,
so every sequence $x_n : \NN \to X$ gives rise to a net in $X$.

<!--
```agda
module _ {od ℓd ℓx} {D : Poset od ℓd} {X : Type ℓx} (D-directed : is-upwards-directed D) where
  private
    module D where
      open Poset D public
      open is-upwards-directed D-directed public

  open Filter
  open is-filter-base
```
-->

With these pieces in place, we can now define the **eventuality filter** of a net.

:::{.definition #eventuality-filter}
The **eventuality filter** of a net $f : D \to X$ is the filter $\lozenge \square f \subseteq \mathcal{P}(X)$
defined as:

$$
A \in \lozenge \square f := \exists (i : D).\ \forall (j : D).\ i \leq j \to f(j) \in A
$$

In more intuitive terms, $A$ is in the eventuality filter of $f$ if it eventually always
lies within the image of $f$.
:::

```agda
  Eventuality : (⌞ D ⌟ → X) → Filter (Subsets X)
  Eventuality f .F .hom A = elΩ (Σ[ i ∈ ⌞ D ⌟ ] (∀ (j : ⌞ D ⌟) → i D.≤ j → f j ∈ A))
  Eventuality f .F .pres-≤ A⊆B = rec! λ i □A → inc (i , λ j i≤j → A⊆B (f j) (□A j i≤j))
```

The posets of subsets is a meet semilattice, so it suffices to show that
$\lozenge \square f : \mathcal{P}(X) \to \Omega$ is a meet semilattice homomorphism.

First, note that $X \in \lozenge \square f$ if and only if $D$ is inhabited, as
the image of $f$ always lies within $f$, and $D$ is inhabited by definition.

Next, suppose that $A, B \in \lozenge \square f$. By definition, this means
that there exists some $i$ and $j$ such that for all $i \leq i', j \leq j'$,
$f(i') \in A$ and $f(j') \in B$, resp.

Additionally, $D$ is directed, so there merely exists some upper bound $i \leq k \geq j$.
Finally, for every $k \leq l$, $f(l) \in A \cap B$, as $i \leq k \leq l$ and $j \leq k \leq l$.

```agda
  Eventuality f .has-is-filter =
    is-meet-slat-hom→is-filter Subsets-is-meet-slat record
      { top-≤ = λ _ →
        case D.inhab of λ where
          i → inc (i , λ _ _ → tt)
      ; ∩-≤ = elim! λ A B i □A j □B →
        case D.upper-bound i j of λ where
          k i≤k j≤k →
            inc (k , λ l k≤l → □A l (D.≤-trans i≤k k≤l) , □B l (D.≤-trans j≤k k≤l))
      }
```

## Filter bases of the eventuality filter

:::{.definition #tail-of-a-net}
A **tail** of a net $f : D \to X$ at some $i : D$ is set of all $x : X$
that lie in the image of some $j$ with $i \leq j$[^3].
:::

[^3]: More abstractly, the tails of a net $f$ are the [[left kan extensions]]
  of the hom functor $i \leq - : D \to \Omega$ along the monotone map $f : D \to \mathrm{Codisc}(X)$.


```agda
  Tail : (⌞ D ⌟ → X) → ⌞ D ⌟ → ℙ X
  Tail f i x = elΩ (Σ[ j ∈ D ] i D.≤ j × f j ≡ x)
```

The tails of $f$ form a [[filter base]] for the eventuality filter.

```agda
  Tails-is-filter-base : {f : ⌞ D ⌟ → X} → is-filter-base (Eventuality f) (Tail f)
  Tails-is-filter-base .base∈F i =
    pure (i , λ j i≤j → pure (j , i≤j , refl))
  Tails-is-filter-base .up-closed A =
    elim! λ i i≤j→f[j]∈A →
      pure (i , λ x → rec! (λ j i≤j fj=x → subst (_∈ A) fj=x (i≤j→f[j]∈A j i≤j)))
```
