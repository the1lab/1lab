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

:::{.definition #net-in-a-type}
A **net** in a type $X$ consists of a function $D \to X$ from a
[[upwards directed set]] $D$.
:::

```agda
record Net {od ℓd ℓx} (D : Poset od ℓd) (X : Type ℓx) : Type (od ⊔ ℓd ⊔ ℓx) where
  no-eta-equality
  field
    net : ⌞ D ⌟ → X
    dom-directed : is-upwards-directed D
```

<!--
```agda
  open is-upwards-directed dom-directed renaming
    ( inhab to dom-inhab
    ; upper-bound to dom-upper-bound
    )
    public
```
-->


<!--
```agda
module _ {od ℓd ℓx} {D : Poset od ℓd} {X : Type ℓx} where
  private
    module D = Poset D
  open Filter
  open is-filter-base

  instance
    Funlike-Net : Funlike (Net D X) ⌞ D ⌟ λ _ → X
    Funlike-Net .Funlike._·_ = Net.net
```
-->

Nets are a generalization of sequences $\NN \to X$ that tend to be better
behaved both constructively and topologically. Every net presents
a filter known as its **eventuality filter**.

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
  Eventuality : Net D X → Filter (Subsets X)
  Eventuality f .F .hom A = elΩ (Σ[ i ∈ ⌞ D ⌟ ] (∀ (j : ⌞ D ⌟) → i D.≤ j → f · j ∈ A))
  Eventuality f .F .pres-≤ A⊆B = rec! λ i □A → inc (i , λ j i≤j → A⊆B (f · j) (□A j i≤j))
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
    is-meet-slat-hom→is-filter Subsets-is-meet-slat
    $ record
      { top-≤ = λ _ →
        case f.dom-inhab of λ where
          i → inc (i , λ _ _ → tt)
      ; ∩-≤ = elim! λ A B i □A j □B →
        case f.dom-upper-bound i j of λ where
          k i≤k j≤k →
            inc (k , λ l k≤l → □A l (D.≤-trans i≤k k≤l) , □B l (D.≤-trans j≤k k≤l))
      }
    where
      module f = Net f
      open is-meet-slat-hom
```

## Filter bases of the eventuality filter

:::{.definition #tail-of-a-net}
A **tail** of a net $f : D \to X$ at some $i : D$ is set of all $x : X$
that lie in the image of some $j$ with $i \leq j$[^1].
:::

[^1]: More abstractly, the tails of a net $f$ are the [[left kan extensions]]
  of the hom functor $i \leq - : D \to \Omega$ along the monotone map $f : D \to \mathrm{Codisc}(X)$.

```agda
  Tail : (f : Net D X) → ⌞ D ⌟ → ℙ X
  Tail f i x = elΩ (Σ[ j ∈ D ] (i D.≤ j) × f · j ≡ x)
```

The tails of $f$ form a [[filter base]] for the eventuality filter.

```agda
  Tails-is-filter-base : {f : Net D X} → is-filter-base (Eventuality f) (Tail f)
  Tails-is-filter-base .base∈F i =
    pure (i , (λ j i≤j → pure (j , i≤j , refl)))
  Tails-is-filter-base .up-closed A =
    elim! λ i i≤j→f[j]∈A →
      pure (i , λ x → rec! (λ j i≤j fj=x → subst (_∈ A) fj=x (i≤j→f[j]∈A j i≤j)))
```
