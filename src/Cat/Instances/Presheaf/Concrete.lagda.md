<!--
```agda
open import Cat.Functor.FullSubcategory
open import Cat.Diagram.Terminal
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Reasoning

open Precategory
open Functor
```
-->

```agda
module Cat.Instances.Presheaf.Concrete
  {ℓ} (C : Precategory ℓ ℓ) (top : Terminal C)
  where
```

<!--
```agda
private
  module C = Cat.Reasoning C

open Terminal top renaming (top to pt)
```
-->

# Concrete presheaves {defines="concrete-presheaf concrete-object diffeological-space"}

Among the generalized spaces of a gros topos, some — but far from
all! — are determined by their honest *points*: a presheaf $X$ on a
category of probes with terminal probe $\rm{pt}$ is **concrete** when
a plot $x \in X(U)$ is determined by the function it induces from the
points of $U$ to the points of $X$,

$$
X(U) \mono \hom_{\Sets}\big(\hom(\rm{pt}, U),\ X(\rm{pt})\big).
$$

For the site of smooth probes this carves out exactly the
*diffeological spaces* among the smooth sets — and the classifying
smooth sets of differential forms are the standard examples of
non-concrete smooth sets, spaces with a single point but many plots.

The comparison map sends a plot to its evaluation on points; it is
the unit of the $\Gamma \dashv \rm{Codisc}$ adjunction of the
[[cohesive structure|cohesive-topos]] of the topos.

```agda
is-concrete : ⌞ PSh ℓ C ⌟ → Type ℓ
is-concrete X =
  ∀ U → injective λ (x : ∣ X .F₀ U ∣) (p : C.Hom pt U) → X .F₁ p x
```

Concreteness is a property, not structure, so the concrete presheaves
form a full subcategory — for the smooth site, the category of
diffeological spaces inside smooth sets, the paper's (12).

```agda
abstract
  is-concrete-is-prop : ∀ X → is-prop (is-concrete X)
  is-concrete-is-prop X p q i U inj =
    X .F₀ U .is-tr _ _ (p U inj) (q U inj) i

Concrete : Precategory (lsuc ℓ) ℓ
Concrete = Restrict {C = PSh ℓ C} is-concrete
```
