---
description: |
    We show that the universe of n-types is not an n-type for n equal to
    2 and 3.
---
<!--
```agda
open import 1Lab.HLevel.Universe
open import 1Lab.HLevel.Closure
open import 1Lab.Equiv
open import 1Lab.HLevel
open import 1Lab.Path
open import 1Lab.Type

open import Homotopy.Space.Circle

open import Data.Bool
```
-->

```agda
module 1Lab.Counterexamples.HLevel.Universes where
```

# Universes of n-types which are not, themselves, n-types

Recall that, as we have observed when discussing
[universes of n-types], the universe of $n$-types of level $ℓ$ is an
$(n + 1)$-type in $1 + ℓ$. We now show that, neither for $n = 2$ nor for
$n = 3$, said universes live in lower homotopy levels.

[universes of n-types]: 1Lab.HLevel.Universe.html

## The universe of homotopy sets is not a homotopy set

Consider `Bool`{.Agda}, the type of booleans. We know it to be a
homotopy set, but not a proposition, since `true`{.Agda} is distinct
from `false`{.Agda}.

```agda
private
  set-Bool : n-Type lzero 2
  set-Bool = el Bool (hlevel 2)

  ¬is-prop-Bool : ¬ is-prop Bool
  ¬is-prop-Bool h = true≠false (h true false)
```

As a consequence, the type of equivalences on `Bool`{.Agda}, which is
equivalent to `Bool`{.Agda} itself, is not a proposition, either.

```agda
  Bool-automorphisms⁻¹ : Bool ≃ (Bool ≃ Bool)
  Bool-automorphisms⁻¹ = Equiv.inverse Bool-automorphisms

  ¬is-prop-Bool≃Bool : ¬ is-prop (Bool ≃ Bool)
  ¬is-prop-Bool≃Bool = ¬is-prop-Bool ∘ Equiv→is-hlevel 1 Bool-automorphisms⁻¹
```

We assume the universe of all homotopy sets to also be a homotopy set
and get to a contradiction. By definition of homotopy set, the path type
from `Bool`{.Agda} (equipped with the proof of it being a homotopy set)
to itself would be a proposition. Now, in such a homotopy universe,
univalence guarantees this path type to be equivalent to the type of
equivalences on `Bool`{.Agda}. Because homotopy levels are preserved by
equivalences, the type of equivalances from `Bool`{.Agda} to itself
would then also be a proposition. This contradicts our previous
observation.

```agda
¬is-set-Set : ¬ is-set (Set lzero)
¬is-set-Set h = let k = h set-Bool set-Bool
  in ¬is-prop-Bool≃Bool (Equiv→is-hlevel 1 n-univalence k)
```

## The universe of homotopy groupoids is not a homotopy groupoid
