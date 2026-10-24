---
description: |
    We show that the universe of n-types is not an n-type for n equal to
    2 and 3.
---
<!--
```agda
open import 1Lab.HLevel.Universe
open import 1Lab.HLevel.Closure
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

open import Data.Bool

open import Homotopy.Space.Circle
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

We are about to make use of `Bool`{.Agda}, the type of booleans. Since
it is only defined for the bottom level universe, we will
[[lift|1Lab.Type.html#lifting]] it as needed.

Together with its proof of being a homotopy set, (the lifting of)
`Bool`{.Agda} lives in the universe of all homotopy sets as a pair
`set-Bool`{.Agda}.

```agda
private
  variable
    ℓ : Level

  set-Bool : n-Type ℓ 2
  set-Bool {ℓ} = el (Lift ℓ Bool) (hlevel 2)
```

Since `true`{.Agda} and `false`{.Agda} are distinct, so are the two
equivalences on (the lifting of) `Bool`.{.Agda} given by the identity
function and negation respectively.

```agda
  Lift-true≠false : ¬_ {ℓ} (lift true ≡ lift false)
  Lift-true≠false = true≠false ∘ ap (fst (Lift-≃))

  Lift-id≠not : ¬ id≃ ≡ Lift-ap {ℓ' = ℓ} not≃
  Lift-id≠not = Lift-true≠false ∘ ap λ f → fst f (lift true)
```

We now assume the universe of all homotopy sets to also be a homotopy
set, aiming for a contradiction. By definition of homotopy set, the path
type from `set-Bool`{.Agda} to itself would be a proposition. Now, in
such a homotopy universe, univalence guarantees this path type to be
equivalent to the type of equivalences on `Bool`{.Agda}. Because
homotopy levels are preserved by equivalences, the type of equivalances
from `Bool`{.Agda} to itself would then also be a proposition. We would
therefore have a path from the identity to negation. This contradicts
our previous observation.

```agda
¬is-set-Set : ¬ is-set (Set ℓ)
¬is-set-Set h =
  let
    k = h set-Bool set-Bool
    Lift-id≡not = (Equiv→is-hlevel 1 n-univalence k) id≃ (Lift-ap not≃)
  in Lift-id≠not Lift-id≡not
```

## The universe of homotopy groupoids is not a homotopy groupoid
