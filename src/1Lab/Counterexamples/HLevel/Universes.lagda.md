---
description: |
    We show that the universe of n-types is not an n-type for n equal to
    2 and 3.
---
<!--
```agda
open import 1Lab.HLevel.Universe
open import 1Lab.HLevel.Closure
open import 1Lab.Univalence
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

In example 3.1.9, [-@HoTT] uses `Bool`{.Agda}, the type of
[[booleans]], to show that [[univalence]] implies that the bottom level
universe of all types is not a homotopy set. This way, one observes that
univalence truly bestows higher structure upon the type universe.
Because `Bool`{.Agda} is, in particular, a homotopy set itself, we can
reuse the same proof strategy to show that not even the universe of
homotopy sets is a homotopy set. Since Mikan's `Bool`{.Agda} is only
defined for the bottom level universe, and we want our proof to be
parametric in a universe level, we will [lift] `Bool`{.Agda} as needed.

[lift]: 1Lab.Type.html#lifting

Together with its proof of being a homotopy set, (the lifting of)
`Bool`{.Agda} lives in the universe of all homotopy sets as a pair
`set-Bool`{.Agda}.

```agda
private
  variable
    ℓ : Level

  set-Bool : Set ℓ
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
    Lift-id≡not = Equiv→is-hlevel 1 n-univalence k id≃ (Lift-ap not≃)
  in Lift-id≠not Lift-id≡not
```

We also prove the weaker statement from example 3.1.9, which only
concerns the type universe. Again, we make it parametric in an arbitrary
universe level.

```agda
¬is-set-Type : ¬ is-set (Type ℓ)
¬is-set-Type {ℓ} h =
  let
    k = h (Lift ℓ Bool) (Lift ℓ Bool)
    Equiv≃Path = Equiv.inverse (Iso→Equiv Path≃Equiv)
    Lift-id≡not = Equiv→is-hlevel 1 Equiv≃Path k id≃ (Lift-ap not≃)
  in Lift-id≠not Lift-id≡not
```

## The universe of homotopy groupoids is not a homotopy groupoid

To prove that the universe of homotopy groupoids is not a homotopy
groupoid, we replace `Bool`{.Agda} from the proof above with
`S¹`{.Agda}, the [[circle]]. Again, we will [lift] it as needed.

[lift]: 1Lab.Type.html#lifting

```agda
private
  groupoid-S¹ : n-Type ℓ 3
  groupoid-S¹ {ℓ} = el (Lift ℓ S¹) (hlevel 3)
```

The crux of the previous proof was showing that there is more than one
equivalence on `Bool`{.Agda}, i.e. the type of equivalences on
`Bool`{.Agda} is not a proposition. Similarly, we will not need to prove
that the type of equivalences on `S¹`{.Agda} is not a homotopy set. This
is more involved. Our proof follows section §2 of [-@Cagne:symmetries].

```agda
{-¬is-groupoid-Groupoid : ¬ is-hlevel (n-Type ℓ 3) 3
¬is-groupoid-Groupoid h =
  let
    k = h groupoid-S¹ groupoid-S¹
  in ?-}
```

## Necessity of Higher Inductive Types

On top of [[univalence]], both proofs above make use of higher inductive
types. In the absence of these, [-@Kraus:higher] explains in section
§6 that it should be possible to construct a model where, for every $n
\geq 0$, every type in the universe at level $n$ is $(n + 2)$-truncated.
As a consequence, the bottom universe would then be a homotopy groupoid,
and so would any homotopy universe in it.
