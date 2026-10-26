---
description: |
    We show that the universe of n-types is not an n-type for n equal to
    2 and 3.
---
<!--
```agda
open import 1Lab.Reflection.HLevel
open import 1Lab.HLevel.Universe
open import 1Lab.HLevel.Closure
open import 1Lab.Type.Sigma
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

  id≠not : ¬ id≃ ≡ Lift-ap {ℓ' = ℓ} not≃
  id≠not = Lift-true≠false ∘ ap λ f → fst f (lift true)
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
¬is-set-Set is-set-Set =
  let
    h = is-set-Set set-Bool set-Bool
    id≡not = Equiv→is-hlevel 1 n-univalence h id≃ (Lift-ap not≃)
  in id≠not id≡not
```

We also prove the weaker statement from example 3.1.9, which only
concerns the type universe. Again, we make it parametric in an arbitrary
universe level.

```agda
¬is-set-Type : ¬ is-set (Type ℓ)
¬is-set-Type {ℓ} is-set-Type =
  let
    k = is-set-Type (Lift ℓ Bool) (Lift ℓ Bool)
    Equiv≃Path = Equiv.inverse (Iso→Equiv Path≃Equiv)
    id≡not = Equiv→is-hlevel 1 Equiv≃Path k id≃ (Lift-ap not≃)
  in id≠not id≡not
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
that the type of equivalences on `S¹`{.Agda} is not a homotopy set.
First, we lift the construction of `always-loop`{.Agda}, which we know
not to be `refl`{.Agda} at any input.

```agda
  Lift-always-loop : (x : Lift ℓ S¹) → x ≡ x
  Lift-always-loop (lift x) = ap lift (always-loop x)
```

We use it construct a loop around the identity on `S¹`{.Agda} regarded
as an [equivalence].

[equivalence]: 1Lab.Equiv.html#equivalences-proper

```agda
  id≃-loop : id≃ {A = Lift ℓ S¹} ≡ id≃
  id≃-loop = Σ-prop-path is-equiv-is-prop (funext Lift-always-loop)
```

To prove that, `Lift-always-loop`{.Agda} and `refl`{.Agda} do not agree
on any input, we lift the proof seen in [[circle]].

```agda
  Lift-parity : _≡_ {ℓ} (lift base) (lift base) → Bool
  Lift-parity l =
    let
      p = ap (fst Lift-≃) l
    in subst möbius p true

  Lift-refl≠loop : refl {ℓ} ≠ ap lift loop
  Lift-refl≠loop p = true≠false (ap Lift-parity p)

  Lift-never-refl : (x : S¹) → Lift-always-loop {ℓ} (lift x) ≠ refl
  Lift-never-refl = S¹-elim (Lift-refl≠loop ∘ sym) prop!
```

We now prove `id≃-loop`{.Agda} to be distinct from `refl`. If the two
were equal, moving to the first component of the $\Sigma$-type
`_≃_`{.Agda} and then to homotopies, `Lift-always-loop`{.Agda} would
coincide with `id`{.Agda}. In particular, by evaluating both functions
to `lift base`{.Agda}, we would contradict `Lift-never-refl`{.Agda}. So
`id≃-loop`{.Agda} must be distinct from `refl`{.Agda}.

```agda
  refl≠id≃-loop : id≃-loop {ℓ} ≠ refl
  refl≠id≃-loop h =
    let
      fst-path = fst (Equiv.inverse Σ-pathp≃)
      base-path p = happly p (lift base)
      refl-at-base = ap (base-path ∘ fst ∘ fst-path) h
    in Lift-never-refl base refl-at-base
```

We can now use the circle to refute the idea that the universe of all
homotopy groupoids is a homotopy groupoid. Assume it is. Then, in
particular, the loop space on `S¹`{.Agda} would be a homotopy set. By
univalence for homotopy sets, and because equivalences respect homotopy
levels, so would the type of equivalences on `S¹`{.Agda}. In particular,
the loop space on the equivalence on `S¹`{.Agda} given by the identity
would be a proposition. Thus, `id≃-loop`{.Agda} would have to coincide
with `refl`. This contradicts our observation above.

```agda
¬is-groupoid-Groupoid : ¬ is-hlevel (n-Type ℓ 3) 3
¬is-groupoid-Groupoid {ℓ} h =
  let
    k = h groupoid-S¹ groupoid-S¹
    is-set-S¹≃S^1 = Equiv→is-hlevel 2 n-univalence k
    is-prop-id≃≡id≃ = is-set-S¹≃S^1 id≃ id≃
    id≃-loop≡refl = is-prop-id≃≡id≃ id≃-loop refl
  in refl≠id≃-loop id≃-loop≡refl
```

### Necessity of Higher Inductive Types

On top of [[univalence]], this last proof makes use of an higher
inductive type. In the absence of these, [-@Kraus:higher] explains in
section §6 that it should be possible to construct a model where, for
every $n \geq 0$, every type in the universe at level $n$ is $(n +
2)$-truncated. As a consequence, the bottom universe would then be a
homotopy groupoid, and so would any homotopy universe in it.
