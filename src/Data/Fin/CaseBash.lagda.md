---
description: |
  Case bashing automation.
---
<!--
```agda
open import 1Lab.Type.Pi.Currying
open import 1Lab.Prelude

open import Data.List.Quantifiers
open import Data.List.Membership
open import Data.Fin.Finite
open import Data.Bool.Base
open import Data.List.Base
open import Data.Dec.Base
```
-->
```agda
module Data.Fin.CaseBash where
```

# The case bash tactic

In the 1Lab, we try to strive for the most elegant proofs possible.
Unfortunately, sometimes the most elegant proof really is a giant
proof-by-cases. These proofs are enlightening to read and tedious to
write, and are a prime candidate for proof automation.

Enter `case-bash!`{.Agda}. This tactic walks down a goal like
$(x : A) \to (y : B x) \to \cdots$, and repeatedly case splits
on each [[listable|listing]] type in the domain, and which point it
gathers all of the resulting goals into a dependent list.

Somewhat surprisingly, this can be implemented entirely using instance
arguments! We first use the `Curried`{.Agda} typeclass to gather
all of the arguments into a big Σ type. We then use instance resolution
to try and find a `Listing`{.Agda} of that Σ-type, which
will attempt to resolve `Listing`{.Agda} instances for all of the
components. We then require proofs of the curried codomain for every
single element in the listing of the curried codomain.

```agda
case-bash!
  : ∀ {ℓ ℓd ℓf} {Goal : Type ℓ}
  → ⦃ C : Curried Goal ℓd ℓf ⦄
  → ⦃ ds : Listing (Curried.Dom C) ⦄
  → All (Curried.Cod C) (Listing.univ ds)
  → Goal
```

The type of the function is honestly more complicated then it's
implementation, which just curries and then looks up proofs in a list.

```agda
case-bash! ⦃ C ⦄ ⦃ ds ⦄ proofs =
  Equiv.to (Curried.eqv C) (λ ix → all-∈ proofs (Listing.find ds ix))
```

## Examples

Now that we have our tactic, let's see some examples. The following
bit of code proves commutativity of `and`{.Agda} via `case-bash!`.

```agda
private
  and-comm-via-case-bash : ∀ (x y : Bool) → and x y ≡ and y x
  and-comm-via-case-bash = case-bash! (refl ∷ refl ∷ refl ∷ refl ∷ [])
```

We can avoid writing a giant list of `refl`{.Agda} by using even more proof
automation. The `decide!`{.Agda} tactic lets us use `Dec`{.Agda} instances
to prove goals, and `All`{.Agda} has a `Dec`{.Agda} instance that tries
to decide some predicate for every element of the list. This means that
we can combine `case-bash!`{.Agda} and `decide!`{.Agda} to discharge the
entire list of goals in one go, provided that every goal is decidable.

```agda
private
  and-assoc-via-case-bash : ∀ (x y z : Bool) → and x (and y z) ≡ and (and x y) z
  and-assoc-via-case-bash = case-bash! decide!
```
