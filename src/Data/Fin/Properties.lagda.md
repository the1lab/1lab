```agda
open import 1Lab.Prelude

open import Data.Fin.Base

import Data.Nat as Nat

module Data.Fin.Properties where

```

# Finite Sets - Properties

## Ordering

As noted in [`Data.Fin.Base`], we've set up the ordering on `Fin` so that
we can re-use all the proofs about the ordering on `Nat`{.Agda}.

[`Data.Fin.Base`]: Data.Fin.Base.html

However, there are still quite a few interesting things one can say about
`skip`{.Agda} and `squish`{.Agda}. In particular, we can prove the
*simplicial identities*, which characterize the interactions between
these two functions.

These lemmas might seem somewhat arbitrary and complicated, which
is true! However, they are enough to describe all the possible
interactions of `skip`{.Agda} and `squish`{.Agda}, which in turn
are the building blocks for _every_ monotone function between
`Fin`{.Agda}, so it's not that surprising that they would be a bit
of a mess!

<!-- [TODO: Reed M, 23/02/2022] Link to Simplicial Sets Stuff -->

```agda
skip-comm : ∀ {n} (i j : Fin (suc n)) → i ≤ j
          → ∀ x → skip (weaken i) (skip j x) ≡ skip (fsuc j) (skip i x)
skip-comm fzero    j        le x        = refl
skip-comm (fsuc i) (fsuc j) le fzero    = refl
skip-comm (fsuc i) (fsuc j) le (fsuc x) = ap fsuc (skip-comm i j le x)

drop-comm : ∀ {n} (i j : Fin n) → i ≤ j
          → ∀ x → squish j (squish (weaken i) x) ≡ squish i (squish (fsuc j) x)
drop-comm fzero    fzero    le fzero = refl
drop-comm fzero    fzero    le (fsuc x) = refl
drop-comm fzero    (fsuc j) le fzero = refl
drop-comm fzero    (fsuc j) le (fsuc x) = refl
drop-comm (fsuc i) (fsuc j) le fzero = refl
drop-comm (fsuc i) (fsuc j) le (fsuc x) = ap fsuc (drop-comm i j le x)

squish-skip-comm : ∀ {n} (i : Fin (suc n)) (j : Fin n) → i < fsuc j
                 → ∀ x → squish (fsuc j) (skip (weaken i) x) ≡ skip i (squish j x)
squish-skip-comm fzero j le x = refl
squish-skip-comm (fsuc i) (fsuc j) le fzero = refl
squish-skip-comm (fsuc i) (fsuc j) le (fsuc x) = ap fsuc (squish-skip-comm i j le x)

squish-skip : ∀ {n} (i j : Fin n) → i ≡ j
            → ∀ x → squish j (skip (weaken j) x) ≡ x
squish-skip fzero fzero p x = refl
squish-skip fzero (fsuc j) p x = absurd (fzero≠fsuc p)
squish-skip (fsuc i) fzero p x = refl
squish-skip (fsuc i) (fsuc j) p fzero = refl
squish-skip (fsuc i) (fsuc j) p (fsuc x) = ap fsuc (squish-skip i j (fsuc-inj p) x)

squish-skip-fsuc : ∀ {n} (i : Fin (suc n)) (j : Fin n) → i ≡ fsuc j
                 → ∀ x → squish j (skip i x) ≡ x
squish-skip-fsuc fzero fzero p x = refl
squish-skip-fsuc fzero (fsuc j) p x = absurd (fzero≠fsuc p)
squish-skip-fsuc (fsuc i) fzero p fzero = refl
squish-skip-fsuc (fsuc fzero) fzero p (fsuc x) = refl
squish-skip-fsuc (fsuc (fsuc i)) fzero p (fsuc x) =
  absurd (fzero≠fsuc (fsuc-inj (sym p)))
squish-skip-fsuc (fsuc i) (fsuc j) p fzero = refl
squish-skip-fsuc (fsuc i) (fsuc j) p (fsuc x) =
  ap fsuc (squish-skip-fsuc i j (fsuc-inj p) x)
```

