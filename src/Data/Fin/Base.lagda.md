```agda
open import 1Lab.Prelude

open import Data.Sum

import Data.Nat as Nat

module Data.Fin.Base where
```

# Finite Sets

The type `Fin`{.Agda} is the type of size `n`.
These are defined as an inductive family over `Nat`{.Agda},
such that `Fin 0` has 0 elements, `Fin 1` has 1 element, and so on.

Another way to view `Fin`{.Agda} is that it's the type of numbers
less than some upper bound. For instance, `fsuc fzero` is
of type `Fin 3`, but will _not_ typecheck as a `Fin 1`!

```agda
data Fin : Nat → Type where
  fzero : ∀ {n} → Fin (suc n)
  fsuc : ∀ {n} → Fin n → Fin (suc n)
```

Keeping with the perspective of `Fin`{.Agda} as a type of bounded
natural numbers, we provide conversion functions going back and forth.

```agda
from-nat : ∀ (n : Nat) → Fin (suc n)
from-nat zero = fzero
from-nat (suc n) = fsuc (from-nat n)

to-nat : ∀ {n : Nat} → Fin n → Nat
to-nat fzero = zero
to-nat (fsuc i) = suc (to-nat i)
```

A note of caution: because of some ✨technical reasons✨ cubical
agda cannot handle transports over indexed inductive types very well.
Instead, we define a function `cast`{.Agda} that computes on
the indicies of `Fin`{.Agda}, rather than on the path.

```agda
cast : ∀ {m n} → m ≡ n → Fin m → Fin n
cast {suc m} {zero} p fzero = absurd (Nat.zero≠suc (sym p))
cast {suc m} {suc n} p fzero = fzero
cast {suc m} {zero} p (fsuc i) = absurd (Nat.zero≠suc (sym p))
cast {suc m} {suc n} p (fsuc i) = fsuc (cast (Nat.suc-inj p) i)
```

Next, we move on to one of the most useful functions for `Fin`{.Agda}:
`strength`. This allows us to (possibly) strengthen the upper bound
on some `Fin n`.

```agda
strengthen : ∀ {n} → Fin (suc n) → Fin (suc n) ⊎ Fin n
strengthen {n = zero} fzero = inl fzero
strengthen {n = suc n} fzero = inr fzero
strengthen {n = suc n} (fsuc i) = ⊎-map fsuc fsuc (strengthen i)
```

On the other hand, `weaken`{.Agda} does the opposite: it relaxes
the upper bound on some `Fin n`, allowing us to regard it as a 
`Fin (suc n)`.

```agda
weaken : ∀ {n} → Fin n → Fin (suc n) 
weaken fzero = fzero
weaken (fsuc i) = fsuc (weaken i)
```

We can also relax the upper bounds if `m ≤ n`.

```agda
inject : ∀ {m n} → m Nat.≤ n → Fin m → Fin n
inject {_} {suc n} le fzero = fzero
inject {_} {suc n} le (fsuc i) = fsuc (inject le i)
```


## Discreteness

The proof here mirrors the one found in [`Data.Nat.Base`],
just with some slight tweaks required to handle the indexing.

[`Data.Nat.Base`]: Data.Nat.Base.html

We begin by showing that one can `distinguish`{.Agda} zero
from successor:

```agda
fzero≠fsuc : ∀ {n} {i : Fin n} → fzero ≡ fsuc i → ⊥
fzero≠fsuc {n = n} path = subst distinguish path tt
  where
    distinguish : Fin (suc n) → Type
    distinguish fzero = ⊤
    distinguish (fsuc _) = ⊥
```

Next, we show that `fsuc` is injective. This again follows
the proof in [`Data.Nat.Base`], but some extra care must be
taken to ensure that `pred`{.Agda} is well typed!

[`Data.Nat.Base`]: Data.Nat.Base.html

```agda
fsuc-inj : ∀ {n} {i j : Fin n} → fsuc i ≡ fsuc j → i ≡ j
fsuc-inj {n = suc n} p = ap pred p
  where
    pred : Fin (suc (suc n)) → Fin (suc n)
    pred fzero = fzero
    pred (fsuc i) = i
```

Finally, we pull everything together to show that `Fin`{.Agda}
is Discrete. This is not exactly a shock (after all, `Nat`{.Agda}) is
discrete), but it's useful nonetheless!

```agda
Discrete-Fin : ∀ {n} → Discrete (Fin n)
Discrete-Fin fzero fzero = yes refl
Discrete-Fin fzero (fsuc j) = no λ zero≡suc → absurd (fzero≠fsuc zero≡suc)
Discrete-Fin (fsuc i) fzero = no λ zero≡suc → absurd (fzero≠fsuc (sym zero≡suc))
Discrete-Fin (fsuc i) (fsuc j) with Discrete-Fin i j
... | yes i≡j = yes (ap fsuc i≡j)
... | no ¬i≡j = no λ suci≡sucj → ¬i≡j (fsuc-inj suci≡sucj)
```

[Hedberg's theorem] implies that `Fin{.Agda} is a [set], i.e., it only
has trivial paths.

[Hedberg's theorem]: agda://1Lab.HLevel.Sets#Discrete→is-set
[set]: agda://1Lab.HLevel#is-set

```agda
Nat-is-set : ∀ {n} → is-set (Fin n)
Nat-is-set = Discrete→is-set Discrete-Fin
```

## Ordering

Keeping with the view that `Fin`{.Agda} represents the type of
bounded natural numbers, we can re-use the ordering on
`Nat`{.Agda} to induce an ordering on `Fin`{.Agda}.
This lets us repurpose any lemmas on [`≤`] to also operate
on `Fin`{.Agda}.

[`≤`]: agda://Data.Nat.Base#_≤_

```agda
_≤_ : ∀ {n} → Fin n → Fin n → Type
i ≤ j = (to-nat i) Nat.≤ (to-nat j)
infix 3 _≤_

_<_ : ∀ {n} → Fin n → Fin n → Type
i < j = (to-nat i) Nat.< (to-nat j)
infix 3 _<_
```

Next, we define a pair of functions `squish{.Agda} and `skip`{.Agda},
which are the building blocks for _all_ monotone functions between
`Fin`{.Agda}. `squish i` takes a `j : Fin (suc n)` to a `Fin n`
by mapping both `i` and `i+1` to `i`. It's counterpart `skip i`
takes some `j : Fin n` to a `Fin (suc n)` by skipping over `i` instead.

```agda
squish : ∀ {n} → Fin n → Fin (suc n) → Fin n
squish fzero fzero = fzero
squish fzero (fsuc j) = j
squish (fsuc i) fzero = fzero
squish (fsuc i) (fsuc j) = fsuc (squish i j)

skip : ∀ {n} → Fin (suc n) → Fin n → Fin (suc n)
skip fzero j = fsuc j
skip (fsuc i) fzero = fzero
skip (fsuc i) (fsuc j) = fsuc (skip i j)
```

