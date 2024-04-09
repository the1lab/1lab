<!--
```agda
open import 1Lab.HIT.Truncation
open import 1Lab.HLevel.Closure
open import 1Lab.Inductive
open import 1Lab.Resizing
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Type

open import Data.List.Membership
open import Data.Fin.Indexed
open import Data.List.Base
open import Data.Dec.Base
open import Data.Fin

open import Meta.Idiom
open import Meta.Bind
```
-->

```agda
module Data.Fin.Finite.Listed where
```

<!--
```agda
private variable
  ℓ   : Level
  A B : Type ℓ
```
-->

# Finite types through lists

We have defined [[finiteness|finite]] (and [[finite indexing|finitely
indexed set]]) for a type $T$ in terms of its relationship with a
specific [[standard finite set]] $[n]$. However, this is not always the
most convenient presentation of finiteness. It's often desirable to have
an actual [[list]] of $T$'s purported elements, which can be manipulated
using the usual toolkit for working on lists.

To this end, we define a **listing** for a type $A$ to consist of a list
$\rm{members} : \List{A}$ which contains every element of $A$ at least
once. The type-theoretic interpretation of "contains at least once" is
up for debate: it could either mean that we have an operation
$\rm{ix}(a) : a \in \rm{members}$ assigning each element of $T$ to its
index in $\rm{members}$, or that we have the weaker $\rm{ix}(a) : \| a
\in \rm{members} \|$, which only [[merely]] gets us an index.

```agda
record Listing {ℓ} (A : Type ℓ) : Type ℓ where
  field
    members    : List A
    has-member : ∀ a → ∥ a ∈ₗ members ∥
```

<!--
```agda
open Listing
```
-->

Our choice is the latter, and the reason is twofold: First, this
corresponds directly to the notion of finite cover, which means that
_having a listing_ will be equivalent to _being finitely indexed_, as
desired.

```agda
listing→finite-cover : Listing A → Finite-cover A
listing→finite-cover l = record
  { cover    = l .members !_
  ; is-cover = λ x → element→!-fibre <$> l .has-member x
  }

finite-cover→listing : Finite-cover A → Listing A
finite-cover→listing (covering f has) = record
  { members    = tabulate f
  ; has-member = λ a → Equiv.from (member-tabulate f a) <$> has a
  }
```

The second motivation has to do with _identity_ of listings: we want to
regard listings as the same precisely when their underlying lists are
the same.  However, if the assignment of indices were not truncated, it
would also factor identity of listings: we could regard $[0,0]$ as a
listing for the unit type in two different ways, depending on whether we
give back the index 0 or the index 1.

## Enumerations

Refining the notion of listing, we have **enumerations**: in a listing,
each element appears at least once, but it may appear an arbitrary
number of times. In an enumeration, each element is required to appear
_exactly_ once. To state this in a coherent way, we demand that, for
each $a$, the type of proofs-of-membership $a \in \rm{members}$ be
contractible.

```agda
record Enumeration {ℓ} (A : Type ℓ) : Type ℓ where
  field
    members    : List A
    has-member : ∀ a → is-contr (a ∈ₗ members)
```

<!--
```agda
open Enumeration
```
-->

Unsurprisingly, much like a listing corresponds to a surjection $[n] \to
A$, an enumeration corresponds to an _equivalence_ $[n] \to A$.

```agda
enumeration→fin-equiv : (l : Enumeration A) → Fin (length (l .members)) ≃ A
enumeration→fin-equiv l .fst         a = l .members ! a
enumeration→fin-equiv l .snd .is-eqv a = Equiv→is-hlevel 0
  (Equiv.inverse element≃!-fibre) (l .has-member a)

fin-equiv→enumeration : ∀ {n} → Fin n ≃ A → Enumeration A
fin-equiv→enumeration (fn , eqv) = record
  { members    = tabulate fn
  ; has-member = λ a → Equiv→is-hlevel 0 (member-tabulate fn a) (eqv .is-eqv a)
  }
```

<!--
```agda
enumeration→finite : Enumeration A → Finite A
enumeration→finite l = fin (pure (Equiv.inverse (enumeration→fin-equiv l)))
```
-->

## For discrete types

An important theorem about [[finitely-indexed sets]] is that, if they
are [[discrete]], then they are properly [[finite]]. This is much easier
to prove when working with listings than when working with surjections,
because the heavy lifting applies generically to arbitrary lists.

Given a listing, we may `nub`{.Agda} the list $xs$ of members, removing
the duplicates: the resulting list $ys$ has each $x \in ys$ a
[[proposition]]. Since each $x \in xs$ was merely inhabited, each $x :
A$ appears both _at least_ and _at most_ once in $ys$: we have refined
the listing into an enumeration.

```agda
nub-listing : ⦃ _ : Discrete A ⦄ → Listing A → Enumeration A
nub-listing li = record
  { members    = nub m
  ; has-member = λ a → ∥-∥-out! do
    memb ← has a
    pure (is-prop∙→is-contr (member-nub-is-prop m) (member→member-nub memb))
  }
  where open Listing li renaming (members to m ; has-member to has)
```

Plugging this construction into the connections between listings and
notions of finiteness constructed above, we obtain the desired theorem:
a finitely-indexed discrete type is finite.

```agda
Discrete-finitely-indexed→Finite
  : ⦃ _ : Discrete A ⦄
  → is-finitely-indexed A
  → Finite A
Discrete-finitely-indexed→Finite fi = ∥-∥-out! do
  cov ← □-tr fi
  let
    over  = finite-cover→listing cov
    exact = nub-listing over
  pure (enumeration→finite exact)
```
