---
description: |
  Groups and quasigroups
---
<!--
```agda
open import Algebra.Quasigroup
open import Algebra.Semigroup
open import Algebra.Group.Ab
open import Algebra.Monoid
open import Algebra.Group

open import Cat.Prelude hiding (_/_; _+_; _-_)

import Algebra.Monoid.Reasoning
```
-->
```agda
module Algebra.Quasigroup.Instances.Group where
```

# Groups and quasigroups

<!--
```agda
private variable
  ℓ : Level
  A : Type ℓ
```
-->

Every [[group]] is a [[quasigroup]], as multiplication in a group is
an equivalence.

```agda
is-group→is-left-quasigroup
  : ∀ {_⋆_ : A → A → A}
  → is-group _⋆_
  → is-left-quasigroup _⋆_
is-group→is-left-quasigroup {_⋆_ = _⋆_} ⋆-group =
  ⋆-equivl→is-left-quasigroup (hlevel 2) ⋆-equivl
  where open is-group ⋆-group

is-group→is-right-quasigroup
  : ∀ {_⋆_ : A → A → A}
  → is-group _⋆_
  → is-right-quasigroup _⋆_
is-group→is-right-quasigroup {_⋆_ = _⋆_} ⋆-group =
  ⋆-equivr→is-right-quasigroup (hlevel 2) ⋆-equivr
  where open is-group ⋆-group

is-group→is-quasigroup
  : ∀ {_⋆_ : A → A → A}
  → is-group _⋆_
  → is-quasigroup _⋆_
is-group→is-quasigroup {_⋆_ = _⋆_} ⋆-group .is-quasigroup.has-is-left-quasigroup =
  is-group→is-left-quasigroup ⋆-group
is-group→is-quasigroup {_⋆_ = _⋆_} ⋆-group .is-quasigroup.has-is-right-quasigroup =
  is-group→is-right-quasigroup ⋆-group
```

## Associative quasigroups as groups

Conversely, if a quasigroup $(A, \star)$ is merely inhabited and associative,
then it is a group.

```agda
associative+is-quasigroup→is-group
  : ∀ {_⋆_ : A → A → A}
  → ∥ A ∥
  → (∀ x y z → x ⋆ (y ⋆ z) ≡ (x ⋆ y) ⋆ z)
  → is-quasigroup _⋆_
  → is-group _⋆_
```

We start by observing that `is-group` is an h-prop, so it suffices to
consider the case where $A$ is inhabited.

```agda
associative+is-quasigroup→is-group {A = A} {_⋆_ = _⋆_} ∥a∥ ⋆-assoc ⋆-quasi =
  rec! (λ a → to-is-group (⋆-group a)) ∥a∥
```

<!--
```agda
  where
    open is-quasigroup ⋆-quasi renaming (has-is-magma to ⋆-magma)
    open make-group
```
-->

Next, a useful technical lemma: if $a \star x = b \star y$, then
$x \backslash a = b / y$.

```agda
    ⧵-/-comm
      : ∀ {a b x y}
      → x ⋆ b ≡ a ⋆ y
      → x ⧵ a ≡ b / y
```

The proof is an elegant bit of algebra. Recall that in a quasigroup,
$\star$ is left and right cancellative, so it suffices to show that:

$$(x \star (x \backslash a)) \star y = (x \star (b / y)) \star y$$

Next, $(x \star (x \backslash a)) \star y = a \star y$, and $a \star y = x \star b$,
so it remains to show that $x \star b = (x \star (b / y)) \star y$. Crucially,
$\star$ is associative, so:

$$
(x \star (b / y)) \star y = x \star ((b / y) \star y) = x \star b
$$

which completes the proof.

```agda
    ⧵-/-comm {a} {b} {x} {y} comm =
      ⋆-cancell x $ ⋆-cancelr y $
       (x ⋆ (x ⧵ a)) ⋆ y ≡⟨ ap (_⋆ y) (⧵-invr x a) ⟩
       a ⋆ y             ≡˘⟨ comm ⟩
       x ⋆ b             ≡˘⟨ ap (x ⋆_) (/-invl b y) ⟩
       x ⋆ ((b / y) ⋆ y) ≡⟨ ⋆-assoc x (b / y) y ⟩
       (x ⋆ (b / y)) ⋆ y ∎
```

With that out of the way, we shall show that

$$(A, \star, (a \backslash a), (\lambda x. (a \backslash a) / x))$$

forms a group for any $a : A$.

```agda
    ⋆-group : A → make-group A
    ⋆-group a .group-is-set = hlevel 2
    ⋆-group a .unit = a ⧵ a
    ⋆-group a .mul x y = x ⋆ y
    ⋆-group a .inv x = (a ⧵ a) / x
```

Associativity is one of our hypotheses, so all that remains is left
inverses and left identities. Next, note that

$$
(a \backslash a), (\lambda x. (a \backslash a) / x)) \star x = (a \backslash a)
$$

is just one of the quasigroup axioms. Finally, our lemma gives us
$a \backslash a = x / x$, so we have:

$$
(a \backslash a) \star x = (x / x) \star x = x
$$

which completes the proof.

```agda
    ⋆-group a .assoc x y z =
      ⋆-assoc x y z
    ⋆-group a .invl x =
      /-invl (a ⧵ a) x
    ⋆-group a .idl x =
      (a ⧵ a) ⋆ x ≡⟨ ap (_⋆ x) (⧵-/-comm refl) ⟩
      (x / x) ⋆ x ≡⟨ /-invl x x ⟩
      x ∎
```

Taking a step back, this result demonstrates that associative quasigroups
behave like potentially empty groups.
