<!--
```
open import 1Lab.Prelude
```
-->

```agda
module Homotopy.Space.Suspension where
```

# Suspension

Given a type `A`, the type `Susp A` is defined by the property that `Susp A`
has two _poles_ denoted `N` and `S` and an `A`-indexed family of paths `N ≡ S`.

```agda
data Susp {ℓ} (A : Type ℓ) : Type ℓ where
  N S   : Susp A
  merid : A → N ≡ S

```

*TODO*: Draw a picture and explain!

Suspension is an operation that increases the [[connectivity]] of a type:
suspending an empty type makes it inhabited, suspending an inhabited type
makes it connected, suspending a connected type makes it 1-connected, etc.
