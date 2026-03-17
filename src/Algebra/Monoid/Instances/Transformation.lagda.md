<!--
```agda
open import 1Lab.Prelude

open import Algebra.Monoid

open import Data.Product.NAry
open import Data.Vec.Base
open import Data.Fin
```
-->

```agda
module Algebra.Monoid.Instances.Transformation where
```

# Full transformation monoids {defines="full-transformation-monoid"}

If $X$ is a [[set]], then so too is its type of endomaps $X \to X$. 
Moreover, $X \to X$ is a [[monoid]] under composition, called the _full 
transformation monoid_ on $X$, with the associativity and identity laws
holding definitionally:

```agda
End : ∀ {ℓ} (X : Set ℓ) → Monoid-on (∣ X ∣ → ∣ X ∣)
End X = to-monoid-on M where
  open make-monoid
  M : make-monoid (∣ X ∣ → ∣ X ∣)
  M .monoid-is-set = hlevel 2
  M ._⋆_ f g = f ∘ g
  M .1M = id
  M .⋆-assoc f g h = refl
  M .⋆-idl f = refl
  M .⋆-idr f = refl
```

In the case $X$ is a [[standard finite set]], there is a more convenient
[isomorphic construction].

[isomorphic construction]: Algebra.Monoid.Instances.Transformation.Fin.html