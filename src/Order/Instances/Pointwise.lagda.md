```agda
open import Cat.Prelude

open import Order.Instances.Props
open import Order.Displayed
open import Order.Base

import Order.Reasoning as Pr

module Order.Instances.Pointwise where
```

# The pointwise ordering

If $(B, \le)$ is a partially ordered set, then so is $A \to B$, for any
type $A$ which we might choose! There might be other ways of making $A
\to B$ into a poset, of course, but the canonical way we're talking
about here is the **pointwise ordering** on $A \to B$, where $f \le g$
iff $f(x) \le g(x)$ for all $x$.

```agda
Pointwise : ∀ {ℓ ℓₐ ℓᵣ} → Type ℓ → Poset ℓₐ ℓᵣ → Poset (ℓ ⊔ ℓₐ) (ℓ ⊔ ℓᵣ)
Pointwise A B = to-poset (A → ⌞ B ⌟) mk-pwise where
  open Pr B
  mk-pwise : make-poset _ _
  mk-pwise .make-poset.rel f g         = ∀ x → f x ≤ g x
  mk-pwise .make-poset.thin            = hlevel 1
  mk-pwise .make-poset.id x            = ≤-refl
  mk-pwise .make-poset.trans f<g g<h x = ≤-trans (f<g x) (g<h x)
  mk-pwise .make-poset.antisym f<g g<f = funext λ x → ≤-antisym (f<g x) (g<f x)

```

A very important particular case of the pointwise ordering is the poset
of subsets of a fixed type, which has underlying set $A \to \Omega$.

```agda
Subsets : ∀ {ℓ} → Type ℓ → Poset ℓ ℓ
Subsets A = Pointwise A Props
```
