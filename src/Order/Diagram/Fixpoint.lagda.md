<!--
```agda
open import Cat.Displayed.Total
open import Cat.Prelude

open import Order.Base

import Order.Reasoning
```
-->

```agda
module Order.Diagram.Fixpoint {o ℓ} (P : Poset o ℓ) where
```

<!--
```agda
open Order.Reasoning P
```
-->

Let $(P, \le)$ be a poset, and $f : P \to P$ be a monotone map. We say
that $f$ has a **least fixpoint** if there exists some $x : P$ such that
$f(x) = x$, and for every other $y$ such that $f(y) = y$, $x \le y$.

```agda
record is-least-fixpoint (f : Posets.Hom P P) (x : Ob) : Type (o ⊔ ℓ) where
  no-eta-equality
  field
    fixed : f .hom x ≡ x
    least : ∀ (y : Ob) → f .hom y ≡ y → x ≤ y

record Least-fixpoint (f : Posets.Hom P P) : Type (o ⊔ ℓ) where
  no-eta-equality
  field
    fixpoint : Ob
    has-least-fixpoint : is-least-fixpoint f fixpoint
  open is-least-fixpoint has-least-fixpoint public

open is-least-fixpoint
```

Least fixed points are unique, so the type of least fixpoints of $f$ is
a proposition.

```agda
least-fixpoint-unique
  : ∀ {f : Posets.Hom P P} {x y}
  → is-least-fixpoint f x → is-least-fixpoint f y
  → x ≡ y
least-fixpoint-unique x-fix y-fix =
  ≤-antisym (x-fix .least _ (y-fix .fixed)) (y-fix .least _ (x-fix .fixed))

is-least-fixpoint-is-prop
  : ∀ {f : Posets.Hom P P} {x}
  → is-prop (is-least-fixpoint f x)
is-least-fixpoint-is-prop {f = f} {x = x} p q i .fixed =
  Ob-is-set (f .hom x) x (p .fixed) (q .fixed) i
is-least-fixpoint-is-prop {f = f} {x = x} p q i .least y y-fix =
  is-prop→pathp
    (λ i → ≤-thin)
    (p .least y y-fix) (q .least y y-fix) i

Least-fixpoint-is-prop
  : ∀ {f : Posets.Hom P P}
  → is-prop (Least-fixpoint f)
Least-fixpoint-is-prop {f = f} p q = p≡q where
  module p = Least-fixpoint p
  module q = Least-fixpoint q

  path : p.fixpoint ≡ q.fixpoint
  path = least-fixpoint-unique p.has-least-fixpoint q.has-least-fixpoint

  p≡q : p ≡ q
  p≡q i .Least-fixpoint.fixpoint = path i
  p≡q i .Least-fixpoint.has-least-fixpoint =
    is-prop→pathp (λ i → is-least-fixpoint-is-prop {x = path i})
      p.has-least-fixpoint q.has-least-fixpoint i
```
