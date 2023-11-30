<!--
```agda
open import Cat.Prelude

open import Order.Instances.Props
open import Order.Displayed
open import Order.Base

import Order.Reasoning as Pr
```
-->

```agda
module Order.Instances.Pointwise where
```

# The pointwise ordering

If $(B, \le)$ is a [[partially ordered set]], then so is $A \to B$, for
any type $A$ which we might choose! There might be other ways of making
$A \to B$ into a poset, of course, but the canonical way we're talking
about here is the **pointwise ordering** on $A \to B$, where $f \le g$
iff $f(x) \le g(x)$ for all $x$.

```agda
Pointwise : ∀ {ℓ ℓₐ ℓᵣ} → Type ℓ → Poset ℓₐ ℓᵣ → Poset (ℓ ⊔ ℓₐ) (ℓ ⊔ ℓᵣ)
Pointwise A B = po where
  open Pr B

  po : Poset _ _
  po .Poset.Ob = A → ⌞ B ⌟
  po .Poset._≤_ f g = ∀ x → f x ≤ g x
  po .Poset.≤-thin = hlevel!
  po .Poset.≤-refl x = ≤-refl
  po .Poset.≤-trans f≤g g≤h x = ≤-trans (f≤g x) (g≤h x)
  po .Poset.≤-antisym f≤g g≤f = funext λ x → ≤-antisym (f≤g x) (g≤f x)
```

A very important particular case of the pointwise ordering is the poset
of subsets of a fixed type, which has underlying set $A \to \Omega$.

```agda
Subsets : ∀ {ℓ} → Type ℓ → Poset ℓ ℓ
Subsets A = Pointwise A Props
```

Another important case: when your domain is not an arbitrary type but
another poset, you might want to consider the full subposet of $P \to Q$
consisting of the monotone maps:

```agda
Poset[_,_] : ∀ {ℓₒ ℓᵣ ℓₒ' ℓᵣ'}
         → Poset ℓₒ ℓᵣ
         → Poset ℓₒ' ℓᵣ'
         → Poset (ℓₒ ⊔ ℓᵣ ⊔ ℓₒ' ⊔ ℓᵣ') (ℓₒ ⊔ ℓᵣ')
Poset[_,_] P Q = po where
  open Pr Q

  po : Poset _ _
  po .Poset.Ob = Monotone P Q
  po .Poset._≤_ f g = ∀ (x : ⌞ P ⌟) → f # x ≤ g # x
  po .Poset.≤-thin = hlevel!
  po .Poset.≤-refl _ = ≤-refl
  po .Poset.≤-trans f≤g g≤h x = ≤-trans (f≤g x) (g≤h x)
  po .Poset.≤-antisym f≤g g≤f = ext (λ x → ≤-antisym (f≤g x) (g≤f x))
```
