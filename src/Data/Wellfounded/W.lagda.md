```agda
open import 1Lab.Prelude

open import Data.Wellfounded.Properties
open import Data.Wellfounded.Base

module Data.Wellfounded.W where
```

# W-types

The idea behind $W$ types is much simpler than they might appear at
first brush, especially because their form is like that one of the "big
two" $\Pi$ and $\Sigma$. However, the humble $W$ is much simpler: A
value of $W_A B$ is a tree with nodes labelled by $x : A$, and such that
the branching factor of such a node is given by $B(x)$. $W$-types can be
defined inductively:

```agda
data W {ℓ ℓ′} (A : Type ℓ) (B : A → Type ℓ′) : Type (ℓ ⊔ ℓ′) where
  sup : (x : A) (f : B x → W A B) → W A B
```

The constructor `sup`{.Agda} stands for **supremum**: it bunches up
(takes the supremum of) a bunch of subtrees, each subtree being given by
a value $y : B(x)$ of the branching factor for that node. The natural
question to ask, then, is: "supremum in _what_ order?". The order given
by the "is a subtree of" relation!

```agda
module _ {ℓ ℓ′} {A : Type ℓ} {B : A → Type ℓ′} where
  _<_ : W A B → W A B → Type _
  x < sup i f = ∃[ j ∈ B i ] (f j ≡ x)
```

This order is actually well-founded: if we want to prove a property of
$x : W_A B$, we may as well assume it's been proven for any (transitive)
subtree of $x$.

```agda
  W-well-founded : Wf _<_
  W-well-founded (sup x f) = acc λ y y<sup →
    ∥-∥-rec (Acc-is-prop _)
      (λ { (j , p) → subst (Acc _<_) p (W-well-founded (f j)) })
      y<sup
```
