<!--
```agda
open import 1Lab.Prelude

open import Order.Base
```
-->

```agda
module Order.Instances.Lift where
```

# Lifting posets across universes

Suppose you have a poset whose elements are in $o$ and relation in
$r$, but you really need it to have elements or relationships
in some larger universe $o \sqcup o'$ and homs in $r \sqcup r'$.
Fortunately you can uniformly lift the poset to this bigger universe.

```agda
Liftᵖ : ∀ {o r} o′ r′ → Poset o r → Poset (o ⊔ o′) (r ⊔ r′)
Liftᵖ o' r' X .Poset.Ob      = Lift o' ⌞ X ⌟
Liftᵖ o' r' X .Poset._≤_ x y = Lift r' $ (X .Poset._≤_) (lower x) (lower y)
Liftᵖ o' r' X .Poset.≤-thin  = Lift-is-hlevel 1 $ X .Poset.≤-thin
Liftᵖ o' r' X .Poset.≤-refl  = lift $ X .Poset.≤-refl
Liftᵖ o' r' X .Poset.≤-trans (lift p) (lift q)   = lift (X .Poset.≤-trans p q)
Liftᵖ o' r' X .Poset.≤-antisym (lift p) (lift q) = ap lift (X .Poset.≤-antisym p q)

Lift-monotone-l
  : ∀ {so sr} bo br {o r} {X : Poset so sr} {Y : Poset o r}
  → Monotone X Y
  → Monotone (Liftᵖ bo br X) Y
Lift-monotone-l bo br G = F where
  open Monotone
  F : Monotone _ _
  F .hom    (lift x) = G .hom x
  F .pres-≤ (lift α) = G .pres-≤ α

Lift-monotone-r
  : ∀ {so sr} bo br {o r} {X : Poset so sr} {Y : Poset o r}
  → Monotone X Y
  → Monotone X (Liftᵖ bo br Y)
Lift-monotone-r bo br G = F where
  open Monotone
  F : Monotone _ _
  F .hom    x = lift $ G .hom x
  F .pres-≤ α = lift $ G .pres-≤ α
```
