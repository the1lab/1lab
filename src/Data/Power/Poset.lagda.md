```
open import 1Lab.Prelude

open import Data.Power
open import Data.Sum

open import Order.Proset
open import Order.Poset

module Data.Power.Poset where
```

# Poset of Subobjects

The `power set`{.Agda ident=ℙ} of a type $X$ can be organised into a
partially-ordered set, where the order relation is given by inclusion.
We call this the **poset of subobjects** of $X$, and denote it by
`Power`{.Agda}.

```
Power : ∀ {ℓ} → Type ℓ → Poset ℓ (lsuc ℓ)
Power A .fst = ℙ A
Power A .snd = st where
  open PosetOn
  open isPartialOrder
  open isPreorder

  st : PosetOn (ℙ A)
  st ._≤_ = _⊆_
  st .hasIsPartialOrder .hasIsPreorder .reflexive _ x = x
  st .hasIsPartialOrder .hasIsPreorder .transitive x⊆y y⊆z a a∈x = y⊆z a (x⊆y a a∈x)
  st .hasIsPartialOrder .hasIsPreorder .propositional {y = y} =
    isHLevelΠ 1 λ x → isHLevel→ 1 (y x .snd)
  st .hasIsPartialOrder .antisym = ℙ-ext _ _
```

Additionally, `Power`{.Agda} has all meets and joins; These are given by
the intersections and unions.

<!--
```
private variable
  ℓ : Level
  A : Type ℓ
  x y : ℙ A
```
-->

```
Power-meet : isMeet (Power A) (x ∩ y) x y
Power-meet .isMeet.m≤x x (x∈x , x∈y) = x∈x
Power-meet .isMeet.m≤y x (x∈x , x∈y) = x∈y
Power-meet .isMeet.limiting a a⊆x a⊆y x x∈a = (a⊆x x x∈a) , a⊆y x x∈a

Power-join : isJoin (Power A) (x ∪ y) x y
Power-join .isJoin.x≤j x x∈x = inc (inl x∈x)
Power-join .isJoin.y≤j x x∈y = inc (inr x∈y)
Power-join .isJoin.colimiting a x⊆a y⊆a x x∈cup =
  ∥-∥-elim (λ _ → a x .snd) (λ { (inl p) → x⊆a x p
                               ; (inr q) → y⊆a x q
                               })
                            x∈cup
```
