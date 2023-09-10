<!--
```agda
open import Data.Dec.Base
open import Data.Sum

open import Meta.Invariant
open import Meta.Idiom
```
-->

```agda
module Data.Dec.Properties where
```

# Decidable types - Properties

The closure properties of [[decidable]] types make `Dec`{.Agda}
a `Monoidal`{.Agda} and `Alternative`{.Agda} `Invariant`{.Agda} functor.

```agda
instance
  Invariant-Dec : Invariant (eff Dec)
  Invariant-Dec .Invariant.invmap = Dec-map

  Monoidal-Dec : Monoidal (eff Dec)
  Monoidal-Dec .Monoidal.munit = Dec-⊤
  Monoidal-Dec .Monoidal._<,>_ a b = Dec-× ⦃ a ⦄ ⦃ b ⦄

  Alternative-Dec : Alternative (eff Dec)
  Alternative-Dec .Alternative.empty = Dec-⊥
  Alternative-Dec .Alternative._<+>_ a b = Dec-⊎ ⦃ a ⦄ ⦃ b ⦄
```
