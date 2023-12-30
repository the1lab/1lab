<!--
```agda
open import 1Lab.Prelude

open import Data.Int.Order
open import Data.Int.Base
open import Data.Nat using (max; max-≤l; max-≤r; max-univ; min; min-≤l; min-≤r; min-univ)
```
-->

```agda
module Data.Int.Order.Properties where
```

<!--
```agda
abstract
```
-->

# Properties of the order of integers

This module establishes further arithmetic and algebraic properties
of the integers that involve the order. All proofs are straightforward
case bashes; there are no further comments.

```agda
  maxℤ-≤l : (x y : Int) → x ≤ maxℤ x y
  maxℤ-≤l (pos x)    (pos y)    = pos≤pos (max-≤l x y)
  maxℤ-≤l (pos _)    (negsuc _) = ≤-refl
  maxℤ-≤l (negsuc _) (pos _)    = neg≤pos
  maxℤ-≤l (negsuc x) (negsuc y) = neg≤neg (min-≤l x y)

  maxℤ-≤r : (x y : Int) → y ≤ maxℤ x y
  maxℤ-≤r (pos x)    (pos y)    = pos≤pos (max-≤r x y)
  maxℤ-≤r (pos _)    (negsuc _) = neg≤pos
  maxℤ-≤r (negsuc _) (pos _)    = ≤-refl
  maxℤ-≤r (negsuc x) (negsuc y) = neg≤neg (min-≤r x y)

  maxℤ-univ : (x y z : Int) → x ≤ z → y ≤ z → maxℤ x y ≤ z
  maxℤ-univ _ _ _ (pos≤pos x≤z) (pos≤pos y≤z) = pos≤pos (max-univ _ _ _ x≤z y≤z)
  maxℤ-univ _ _ _ (pos≤pos x≤z) neg≤pos       = pos≤pos x≤z
  maxℤ-univ _ _ _ neg≤pos       (pos≤pos y≤z) = pos≤pos y≤z
  maxℤ-univ _ _ _ neg≤pos       neg≤pos       = neg≤pos
  maxℤ-univ _ _ _ (neg≤neg x≥z) (neg≤neg y≥z) = neg≤neg (min-univ _ _ _ x≥z y≥z)

  minℤ-≤l : (x y : Int) → minℤ x y ≤ x
  minℤ-≤l (pos x)    (pos y)    = pos≤pos (min-≤l x y)
  minℤ-≤l (pos _)    (negsuc _) = neg≤pos
  minℤ-≤l (negsuc _) (pos _)    = ≤-refl
  minℤ-≤l (negsuc x) (negsuc y) = neg≤neg (max-≤l x y)

  minℤ-≤r : (x y : Int) → minℤ x y ≤ y
  minℤ-≤r (pos x)    (pos y)    = pos≤pos (min-≤r x y)
  minℤ-≤r (pos _)    (negsuc _) = ≤-refl
  minℤ-≤r (negsuc _) (pos _)    = neg≤pos
  minℤ-≤r (negsuc x) (negsuc y) = neg≤neg (max-≤r x y)

  minℤ-univ : (x y z : Int) → z ≤ x → z ≤ y → z ≤ minℤ x y
  minℤ-univ _ _ _ (pos≤pos x≥z) (pos≤pos y≥z) = pos≤pos (min-univ _ _ _ x≥z y≥z)
  minℤ-univ _ _ _ neg≤pos       neg≤pos       = neg≤pos
  minℤ-univ _ _ _ neg≤pos       (neg≤neg y≤z) = neg≤neg y≤z
  minℤ-univ _ _ _ (neg≤neg x≤z) neg≤pos       = neg≤neg x≤z
  minℤ-univ _ _ _ (neg≤neg x≤z) (neg≤neg y≤z) = neg≤neg (max-univ _ _ _ x≤z y≤z)
```
