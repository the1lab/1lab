---
description: |
  Properties of conatural numbers.
---
<!--
```agda
open import 1Lab.Prelude hiding (zero; suc; _+_; _*_)

open import Codata.Conat.Base

import Data.Nat.Base as Nat
```
-->
```agda
module Codata.Conat.Properties where
```

<!--
```agda
open Conat
open _≈_
open _≤_
```
-->

## Bisimulation

```agda
mutual
  ≈-sym : ∀ {x y} → x ≈ y → y ≈ x
  ≈-sym p .force = ≈#-sym (p .force)

  ≈#-sym : ∀ {x y} → x ≈# y → y ≈# x
  ≈#-sym z≈z# = z≈z#
  ≈#-sym (s≈s# p) = s≈s# (≈-sym p)

mutual
  ≈-trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
  ≈-trans p q .force = ≈#-trans (p .force) (q .force)

  ≈#-trans : ∀ {x y z} → x ≈# y → y ≈# z → x ≈# z
  ≈#-trans z≈z# z≈z# = z≈z#
  ≈#-trans (s≈s# p) (s≈s# q) = s≈s# (≈-trans p q)
```

## Arithmetic

```agda
mutual
  fadd-comm : ∀ x y z → fadd x y z ≡ fadd y x z
  fadd-comm x y z i .force = fadd-comm# (x .force) (y .force) z i

  fadd-comm# : ∀ x y z → fadd# x y z ≡ fadd# y x z
  fadd-comm# zero# zero# z i = z .force
  fadd-comm# zero# (suc# y) z i = suc# (fadd-comm zero y z i)
  fadd-comm# (suc# x) zero# z i = suc# (fadd-comm x zero z i)
  fadd-comm# (suc# x) (suc# y) z i = suc# (fadd-comm x y (suc z) i)

+-comm : ∀ x y → x + y ≡ y + x
+-comm x y = fadd-comm x y 0

+-comm# : ∀ x y → x +# y ≡ y +# x
+-comm# x y = fadd-comm# x y 0
```

```agda
mutual
  +-zerol : ∀ x → 0 + x ≡ x
  +-zerol x i .force = +-zerol# (x .force) i

  +-zerol# : ∀ x → 0 +# x ≡ x
  +-zerol# zero# i = zero#
  +-zerol# (suc# x) i = suc# (+-zerol x i)

+-zeror : ∀ x → x + 0 ≡ x
+-zeror x = +-comm x 0 ∙ +-zerol x

+-zeror# : ∀ x → x +# 0 ≡ x
+-zeror# x = +-comm# x 0 ∙ +-zerol# x
```


```agda
mutual
  fadd-infl : ∀ x y → fadd ∞ x y ≡ ∞
  fadd-infl x y i .force = fadd-infl# (x .force) y i

  fadd-infl# : ∀ x y → fadd# (suc# ∞) x y ≡ suc# ∞
  fadd-infl# zero# y i = suc# (fadd-infl 0 y i)
  fadd-infl# (suc# x) y i = suc# (fadd-infl x (suc y) i)

fadd-infr : ∀ x y → fadd x ∞ y ≡ ∞
fadd-infr x y = fadd-comm x ∞ y ∙ fadd-infl x y

fadd-infr# : ∀ x y → fadd# x (suc# ∞) y ≡ suc# ∞
fadd-infr# x y = fadd-comm# x (suc# ∞) y ∙ fadd-infl# x y

+-infl : ∀ x → ∞ + x ≡ ∞
+-infl x = fadd-infl x 0

+-infr : ∀ x → x + ∞ ≡ ∞
+-infr x = fadd-infr x 0
```

```agda
mutual
  fmul-comm : ∀ x y z → fmul x y z ≡ fmul y x z
  fmul-comm x y z i .force = fmul-comm# (x .force) (y .force) z i

  fmul-comm# : ∀ x y z → fmul# x y z ≡ fmul# y x z
  fmul-comm# zero# zero# z i = z .force
  fmul-comm# zero# (suc# x) z i = z .force
  fmul-comm# (suc# x) zero# z i = z .force
  fmul-comm# (suc# x) (suc# y) z i = suc# (fmul-comm x y (fadd-comm x y z i) i)

*-comm : ∀ x y → x * y ≡ y * x
*-comm x y = fmul-comm x y 0

*-comm# : ∀ x y → x *# y ≡ y *# x
*-comm# x y = fmul-comm# x y 0
```

```agda
fmul-zerol : ∀ x y → fmul 0 x y ≡ y
fmul-zerol x y i .force = y .force

fmul-zerol# : ∀ x y → fmul# 0 x y ≡ y .force
fmul-zerol# x y = refl

fmul-zeror : ∀ x y → fmul x 0 y ≡ y
fmul-zeror x y = fmul-comm x 0 y ∙ fmul-zerol x y

fmul-zeror# : ∀ x y → fmul# x 0 y ≡ y .force
fmul-zeror# x y = fmul-comm# x 0 y ∙ fmul-zerol# x y

*-zerol : ∀ x → 0 * x ≡ 0
*-zerol x = fmul-zerol x 0

*-zeror : ∀ x → x * 0 ≡ 0
*-zeror x = *-comm x 0 ∙ *-zerol x
```


## Ordering

```agda
mutual
  ≤-refl : ∀ {x : Conat} → x ≤ x
  ≤-refl .force = ≤-refl#

  ≤-refl# : ∀ {x : Conat#} → x ≤# x
  ≤-refl# {x = zero#} = 0≤x#
  ≤-refl# {x = suc# x} = s≤s# ≤-refl
```

```agda
mutual
  ≤-trans : ∀ {x y z : Conat} → x ≤ y → y ≤ z → x ≤ z
  ≤-trans p q .force = ≤-trans# (p .force) (q .force)

  ≤-trans# : ∀ {x y z : Conat#} → x ≤# y → y ≤# z → x ≤# z
  ≤-trans# 0≤x# q = 0≤x#
  ≤-trans# (s≤s# x≤y) (s≤s# y≤z) = s≤s# (≤-trans x≤y y≤z)
```

```agda
mutual
  ≤-antisym : ∀ {x y} → x ≤ y → y ≤ x → x ≡ y
  ≤-antisym x≤y y≤x i .force = ≤-antisym# (x≤y .force) (y≤x .force) i

  ≤-antisym# : ∀ {x y} → x ≤# y → y ≤# x → x ≡ y
  ≤-antisym# 0≤x# 0≤x# i = zero#
  ≤-antisym# (s≤s# x≤y) (s≤s# y≤x) i = suc# (≤-antisym x≤y y≤x i)
```


```agda
mutual
  ≤-infr : ∀ {x} → x ≤ ∞
  ≤-infr {x = x} .force = ≤-infr#

  ≤-infr# : ∀ {x} → x ≤# suc# ∞
  ≤-infr# {x = zero#} = 0≤x#
  ≤-infr# {x = suc# x} = s≤s# ≤-infr
```
