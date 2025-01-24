---
description: |
  Properties of conatural numbers.
---
<!--
```agda
open import 1Lab.Prelude hiding (zero; suc; _+_; _*_)

open import Data.Sum.Base


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

# Basic Properties

```agda
unsuc# : Conat# → Conat
unsuc# zero# = 0
unsuc# (suc# x) = x

suc-inj# : ∀ {x y} → suc# x ≡ suc# y → x ≡ y
suc-inj# = ap unsuc#

force-inj : ∀ {x y : Conat} → x .force ≡ y .force → x ≡ y
force-inj p i .force = p i
```

```agda
is-zero# : Conat# → Type
is-zero# zero# = ⊤
is-zero# (suc# x) = ⊥

is-suc# : Conat# → Type
is-suc# zero# = ⊥
is-suc# (suc# x) = ⊤

zero#≠suc# : ∀ {x} → zero# ≠ suc# x
zero#≠suc# p = subst is-zero# p tt

suc#≠zero# : ∀ {x} → suc# x ≠ zero#
suc#≠zero# p = subst is-suc# p tt
```


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
fadd-zero-zero : ∀ z → fadd 0 0 z ≡ z
fadd-zero-zero z = force-inj refl
```


```agda
mutual
  fadd-sucl#
    : ∀ {x+1# x y# y z}
    → x+1# ≡ suc# x
    → y# ≡ y .force
    → fadd# x+1# y# z ≡ suc# (fadd x y z)
  fadd-sucl# {zero#} {x} {y#} {y} {z} p q =
    absurd (zero#≠suc# p)
  fadd-sucl# {suc# x-1} {x} {zero#} {y} {z} p q =
    ap suc# (ap₂ (λ x y → fadd x y z) (suc-inj# p) (force-inj q))
  fadd-sucl# {suc# x-1} {x} {suc# y-1} {y} {z} p q i =
    suc# (fadd-suc-sucr {suc-inj# p i} {y-1} {y} {z} q i)

  fadd-sucr#
    : ∀ {x# x y+1# y z}
    → x# ≡ x .force
    → y+1# ≡ suc# y
    → fadd# x# y+1# z ≡ suc# (fadd x y z)
  fadd-sucr# {x#} {x} {zero#} {y} {z} p q =
    absurd (zero#≠suc# q)
  fadd-sucr# {zero#} {x} {suc# y-1} {y} {z} p q =
    ap suc# (ap₂ (λ x y → fadd x y z) (force-inj p) (suc-inj# q))
  fadd-sucr# {suc# x-1} {x} {suc# y-1} {y} {z} p q i =
    suc# (fadd-suc-sucl {x-1} {x} {suc-inj# q i} {z} p i)

  fadd-suc-suc#
    : ∀ {x x+1# y y+1# z}
    → suc# x ≡ x+1#
    → suc# y ≡ y+1#
    → fadd# (x .force) (y .force) (suc (suc z)) ≡ fadd# x+1# y+1# z
  fadd-suc-suc# {x+1# = zero#} {y+1# = y+1#} p q = absurd (suc#≠zero# p)
  fadd-suc-suc# {x+1# = suc# x} {y+1# = zero#} p q = absurd (suc#≠zero# q)
  fadd-suc-suc# {x+1# = suc# x} {y+1# = suc# y} p q =
    fadd-suc# (ap (force ∘ unsuc#) p) (ap (force ∘ unsuc#) q)

  fadd-suc-suc
    : ∀ {x x+1 y y+1 z}
    → suc# x ≡ x+1 .force
    → suc# y ≡ y+1 .force
    → fadd x y (suc (suc z)) ≡ fadd x+1 y+1 z
  fadd-suc-suc {z = z} p q i .force = fadd-suc-suc# {z = z} p q i

  fadd-suc#
    : ∀ {x# x y# y z}
    → x# ≡ x .force
    → y# ≡ y .force
    → fadd# x# y# (suc z) ≡ suc# (fadd x y z)
  fadd-suc# {zero#} {x} {zero#} {y} {z} p q =
    ap suc# $
    subst₂ (λ x y → z ≡ (fadd x y z))
      (force-inj p)
      (force-inj q)
      (sym (fadd-zero-zero z))
  fadd-suc# {zero#} {x} {suc# y-1} {y} {z} p q i =
    suc# (fadd-suc-sucr {force-inj {zero} {x} p i} {y-1} {y} {z} q i)
  fadd-suc# {suc# x-1} {x} {zero#} {y} {z} p q i =
    suc# (fadd-suc-sucl {x-1} {x} {force-inj {zero} {y} q i} {z} p i)
  fadd-suc# {suc# x-1} {x} {suc# y-1} {y} {z} p q i =
    suc# (fadd-suc-suc {x-1} {x} {y-1} {y} {z} p q i)

  fadd-suc-sucr#
    : ∀ {x# y y+1# z}
    → suc# y ≡ y+1#
    → fadd# x# (y .force) (suc z) ≡ fadd# x# y+1# z
  fadd-suc-sucr# {x#} {y} {zero#} {z} p = absurd (suc#≠zero# p)
  fadd-suc-sucr# {zero#} {y} {suc# y-1} {z} p =
    fadd-suc# refl (ap (force ∘ unsuc#) p)
  fadd-suc-sucr# {suc# x-1} {y} {suc# y-1} {z} p =
    fadd-sucl# refl (ap (force ∘ unsuc#) p)

  fadd-suc-sucr
    : ∀ {x y y+1 z}
    → suc# y ≡ y+1 .force
    → fadd x y (suc z) ≡ fadd x y+1 z
  fadd-suc-sucr {x = x} {z = z} p i .force =
    fadd-suc-sucr# {x# = x .force} {z = z} p i

  fadd-suc-sucl#
    : ∀ {x x+1# y# z}
    → suc# x ≡ x+1#
    → fadd# (x .force) y# (suc z) ≡ fadd# x+1# y# z
  fadd-suc-sucl# {x} {zero#} {y#} {z} p =
    absurd (suc#≠zero# p)
  fadd-suc-sucl# {x} {suc# x-1} {zero#} {z} p =
    fadd-suc# (ap (force ∘ unsuc#) p) refl
  fadd-suc-sucl# {x} {suc# x-1} {suc# y-1} {z} p =
    fadd-sucr# (ap (force ∘ unsuc#) p) refl

  fadd-suc-sucl
    : ∀ {x x+1 y z}
    → suc# x ≡ x+1 .force
    → fadd x y (suc z) ≡ fadd x+1 y z
  fadd-suc-sucl {y = y} {z = z} p i .force =
    fadd-suc-sucl# {y# = y .force} {z = z} p i
```

```agda
+-sucl : ∀ x y → suc x + y ≡ suc (x + y)
+-sucl x y i .force =
  fadd-sucl# {x = x} {y = y} {z = 0} refl refl i

+-sucr : ∀ x y → x + suc y ≡ suc (x + y)
+-sucr x y i .force =
  fadd-sucr# {x = x} {y = y} {z = 0} refl refl i
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
