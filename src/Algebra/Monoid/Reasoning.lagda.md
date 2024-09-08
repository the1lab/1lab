<!--
```agda
open import 1Lab.Prelude hiding (_*_)

open import Algebra.Monoid
```
-->

```agda
module Algebra.Monoid.Reasoning {ℓ} (M : Monoid ℓ) where
```

# Reasoning combinators for monoids

<!--
```agda
open Monoid-on (M .snd) renaming (_⋆_ to _*_ ; identity to 1m)

private variable
  a b c d e f f' g g' h h' i w x y z : ⌞ M ⌟
```
-->

```agda
id-comm : a * 1m ≡ 1m * a
id-comm = idr ∙ sym idl

id-comm-sym : 1m * a ≡ a * 1m
id-comm-sym = idl ∙ sym idr

module _ (p : x ≡ 1m) where
  eliml : x * a ≡ a
  eliml = ap₂ _*_ p refl ∙ idl

  elimr : a * x ≡ a
  elimr = ap₂ _*_ refl p ∙ idr

  introl : a ≡ x * a
  introl = sym eliml

  intror : a ≡ a * x
  intror = sym elimr

module _ (p : x * y ≡ z) where
  pulll : x * (y * a) ≡ z * a
  pulll = associative ∙ ap₂ _*_ p refl

  pullr : (a * x) * y ≡ a * z
  pullr = sym associative ∙ ap₂ _*_ refl p

module _ (p : z ≡ x * y) where
  pushl : z * a ≡ x * (y * a)
  pushl = sym (pulll (sym p))

  pushr : a * z ≡ (a * x) * y
  pushr = sym (pullr (sym p))

module _ (p : w * x ≡ y * z) where
  extendl : w * (x * a) ≡ y * (z * a)
  extendl = pulll refl ∙ ap₂ _*_ p refl ∙ pullr refl

  extendr : (a * w) * x ≡ (a * y) * z
  extendr = pullr refl ∙ ap₂ _*_ refl p ∙ pulll refl

module _ (p : x * y ≡ 1m) where
  cancell : x * (y * a) ≡ a
  cancell = pulll p ∙ idl

  cancelr : (a * x) * y ≡ a
  cancelr = pullr p ∙ idr

  insertl : a ≡ x * (y * a)
  insertl = sym cancell

  insertr : a ≡ (a * x) * y
  insertr = sym cancelr

lswizzle : g ≡ h * i → f * h ≡ 1m → f * g ≡ i
lswizzle p q = ap₂ _*_ refl p ∙ cancell q

rswizzle : g ≡ i * h → h * f ≡ 1m → g * f ≡ i
rswizzle p q = ap₂ _*_ p refl ∙ cancelr q

swizzle : f * g ≡ h * i → g * g' ≡ 1m → h' * h ≡ 1m → h' * f ≡ i * g'
swizzle p q r = lswizzle (sym (associative ∙ rswizzle (sym p) q)) r
```
