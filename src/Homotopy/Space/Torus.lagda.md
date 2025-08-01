---
description: |
  We construct the torus in components as a cell complex, and establish
  the equivalence between that definition and a product of circles.
---
<!--
```agda
open import 1Lab.Prelude

open import Homotopy.Space.Circle
```
-->

```agda
module Homotopy.Space.Torus where
```

# The torus {defines="torus"}

In classical topology, the two-dimensional torus $T^2$ may be defined
as the product of circles, i.e., $T^2$ may be defined as $S^1 \times
S^1$.  Alternatively, the space $T^2$ may be presented as a CW
complex, built by beginning with a point, attaching two 1-cells to
form the wedge of two circles, and finishing by attaching a 2-cell.

Such a CW complex can be regarded as a higher inductive type,
regarding the 0-cell as a constructor `base`{.Agda}, the two 1-cells
as distinct paths `base ≡ base`{.Agda}, and the 2-cell as a square
with its top and bottom edges attached to one of the 1-cells, and its
left and right edge attached to the other.

```agda
data T² : Type where
  base : T²
  loopA : base ≡ base
  loopB : base ≡ base
  square : Square loopA loopB loopB loopA
```

The resulting HIT is equivalent to the product of two circles.

```agda
open is-iso

T²≃S¹×S¹ : T² ≡ ( S¹ × S¹ )
T²≃S¹×S¹ = ua (T²→S¹×S¹ , is-iso→is-equiv iso-pf) where
  T²→S¹×S¹ : T² → S¹ × S¹
  T²→S¹×S¹ base = base , base
  T²→S¹×S¹ (loopA i) = loop i , base
  T²→S¹×S¹ (loopB j) = base , loop j
  T²→S¹×S¹ (square i j) = loop i , loop j

  S¹×S¹→T² : S¹ × S¹ → T²
  S¹×S¹→T² (base , base) =  base
  S¹×S¹→T² (base , loop j) = loopB j
  S¹×S¹→T² (loop i , base) = loopA i
  S¹×S¹→T² (loop i , loop j) = square i j

  iso-pf : is-iso T²→S¹×S¹
  iso-pf .from = S¹×S¹→T²
  iso-pf .rinv (base , base) = refl
  iso-pf .rinv (base , loop j) = refl
  iso-pf .rinv (loop i , base) = refl
  iso-pf .rinv (loop i , loop j) = refl

  iso-pf .linv base = refl
  iso-pf .linv (loopA i) = refl
  iso-pf .linv (loopB j) = refl
  iso-pf .linv (square i j) = refl
```

Showing that the torus described as a HIT is equivalent to the product
of two circles is Exercise 6.3 of the HoTT Book, but this exercise
includes a warning that "the path algebra for this is rather difficult".
The brevity of the above proof -- straightforward invocations of
`refl`{.Agda} -- is a testament to the strength of cubical methods.
