<!--
```agda
open import 1Lab.Prelude hiding (_*_ ; _+_ ; _-_)

open import Algebra.Monoid
open import Algebra.Ring
```
-->

```agda
module Algebra.Ring.Reasoning {ℓ} (R : Ring ℓ) where
```

# Reasoning combinators for rings

<!--
```agda
open Ring-on (R .snd) public

private variable
  a b c x y z : ⌞ R ⌟
```
-->

```agda
*-zerol : 0r * x ≡ 0r
*-zerol {x} =
  0r * x                       ≡⟨ a.introl a.inversel ⟩
  (- 0r * x) + 0r * x + 0r * x ≡⟨ a.pullr (sym *-distribr) ⟩
  (- 0r * x) + (0r + 0r) * x   ≡⟨ ap₂ _+_ refl (ap (_* x) a.idl) ⟩
  (- 0r * x) + 0r * x          ≡⟨ a.inversel ⟩
  0r                           ∎

*-zeror : x * 0r ≡ 0r
*-zeror {x} =
  x * 0r                     ≡⟨ a.intror a.inverser ⟩
  x * 0r + (x * 0r - x * 0r) ≡⟨ a.pulll (sym *-distribl) ⟩
  x * (0r + 0r) - x * 0r     ≡⟨ ap₂ _-_ (ap (x *_) a.idl) refl ⟩
  x * 0r - x * 0r            ≡⟨ a.inverser ⟩
  0r                         ∎

*-negatel : (- x) * y ≡ - (x * y)
*-negatel {x} {y} = monoid-inverse-unique a.has-is-monoid (x * y) ((- x) * y) (- (x * y))
  (sym *-distribr ·· ap (_* y) a.inversel ·· *-zerol)
  a.inverser

*-negater : x * (- y) ≡ - (x * y)
*-negater {x} {y} = monoid-inverse-unique a.has-is-monoid (x * y) (x * (- y)) (- (x * y))
  (sym *-distribl ·· ap (x *_) a.inversel ·· *-zeror)
  a.inverser
```
