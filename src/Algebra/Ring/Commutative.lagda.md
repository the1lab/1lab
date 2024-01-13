<!--
```agda
open import 1Lab.Function.Embedding

open import Algebra.Prelude
open import Algebra.Ring
```
-->

```agda
module Algebra.Ring.Commutative where
```

<!--
```agda
open Ring-on using (_*_)
```
-->


# Commutative rings

This module is not very mathematically interesting: All it exists to do
is to package commutative rings together into one datum.

```agda
record CRing-on {ℓ} (R : Type ℓ) : Type ℓ where
  field
    has-ring-on : Ring-on R
    *-commutes  : ∀ {x y} → has-ring-on ._*_ x y ≡ has-ring-on ._*_ y x
  open Ring-on has-ring-on public


CRing-structure : ∀ ℓ → Thin-structure ℓ CRing-on
CRing-structure ℓ = Full-substructure ℓ CRing-on Ring-on emb (Ring-structure ℓ) where
  open CRing-on hiding (_↪_)
  emb : ∀ X → CRing-on X ↪ Ring-on X
  emb X .fst = has-ring-on
  emb X .snd y (r , p) (s , q) =
    Σ-pathp (λ i →
      record { has-ring-on = (p ∙ sym q) i
              ; *-commutes  = λ {x} {y} j →
                is-set→squarep (λ i j → CRing-on.has-is-set r)
                  (λ i → (p ∙ sym q) i ._*_ x y)
                  (r .*-commutes)
                  (s .*-commutes)
                  (λ i → (p ∙ sym q) i ._*_ y x)
                  i j
              })
      (commutes→square (∙-cancelr p q ∙ sym (∙-idr p)))

CRings : ∀ ℓ → Precategory (lsuc ℓ) ℓ
CRings ℓ = Structured-objects (CRing-structure ℓ)

CRing : ∀ ℓ → Type (lsuc ℓ)
CRing ℓ = CRings ℓ .Precategory.Ob

module CRing {ℓ} (R : CRing ℓ) where
  open CRing-on (R .snd) public

is-commutative-ring : ∀ {ℓ} (R : Ring ℓ) → Type _
is-commutative-ring R = ∀ {x y} → x R.* y ≡ y R.* x where
  module R = Ring-on (R .snd)
```
