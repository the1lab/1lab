<!--
```agda
open import Cat.Prelude

open import Order.Diagram.Join
open import Order.Lattice
open import Order.Base

import Order.Diagram.Join.Reasoning as Joins
import Order.Diagram.Meet.Reasoning as Meets
import Order.Reasoning as Pos
```
-->

```agda
module Order.Lattice.Reasoning {o ℓ} {P : Poset o ℓ} (lat : is-lattice P) where
```

<!--
```agda
open is-lattice lat
open Pos P
```
-->

# Reasoning in lattices

```agda
open Joins {P = P} ∪-joins public
open Meets {P = P} ∩-meets public

abstract
  ∪-∩-distrib≤ : ∀ {x y z} → (x ∩ y) ∪ (x ∩ z) ≤ x ∩ (y ∪ z)
  ∪-∩-distrib≤ = ∪-universal _
    (∩-universal _ ∩≤l (≤-trans ∩≤r l≤∪))
    (∩-universal _ ∩≤l (≤-trans ∩≤r r≤∪))

  ∩-absorbr : ∀ {x y} → (x ∪ y) ∩ x ≡ x
  ∩-absorbr = ≤-antisym ∩≤r (∩-universal _ l≤∪ ≤-refl)

  ∩-absorbl : ∀ {x y} → x ∩ (x ∪ y) ≡ x
  ∩-absorbl = ∩-comm ∙ ∩-absorbr

  ∪-absorbr : ∀ {x y} → (x ∩ y) ∪ x ≡ x
  ∪-absorbr = ≤-antisym (∪-universal _ ∩≤l ≤-refl) r≤∪

  ∪-absorbl : ∀ {x y} → x ∪ (x ∩ y) ≡ x
  ∪-absorbl = ∪-comm ∙ ∪-absorbr
```

<!--
```agda
open is-lattice lat using (_∩_ ; _∪_ ; top ; ! ; bot ; ¡) public
```
-->
