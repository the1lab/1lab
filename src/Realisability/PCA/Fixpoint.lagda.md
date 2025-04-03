<!--
```agda
open import 1Lab.Prelude

open import Data.Partial.Total
open import Data.Partial.Base
open import Data.Vec.Base

open import Realisability.PCA

import Realisability.Data.Pair
import Realisability.PCA.Sugar
```
-->

```agda
module Realisability.PCA.Fixpoint {ℓ} (𝔸 : PCA ℓ) where
```

<!--
```agda
open Realisability.PCA.Sugar 𝔸
open Realisability.Data.Pair 𝔸

private variable x y : ↯ ⌞ 𝔸 ⌟
```
-->

# Fixed-point combinators in a PCA

```agda
`X : ↯⁺ 𝔸
`X = val ⟨ x ⟩ ⟨ y ⟩ ⟨ z ⟩ y `· (x `· x `· y) `· z

`Z : ↯⁺ 𝔸
`Z = record
  { fst = `X ⋆ `X
  ; snd = subst ⌞_⌟ (sym (abs-βₙ [] (`X ∷ []))) (abs↓ _ _)
  }

abstract
  `Z↓₁ : ⌞ x ⌟ → ⌞ `Z ⋆ x ⌟
  `Z↓₁ {x} xh = subst ⌞_⌟ (sym (abs-βₙ [] ((x , xh) ∷ `X ∷ []))) (abs↓ _ _)

  `Z-β : ⌞ x ⌟ → ⌞ y ⌟ → `Z ⋆ x ⋆ y ≡ x ⋆ (`Z ⋆ x) ⋆ y
  `Z-β {x} {y} xh yh =
    `X ⋆ `X ⋆ x ⋆ y        ≡⟨ abs-βₙ [] ((y , yh) ∷ (x , xh) ∷ `X ∷ []) ⟩
    x ⋆ (`X ⋆ `X ⋆ x) ⋆ y  ≡⟨⟩
    x ⋆ (`Z ⋆ x) ⋆ y       ∎
```
