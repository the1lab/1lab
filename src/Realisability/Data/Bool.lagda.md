<!--
```agda
open import 1Lab.Prelude

open import Data.Partial.Total
open import Data.Partial.Base
open import Data.Vec.Base

open import Realisability.PCA

import Realisability.PCA.Sugar as S
```
-->

```agda
module Realisability.Data.Bool {ℓ} (𝔸@(A , _) : PCA ℓ) where
```

<!--
```agda
open S 𝔸
private variable
  a b : ↯ ⌞ 𝔸 ⌟
```
-->

# Booleans in a PCA {defines="booleans-in-a-pca"}

```agda
`true : ↯⁺ 𝔸
`true = val ⟨ x ⟩ ⟨ y ⟩ x

`false : ↯⁺ 𝔸
`false = val ⟨ x ⟩ ⟨ y ⟩ y

`not : ↯⁺ A
`not = val ⟨ x ⟩ x `· `false `· `true

abstract
  `true↓₁ : ⌞ a ⌟ → ⌞ `true ⋆ a ⌟
  `true↓₁ x = subst ⌞_⌟ (sym (abs-βₙ [] ((_ , x) ∷ []))) (abs↓ _ _)

  `false↓₁ : ⌞ a ⌟ → ⌞ `false .fst % a ⌟
  `false↓₁ ah = subst ⌞_⌟ (sym (abs-βₙ [] ((_ , ah) ∷ []))) (abs↓ _ _)

  `false-β : ⌞ a ⌟ → ⌞ b ⌟ → `false ⋆ a ⋆ b ≡ b
  `false-β {a} {b} ah bh = abs-βₙ [] ((b , bh) ∷ (a , ah) ∷ [])

  `true-β : ⌞ a ⌟ → ⌞ b ⌟ → `true ⋆ a ⋆ b ≡ a
  `true-β {a} {b} ah bh = abs-βₙ [] ((b , bh) ∷ (a , ah) ∷ [])

  `not-βt : `not ⋆ `true ≡ `false .fst
  `not-βt = abs-β _ [] `true ∙ abs-βₙ [] (`true ∷ `false ∷ [])

  `not-βf : `not ⋆ `false ≡ `true .fst
  `not-βf = abs-β _ [] `false ∙ abs-βₙ [] (`true ∷ `false ∷ [])
```
