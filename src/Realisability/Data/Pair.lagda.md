<!--
```agda
open import 1Lab.Prelude

open import Data.Partial.Total
open import Data.Partial.Base
open import Data.Vec.Base

open import Realisability.PCA

import Realisability.Data.Bool
import Realisability.PCA.Sugar
```
-->

```agda
module Realisability.Data.Pair {ℓ} (𝔸@(A , _) : PCA ℓ) where
```

<!--
```agda
open Realisability.PCA.Sugar 𝔸
open Realisability.Data.Bool 𝔸
private variable
  a b : ↯ ⌞ 𝔸 ⌟
```
-->

# Pairs in a PCA {defines="pairs-in-a-pca"}

```agda
`pair : ↯⁺ 𝔸
`pair = val ⟨ a ⟩ ⟨ b ⟩ ⟨ i ⟩ i `· a `· b

`fst : ↯⁺ 𝔸
`fst = val ⟨ p ⟩ p `· `true

`snd : ↯⁺ 𝔸
`snd = val ⟨ p ⟩ p `· `false

abstract
  `pair↓₂ : ⌞ a ⌟ → ⌞ b ⌟ → ⌞ `pair .fst % a % b ⌟
  `pair↓₂ {a} {b} ah bh = subst ⌞_⌟ (sym (abs-βₙ [] ((b , bh) ∷ (a , ah) ∷ []))) (abs↓ _ ((b , bh) ∷ (a , ah) ∷ []))

  `fst-β : ⌞ a ⌟ → ⌞ b ⌟ → `fst ⋆ (`pair ⋆ a ⋆ b) ≡ a
  `fst-β {a} {b} ah bh =
    `fst ⋆ (`pair ⋆ a ⋆ b)  ≡⟨ abs-β _ [] (_ , `pair↓₂ ah bh) ⟩
    `pair ⋆ a ⋆ b ⋆ `true   ≡⟨ abs-βₙ [] (`true ∷ (b , bh) ∷ (a , ah) ∷ []) ⟩
    `true ⋆ a ⋆ b           ≡⟨ `true-β ah bh ⟩
    a                       ∎

  `snd-β : ⌞ a ⌟ → ⌞ b ⌟ → `snd ⋆ (`pair ⋆ a ⋆ b) ≡ b
  `snd-β {a} {b} ah bh =
    `snd ⋆ (`pair ⋆ a ⋆ b)  ≡⟨ abs-β _ [] (_ , `pair↓₂ ah bh) ⟩
    `pair ⋆ a ⋆ b ⋆ `false  ≡⟨ abs-βₙ [] (`false ∷ (b , bh) ∷ (a , ah) ∷ []) ⟩
    `false ⋆ a ⋆ b          ≡⟨ `false-β ah bh ⟩
    b                       ∎
```
