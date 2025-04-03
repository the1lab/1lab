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
module Realisability.Data.Pair {ℓ} (𝔸@(A , _) : PCA ℓ) where
```

<!--
```agda
open S 𝔸
private variable
  a b : ↯ ⌞ 𝔸 ⌟
```
-->

# Pairs in a PCA

```agda
`true : ↯⁺ 𝔸
`true = val ⟨ x ⟩ ⟨ y ⟩ x

`false : ↯⁺ 𝔸
`false = val ⟨ x ⟩ ⟨ y ⟩ y

`pair : ↯⁺ 𝔸
`pair = val ⟨ a ⟩ ⟨ b ⟩ ⟨ i ⟩ i `· a `· b

`fst : ↯⁺ 𝔸
`fst = val ⟨ p ⟩ p `· `true

`snd : ↯⁺ 𝔸
`snd = val ⟨ p ⟩ p `· `false

abstract
  `false-β : ⌞ a ⌟ → ⌞ b ⌟ → `false ⋆ a ⋆ b ≡ b
  `false-β {a} {b} ah bh = abs-βₙ [] ((b , bh) ∷ (a , ah) ∷ [])

  `true-β : ⌞ a ⌟ → ⌞ b ⌟ → `true ⋆ a ⋆ b ≡ a
  `true-β {a} {b} ah bh = abs-βₙ [] ((b , bh) ∷ (a , ah) ∷ [])

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
