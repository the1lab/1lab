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
module Realisability.Data.Pair
```

<!--
```agda
  {ℓ} {A : Type ℓ} {_%_ : ↯ A → ↯ A → ↯ A} (pca : is-pca _%_)
  (let infixl 8 _%_; _%_ = _%_)
  where

open S pca
```
-->

# Pairs in a PCA

```agda
`true : ↯⁺ A
`true = val ⟨ x ⟩ ⟨ y ⟩ x

`false : ↯⁺ A
`false = val ⟨ x ⟩ ⟨ y ⟩ y

abstract
  `false-β : {a b : ↯ A} → ⌞ a ⌟ → ⌞ b ⌟ → `false ⋆ a ⋆ b ≡ b
  `false-β {a} {b} ah bh = abs-βₙ [] ((b , bh) ∷ (a , ah) ∷ [])

  `true-β : {a b : ↯ A} → ⌞ a ⌟ → ⌞ b ⌟ → `true ⋆ a ⋆ b ≡ a
  `true-β {a} {b} ah bh = abs-βₙ [] ((b , bh) ∷ (a , ah) ∷ [])

`pair : ↯⁺ A
`pair = val ⟨ a ⟩ ⟨ b ⟩ ⟨ i ⟩ i `· a `· b

abstract
  `pair↓₂ : ∀ {a b} → ⌞ a ⌟ → ⌞ b ⌟ → ⌞ `pair .fst % a % b ⌟
  `pair↓₂ {a} {b} ah bh = subst ⌞_⌟ (sym (abs-βₙ [] ((b , bh) ∷ (a , ah) ∷ []))) (abs↓ _ ((b , bh) ∷ (a , ah) ∷ []))

`fst : ↯⁺ A
`fst = val ⟨ p ⟩ p `· `true

`snd : ↯⁺ A
`snd = val ⟨ p ⟩ p `· `false

`fst-β : ∀ {a b} → ⌞ a ⌟ → ⌞ b ⌟ → `fst ⋆ (`pair ⋆ a ⋆ b) ≡ a
`fst-β {a} {b} ah bh =
  `fst ⋆ (`pair ⋆ a ⋆ b)  ≡⟨ abs-β _ [] (_ , `pair↓₂ ah bh) ⟩
  `pair ⋆ a ⋆ b ⋆ `true   ≡⟨ abs-βₙ [] (`true ∷ (b , bh) ∷ (a , ah) ∷ []) ⟩
  `true ⋆ a ⋆ b           ≡⟨ `true-β ah bh ⟩
  a                       ∎

`snd-β : ∀ {a b} → ⌞ a ⌟ → ⌞ b ⌟ → `snd ⋆ (`pair ⋆ a ⋆ b) ≡ b
`snd-β {a} {b} ah bh =
  `snd ⋆ (`pair ⋆ a ⋆ b)  ≡⟨ abs-β _ [] (_ , `pair↓₂ ah bh) ⟩
  `pair ⋆ a ⋆ b ⋆ `false  ≡⟨ abs-βₙ [] (`false ∷ (b , bh) ∷ (a , ah) ∷ []) ⟩
  `false ⋆ a ⋆ b          ≡⟨ `false-β ah bh ⟩
  b                       ∎
```
