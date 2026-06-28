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
module Realisability.Data.Pair {ℓ} (𝔸 : PCA ℓ) where
```

<!--
```agda
open Realisability.PCA.Sugar 𝔸
open Realisability.Data.Bool 𝔸
private variable
  a b : ↯ ⌞ 𝔸 ⌟
  ℓ' : Level
  V A B : Type ℓ'
```
-->

# Pairs in a PCA {defines="pairs-in-a-pca"}

We define an encoding for pairs in a [[partial combinatory algebra]] in
terms of the encoding of [[booleans in a PCA]]. The pairing of $a$ and
$b$ is the function
$$
\langle i \rangle \tt{if}\ i\ \tt{then}\ a\ \tt{else}\ b
$$,
and the pairing *function* is this abstracted over $a$ and $b$.

```agda
`pair : ↯⁺ 𝔸
`pair = val ⟨ a ⟩ ⟨ b ⟩ ⟨ i ⟩ `if i then a else b
```

<!--
```agda
_`,_
  : ⦃ _ : To-term V A ⦄ ⦃ _ : To-term V B ⦄
  → A → B → Termʰ V
a `, b = `pair `· a `· b

infixr 24 _`,_
```
-->

The projection functions simply apply a pair to either `` `true
``{.Agda} or `` `false ``{.Agda} depending.

```agda
`fst : ↯⁺ 𝔸
`fst = val ⟨ p ⟩ p `· `true

`snd : ↯⁺ 𝔸
`snd = val ⟨ p ⟩ p `· `false
```

Our standard battery of lemmas follows: `` `pair ``{.Agda} is defined
when applied to two arguments, and the first and second projections
compute as expected.

```agda
abstract
  `pair↓₂ : ⌞ a ⌟ → ⌞ b ⌟ → ⌞ `pair ⋆ a ⋆ b ⌟
  `pair↓₂ {a} {b} ah bh = subst ⌞_⌟ (sym $ abs-βₙ []v ((b , bh) ∷v (a , ah) ∷v []v)) (abs↓ _ _)

  `fst-β : ⌞ a ⌟ → ⌞ b ⌟ → `fst ⋆ (`pair ⋆ a ⋆ b) ≡ a
  `fst-β {a} {b} ah bh =
    `fst ⋆ (`pair ⋆ a ⋆ b)  ≡⟨ abs-β _ []v (_ , `pair↓₂ ah bh) ⟩
    `pair ⋆ a ⋆ b ⋆ `true   ≡⟨ abs-βₙ []v (`true ∷v (b , bh) ∷v (a , ah) ∷v []v) ⟩
    `true ⋆ a ⋆ b           ≡⟨ `true-β ah bh ⟩
    a                       ∎

  `snd-β : ⌞ a ⌟ → ⌞ b ⌟ → `snd ⋆ (`pair ⋆ a ⋆ b) ≡ b
  `snd-β {a} {b} ah bh =
    `snd ⋆ (`pair ⋆ a ⋆ b)  ≡⟨ abs-β _ []v (_ , `pair↓₂ ah bh) ⟩
    `pair ⋆ a ⋆ b ⋆ `false  ≡⟨ abs-βₙ []v (`false ∷v (b , bh) ∷v (a , ah) ∷v []v) ⟩
    `false ⋆ a ⋆ b          ≡⟨ `false-β ah bh ⟩
    b                       ∎
```
