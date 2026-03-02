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
module Realisability.Data.Bool {ℓ} (𝔸 : PCA ℓ) where
```

<!--
```agda
open S 𝔸
private variable
  ℓ' : Level
  V A B C : Type ℓ'
  a b : ↯ ⌞ 𝔸 ⌟
```
-->

# Booleans in a PCA {defines="booleans-in-a-pca"}

We construct [[booleans]] in a [[partial combinatory algebra]] by
defining boolean values to be functions which select one of their two
arguments. In effect, we are defining booleans so that the program
$$
\tt{if}\ b\ \tt{then}\ x\ \tt{else}\ y
$$
is simply $b\, x\, y$. Therefore, we have:

```agda
`true : ↯⁺ 𝔸
`true = val ⟨ x ⟩ ⟨ y ⟩ x

`false : ↯⁺ 𝔸
`false = val ⟨ x ⟩ ⟨ y ⟩ y
```

We define an overloaded notation for constructing terms which case on a
boolean.

```agda
`if_then_else_
  : ⦃ _ : To-term V A ⦄ ⦃ _ : To-term V B ⦄ ⦃ _ : To-term V C ⦄
  → A → B → C → Termʰ V
`if x then y else z = x `· y `· z
```

We can prove the following properties: applying `` `true ``{.Agda} and
`` `false ``{.Agda} to a single argument results in a defined value;
`` `true ``{.Agda} selects its first argument; and `` `false ``{.Agda}
selects its second argument.

```agda
abstract
  `true↓₁ : ⌞ a ⌟ → ⌞ `true ⋆ a ⌟
  `true↓₁ x = subst ⌞_⌟ (sym (abs-βₙ []v ((_ , x) ∷v []v))) (abs↓ _ _)

  `false↓₁ : ⌞ a ⌟ → ⌞ `false ⋆ a ⌟
  `false↓₁ ah = subst ⌞_⌟ (sym (abs-βₙ []v ((_ , ah) ∷v []v))) (abs↓ _ _)

  `true-β : ⌞ a ⌟ → ⌞ b ⌟ → `true ⋆ a ⋆ b ≡ a
  `true-β {a} {b} ah bh = abs-βₙ []v ((b , bh) ∷v (a , ah) ∷v []v)

  `false-β : ⌞ a ⌟ → ⌞ b ⌟ → `false ⋆ a ⋆ b ≡ b
  `false-β {a} {b} ah bh = abs-βₙ []v ((b , bh) ∷v (a , ah) ∷v []v)
```

We can define negation using `` `if_then_else_ ``{.Agda}, and show that
it computes as expected.

```agda
`not : ↯⁺ 𝔸
`not = val ⟨ x ⟩ `if x then `false else `true

abstract
  `not-βt : `not ⋆ `true ≡ `false .fst
  `not-βt = abs-β _ []v `true ∙ abs-βₙ []v (`true ∷v `false ∷v []v)

  `not-βf : `not ⋆ `false ≡ `true .fst
  `not-βf = abs-β _ []v `false ∙ abs-βₙ []v (`true ∷v `false ∷v []v)
```
