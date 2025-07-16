<!--
```agda
open import 1Lab.Prelude

open import Data.Partial.Total
open import Data.Partial.Base
open import Data.Vec.Base

open import Realisability.PCA

import Realisability.Data.Bool
import Realisability.Data.Pair
import Realisability.PCA.Sugar
```
-->

```agda
module Realisability.Data.Sum {ℓ} (𝔸 : PCA ℓ) where
```

<!--
```agda
open Realisability.PCA.Sugar 𝔸
open Realisability.Data.Bool 𝔸
open Realisability.Data.Pair 𝔸

private variable
  x f g : ↯ ⌞ 𝔸 ⌟
```
-->

# Sums in a PCA {defines="sums-in-a-pca"}

```agda
`inl : ↯⁺ ⌞ 𝔸 ⌟
`inl = val ⟨ x ⟩ `pair `· `true `· x

`inr : ↯⁺ ⌞ 𝔸 ⌟
`inr = val ⟨ x ⟩ `pair `· `false `· x

`match : ↯⁺ ⌞ 𝔸 ⌟
`match = val ⟨ f ⟩ ⟨ g ⟩ ⟨ s ⟩ `fst `· s `· f `· g `· (`snd `· s)

abstract
  `inl↓₁ : ⌞ x ⌟ → ⌞ `inl ⋆ x ⌟
  `inl↓₁ {x} hx = subst ⌞_⌟ (sym (abs-β _ [] (x , hx))) (`pair↓₂ (`true .snd) hx)

  `inr↓₁ : ⌞ x ⌟ → ⌞ `inr ⋆ x ⌟
  `inr↓₁ {x} hx = subst ⌞_⌟ (sym (abs-β _ [] (x , hx))) (`pair↓₂ (`false .snd) hx)

  `match↓₂ : ⌞ f ⌟ → ⌞ g ⌟ → ⌞ `match ⋆ f ⋆ g ⌟
  `match↓₂ {f = f} {g} hf hg = subst ⌞_⌟ (sym (abs-βₙ [] ((g , hg) ∷ (f , hf) ∷ []))) (abs↓ _ _)

  `match-βl
    : ⌞ x ⌟ → ⌞ f ⌟ → ⌞ g ⌟
    → `match ⋆ f ⋆ g ⋆ (`inl ⋆ x) ≡ f ⋆ x
  `match-βl {x = x} {f} {g} hx hf hg =
    `match ⋆ f ⋆ g ⋆ (`inl ⋆ x)                                        ≡⟨ abs-βₙ [] ((`inl ⋆ x , `inl↓₁ hx) ∷ (g , hg) ∷ (f , hf) ∷ []) ⟩
    `fst ⋆ ⌜ `inl ⋆ x ⌝ ⋆ f ⋆ g ⋆ (`snd ⋆ ⌜ `inl ⋆ x ⌝)                ≡⟨ ap! (abs-β _ [] (x , hx)) ⟩
    `fst ⋆ (`pair ⋆ `true ⋆ x) ⋆ f ⋆ g ⋆ (`snd ⋆ (`pair ⋆ `true ⋆ x))  ≡⟨ ap₂ (λ e p → e % f % g % p) (`fst-β (`true .snd) hx) (`snd-β (`true .snd) hx) ⟩
    `true ⋆ f ⋆ g ⋆ x                                                  ≡⟨ ap (λ e → e ⋆ x) (`true-β hf hg) ⟩
    f ⋆ x                                                              ∎

  `match-βr
    : ⌞ x ⌟ → ⌞ f ⌟ → ⌞ g ⌟
    → `match ⋆ f ⋆ g ⋆ (`inr ⋆ x) ≡ g ⋆ x
  `match-βr {x = x} {f} {g} hx hf hg =
    `match ⋆ f ⋆ g ⋆ (`inr ⋆ x)                                          ≡⟨ abs-βₙ [] ((`inr ⋆ x , `inr↓₁ hx) ∷ (g , hg) ∷ (f , hf) ∷ []) ⟩
    `fst ⋆ ⌜ `inr ⋆ x ⌝ ⋆ f ⋆ g ⋆ (`snd ⋆ ⌜ `inr ⋆ x ⌝)                  ≡⟨ ap! (abs-β _ [] (x , hx)) ⟩
    `fst ⋆ (`pair ⋆ `false ⋆ x) ⋆ f ⋆ g ⋆ (`snd ⋆ (`pair ⋆ `false ⋆ x))  ≡⟨ ap₂ (λ e p → e % f % g % p) (`fst-β (`false .snd) hx) (`snd-β (`false .snd) hx) ⟩
    `false ⋆ f ⋆ g ⋆ x                                                   ≡⟨ ap (λ e → e ⋆ x) (`false-β hf hg) ⟩
    g ⋆ x                                                                ∎
```
