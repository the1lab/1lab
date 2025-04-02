<!--
```agda
open import 1Lab.Prelude

open import Data.Partial.Total
open import Data.Partial.Base
open import Data.Vec.Base

open import Realisability.PCA

import Realisability.Data.Pair as pairs
import Realisability.PCA.Sugar as S
```
-->

```agda
module Realisability.Data.Sum
```

<!--
```agda
  {ℓ} {A : Type ℓ} {_%_ : ↯ A → ↯ A → ↯ A} (pca : is-pca _%_)
  (let infixl 8 _%_; _%_ = _%_)
  where

open S pca
open pairs pca
```
-->

# Sums in a PCA

```agda
`inl : ↯⁺ A
`inl = val ⟨ x ⟩ `pair `· `true `· x

`inr : ↯⁺ A
`inr = val ⟨ x ⟩ `pair `· `false `· x

`match : ↯⁺ A
`match = val ⟨ f ⟩ ⟨ g ⟩ ⟨ s ⟩ `fst `· s `· f `· g `· (`snd `· s)

abstract
  `inl↓₁ : {x : ↯ A} → ⌞ x ⌟ → ⌞ `inl ⋆ x ⌟
  `inl↓₁ {x} hx = subst ⌞_⌟ (sym (abs-β _ [] (x , hx))) (`pair↓₂ (`true .snd) hx)

  `inr↓₁ : {x : ↯ A} → ⌞ x ⌟ → ⌞ `inr ⋆ x ⌟
  `inr↓₁ {x} hx = subst ⌞_⌟ (sym (abs-β _ [] (x , hx))) (`pair↓₂ (`false .snd) hx)

  `match↓₂ : {f g : ↯ A} → ⌞ f ⌟ → ⌞ g ⌟ → ⌞ `match ⋆ f ⋆ g ⌟
  `match↓₂ {f = f} {g} hf hg = subst ⌞_⌟ (sym (abs-βₙ [] ((g , hg) ∷ (f , hf) ∷ []))) (abs↓ _ _)

  `match-βl
    : {x f g : ↯ A} → ⌞ x ⌟ → ⌞ f ⌟ → ⌞ g ⌟
    → `match ⋆ f ⋆ g ⋆ (`inl ⋆ x) ≡ f ⋆ x
  `match-βl {x = x} {f} {g} hx hf hg =
    `match ⋆ f ⋆ g ⋆ (`inl ⋆ x)                                        ≡⟨ abs-βₙ [] ((`inl ⋆ x , `inl↓₁ hx) ∷ (g , hg) ∷ (f , hf) ∷ []) ⟩
    `fst ⋆ ⌜ `inl ⋆ x ⌝ ⋆ f ⋆ g ⋆ (`snd ⋆ ⌜ `inl ⋆ x ⌝)                ≡⟨ ap! (abs-β _ [] (x , hx)) ⟩
    `fst ⋆ (`pair ⋆ `true ⋆ x) ⋆ f ⋆ g ⋆ (`snd ⋆ (`pair ⋆ `true ⋆ x))  ≡⟨ ap₂ (λ e p → e % f % g % p) (`fst-β (`true .snd) hx) (`snd-β (`true .snd) hx) ⟩
    `true ⋆ f ⋆ g ⋆ x                                                  ≡⟨ ap (λ e → e ⋆ x) (`true-β hf hg) ⟩
    f ⋆ x                                                              ∎

  `match-βr
    : ∀ {x f g : ↯ A} → ⌞ x ⌟ → ⌞ f ⌟ → ⌞ g ⌟
    → `match ⋆ f ⋆ g ⋆ (`inr ⋆ x) ≡ g ⋆ x
  `match-βr {x = x} {f} {g} hx hf hg =
    `match ⋆ f ⋆ g ⋆ (`inr ⋆ x)                                          ≡⟨ abs-βₙ [] ((`inr ⋆ x , `inr↓₁ hx) ∷ (g , hg) ∷ (f , hf) ∷ []) ⟩
    `fst ⋆ ⌜ `inr ⋆ x ⌝ ⋆ f ⋆ g ⋆ (`snd ⋆ ⌜ `inr ⋆ x ⌝)                  ≡⟨ ap! (abs-β _ [] (x , hx)) ⟩
    `fst ⋆ (`pair ⋆ `false ⋆ x) ⋆ f ⋆ g ⋆ (`snd ⋆ (`pair ⋆ `false ⋆ x))  ≡⟨ ap₂ (λ e p → e % f % g % p) (`fst-β (`false .snd) hx) (`snd-β (`false .snd) hx) ⟩
    `false ⋆ f ⋆ g ⋆ x                                                   ≡⟨ ap (λ e → e ⋆ x) (`false-β hf hg) ⟩
    g ⋆ x                                                                ∎
```
