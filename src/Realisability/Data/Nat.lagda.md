<!--
```agda
open import 1Lab.Prelude

open import Data.Partial.Total
open import Data.Partial.Base
open import Data.Vec.Base

open import Realisability.PCA

import Realisability.PCA.Fixpoint
import Realisability.Data.Pair
import Realisability.PCA.Sugar
```
-->

```agda
module Realisability.Data.Nat {ℓ} (𝔸 : PCA ℓ) where
```

<!--
```agda
open Realisability.PCA.Fixpoint 𝔸
open Realisability.PCA.Sugar 𝔸
open Realisability.Data.Pair 𝔸
```
-->

# Natural numbers in a PCA

```agda
`zero : ↯⁺ 𝔸
`zero = val ⟨ x ⟩ x

`suc : ↯⁺ 𝔸
`suc = val ⟨ x ⟩ `pair `· `false `· x

`num : Nat → ↯⁺ 𝔸
`num zero    = `zero
`num (suc x) = record
  { fst = `pair ⋆ `false ⋆ `num x
  ; snd = `pair↓₂ (abs↓ _ _) (`num x .snd)
  }

`pred : ↯⁺ 𝔸
`pred = val ⟨ x ⟩ `fst `· x `· `zero `· (`snd `· x)

`iszero : ↯⁺ 𝔸
`iszero = `fst

private
  variable f g x y z : ↯ ⌞ 𝔸 ⌟

  `worker : ↯⁺ 𝔸
  `worker = val ⟨ rec ⟩ ⟨ zc ⟩ ⟨ sc ⟩ ⟨ num ⟩
    `iszero `· num
      `· (`true `· zc)
      `· (⟨ y ⟩ sc `· (`pred `· num) `· (rec `· zc `· sc `· (`pred `· num) `· `zero))

`primrec : ↯⁺ 𝔸
`primrec = val ⟨ z ⟩ ⟨ s ⟩ ⟨ n ⟩ `Z `· `worker `· z `· s `· n `· `zero

abstract
  `num-suc : ∀ x → `num (suc x) .fst ≡ `suc ⋆ `num x
  `num-suc x = sym (abs-β _ _ (`num x))

  `suc↓₁ : ∀ {a} → ⌞ a ⌟ → ⌞ `suc .fst % a ⌟
  `suc↓₁ ah = subst ⌞_⌟ (sym (abs-βₙ [] ((_ , ah) ∷ []))) (`pair↓₂ (`false .snd) ah)

  `iszero-zero : `iszero ⋆ `zero ≡ `true .fst
  `iszero-zero = abs-β _ _ `zero ∙ abs-β _ _ (_ , abs↓ _ _)

  `iszero-suc : ⌞ x ⌟ → `iszero ⋆ (`suc ⋆ x) ≡ `false .fst
  `iszero-suc {x} xh =
    `iszero ⋆ (`suc ⋆ x)           ≡⟨ ap (`iszero ⋆_) (abs-β _ _ (_ , xh)) ⟩
    `iszero ⋆ (`pair ⋆ `false ⋆ x) ≡⟨ `fst-β (`false .snd) xh ⟩
    `false .fst                    ∎

  `pred-zero : `pred ⋆ `zero ≡ `zero .fst
  `pred-zero =
    `pred ⋆ `zero                             ≡⟨ abs-β _ _ `zero ⟩
    ⌜ `fst ⋆ `zero ⌝ ⋆ `zero ⋆ (`snd ⋆ `zero) ≡⟨ ap! (`iszero-zero) ⟩
    `true ⋆ `zero ⋆ (`snd ⋆ `zero)            ≡⟨ abs-βₙ [] ((_ , subst ⌞_⌟ (sym rem₁) (abs↓ _ _)) ∷ `zero ∷ []) ⟩
    `zero .fst                                ∎
    where
      rem₁ : `snd ⋆ `zero ≡ `false .fst
      rem₁ = abs-β _ _ `zero ∙ abs-β _ _ `false

  `pred-suc : ⌞ x ⌟ → `pred ⋆ (`suc ⋆ x) ≡ x
  `pred-suc {x} xh =
    `pred ⋆ (`suc ⋆ x)                                   ≡⟨ abs-β _ _ (_ , `suc↓₁ xh) ⟩
    ⌜ `fst ⋆ (`suc ⋆ x) ⌝ ⋆ `zero ⋆ (`snd ⋆ (`suc ⋆ x))  ≡⟨ ap! (ap (`fst ⋆_) (abs-β _ _ (_ , xh)) ∙ `fst-β (`false .snd) xh) ⟩
    `false ⋆ `zero ⋆ ⌜ `snd ⋆ (`suc ⋆ x) ⌝               ≡⟨ ap! (ap (`snd ⋆_) (abs-β _ _ (_ , xh)) ∙ `snd-β (`false .snd) xh) ⟩
    `false ⋆ `zero ⋆ x                                   ≡⟨ abs-βₙ [] ((_ , xh) ∷ `zero ∷ []) ⟩
    x                                                    ∎

  `primrec-zero : ⌞ z ⌟ → ⌞ f ⌟ → `primrec ⋆ z ⋆ f ⋆ `zero ≡ z
  `primrec-zero {z} {f} zh fh =
    `primrec ⋆ z ⋆ f ⋆ `zero                                     ≡⟨ abs-βₙ [] (`zero ∷ (_ , fh) ∷ (_ , zh) ∷ []) ⟩
    ⌜ `Z ⋆ `worker ⋆ z ⌝ ⋆ f ⋆ `zero ⋆ `zero                     ≡⟨ ap! (`Z-β (`worker .snd) zh) ⟩
    ⌜ `worker ⋆ (`Z ⋆ `worker) ⋆ z ⋆ f ⋆ `zero ⌝ ⋆ `zero         ≡⟨ ap (λ e → e % `zero .fst) (abs-βₙ [] (`zero ∷ (_ , fh) ∷ (_ , zh) ∷ (_ , `Z↓₁ (`worker .snd)) ∷ [])) ⟩
    ⌜ `iszero ⋆ `zero ⋆ (`true ⋆ z) ⌝ % _ % `zero .fst           ≡⟨ ap₂ _%_ (ap₂ _%_ (ap₂ _%_ `iszero-zero refl) refl ∙ `true-β (`true↓₁ zh) (abs↓ _ _)) refl ⟩
    `true ⋆ z ⋆ `zero .fst                                       ≡⟨ `true-β zh (`zero .snd) ⟩
    z                                                            ∎

  `primrec-suc : ⌞ z ⌟ → ⌞ f ⌟ → ⌞ x ⌟ → `primrec ⋆ z ⋆ f ⋆ (`suc ⋆ x) ≡ f ⋆ x ⋆ (`primrec ⋆ z ⋆ f ⋆ x)
  `primrec-suc {z} {f} {x} zh fh xh =
    `primrec ⋆ z ⋆ f ⋆ (`suc ⋆ x)                                                 ≡⟨ abs-βₙ [] ((_ , `suc↓₁ xh) ∷ (_ , fh) ∷ (_ , zh) ∷ []) ⟩
    ⌜ `Z ⋆ `worker ⋆ z ⌝ ⋆ f ⋆ (`suc ⋆ x) ⋆ `zero                                 ≡⟨ ap! (`Z-β (`worker .snd) zh) ⟩
    `worker ⋆ (`Z ⋆ `worker) ⋆ z ⋆ f ⋆ (`suc ⋆ x) ⋆ `zero                         ≡⟨ ap (λ e → e % `zero .fst) (abs-βₙ [] ((_ , `suc↓₁ xh) ∷ (_ , fh) ∷ (_ , zh) ∷ (_ , `Z↓₁ (`worker .snd)) ∷ [])) ⟩
    `iszero ⋆ (`suc ⋆ x) ⋆ (`true ⋆ z) % _ % `zero .fst                           ≡⟨ ap₂ _%_ (ap₂ _%_ (ap₂ _%_ (`iszero-suc xh) refl) refl ∙ `false-β (`true↓₁ zh) (abs↓ _ _)) refl ∙ abs-βₙ ((`suc ⋆ x , `suc↓₁ xh) ∷ (f , fh) ∷ (z , zh) ∷ (`Z ⋆ `worker , `Z↓₁ (`worker .snd)) ∷ []) (`zero ∷ []) ⟩
    f % `pred ⋆ (`suc ⋆ x) % `Z ⋆ `worker ⋆ z ⋆ f ⋆ (`pred ⋆ (`suc ⋆ x)) ⋆ `zero  ≡⟨ ap (λ e → f % e % `Z ⋆ `worker ⋆ z ⋆ f ⋆ e ⋆ `zero) (`pred-suc xh) ⟩
    f ⋆ x ⋆ (`Z ⋆ `worker ⋆ z ⋆ f ⋆ x ⋆ `zero)                                    ≡⟨ ap₂ _%_ refl (sym (abs-βₙ [] ((_ , xh) ∷ (_ , fh) ∷ (_ , zh) ∷ []))) ⟩
    f ⋆ x ⋆ (`primrec ⋆ z ⋆ f ⋆ x)                                                ∎
```
