<!--
```agda
open import 1Lab.Prelude

open import Data.Partial.Total
open import Data.Partial.Base
open import Data.Vec.Base

open import Realisability.PCA

import Realisability.Data.Pair as pairs
import Realisability.PCA.Sugar as S
import Realisability.Data.Sum as sums
```
-->

```agda
module Realisability.Base
  {ℓ} {𝔸 : Type ℓ} {_%_ : ↯ 𝔸 → ↯ 𝔸 → ↯ 𝔸} (p : is-pca _%_)
  where
```

<!--
```agda
open pairs p
open sums p
open S p

private variable
  ℓ' ℓ'' : Level
  X Y Z : Type ℓ'
  n : Nat
```
-->

# Realisability logic

```agda
record [_]_⊢_ (f : X → Y) (P : X → ℙ⁺ 𝔸) (Q : Y → ℙ⁺ 𝔸) : Type (level-of X ⊔ level-of Y ⊔ ℓ) where
  field
    realiser : ↯⁺ 𝔸
    tracks   : ∀ {x} (a : ↯ 𝔸) (ah : a ∈ P x) → realiser ⋆ a ∈ Q (f x)

  realiser↓ : ∀ {x} (a : ↯ 𝔸) (ah : a ∈ P x) → ⌞ realiser ⋆ a ⌟
  realiser↓ a ah = Q _ .defined (tracks a ah)
```

<!--
```agda
private unquoteDecl eqv' = declare-record-iso eqv' (quote [_]_⊢_)

open [_]_⊢_

instance
  tracks-to-term : ∀ {V : Type} {P : X → ℙ⁺ 𝔸} {Q : Y → ℙ⁺ 𝔸} {f : X → Y} → To-term V ([ f ] P ⊢ Q)
  tracks-to-term = record { to = λ x → const (x .realiser) }

  tracks-to-part : ∀ {P : X → ℙ⁺ 𝔸} {Q : Y → ℙ⁺ 𝔸} {f : X → Y} → To-part ([ f ] P ⊢ Q) 𝔸
  tracks-to-part = record { to-part = λ x → x .realiser .fst }

private
  variable P Q R : X → ℙ⁺ 𝔸

  subst-∈ : (P : ℙ⁺ 𝔸) {x y : ↯ 𝔸} → x ∈ P → y ≡ x → y ∈ P
  subst-∈ P hx p = subst (_∈ P) (sym p) hx
```
-->

## Basic structural rules

```agda
id⊢ : [ id ] P ⊢ P
id⊢ {P = P} = record
  { realiser = val ⟨ x ⟩ x
  ; tracks   = λ {x} a ha → subst-∈ (P x) ha (abs-β _ [] (a , P x .defined ha))
  }

_∘⊢_ : ∀ {f g} → [ g ] Q ⊢ R → [ f ] P ⊢ Q → [ g ∘ f ] P ⊢ R
_∘⊢_ {R = R} {P = P} α β = record
  { realiser = val ⟨ x ⟩ α `· (β `· x)
  ; tracks   = λ a ha → subst-∈ (R _) (α .tracks (β ⋆ a) (β .tracks a ha)) $
      (val ⟨ x ⟩ α `· (β `· x)) ⋆ a ≡⟨ abs-β _ [] (a , P _ .defined ha) ⟩
      α ⋆ (β ⋆ a)                   ∎
  }
```

## Conjunction

```agda
_∧T_ : (P Q : X → ℙ⁺ 𝔸) → X → ℙ⁺ 𝔸
(P ∧T Q) x = record
  { mem     = λ a → elΩ (Σ[ u ∈ ↯⁺ 𝔸 ] Σ[ v ∈ ↯⁺ 𝔸 ] (a ≡ `pair ⋆ u ⋆ v × u ∈ P x × v ∈ Q x))
  ; defined = rec! (λ u hu v hv α _ _ → subst ⌞_⌟ (sym α) (`pair↓₂ hu hv))
  }

π₁⊢ : [ id ] (P ∧T Q) ⊢ P
π₁⊢ {P = P} {Q = Q} = record { realiser = `fst ; tracks = tr } where
  tr : ∀ {x} (a : ↯ 𝔸) (ah : a ∈ (P ∧T Q) x) → `fst ⋆ a ∈ P x
  tr {x} = elim! λ a p hp q hq α pp qq → subst-∈ (P _) pp $
    `fst ⋆ a               ≡⟨ ap (`fst ⋆_) α ⟩
    `fst ⋆ (`pair ⋆ p ⋆ q) ≡⟨ `fst-β hp hq ⟩
    p                      ∎

π₂⊢ : [ id ] (P ∧T Q) ⊢ Q
π₂⊢ {P = P} {Q = Q} = record { realiser = `snd ; tracks = tr } where
  tr : ∀ {x} (a : ↯ 𝔸) (ah : a ∈ (P ∧T Q) x) → `snd ⋆ a ∈ Q x
  tr {x} = elim! λ a p hp q hq α pp qq → subst-∈ (Q _) qq $
    `snd ⋆ a               ≡⟨ ap (`snd ⋆_) α ⟩
    `snd ⋆ (`pair ⋆ p ⋆ q) ≡⟨ `snd-β hp hq ⟩
    q                      ∎
```
