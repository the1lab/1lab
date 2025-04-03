<!--
```agda
open import 1Lab.Prelude

open import Data.Partial.Total
open import Data.Partial.Base
open import Data.Vec.Base

open import Realisability.PCA

import Realisability.Data.Pair
import Realisability.PCA.Sugar
import Realisability.Data.Sum
```
-->

```agda
module Realisability.Base {ℓA} (pca@(𝔸 , _) : PCA ℓA) where
```

<!--
```agda
open Realisability.PCA.Sugar pca
open Realisability.Data.Pair pca
open Realisability.Data.Sum pca

private variable
  ℓ ℓ' ℓ'' : Level
  X Y Z : Type ℓ'
  n : Nat
```
-->

# Realisability logic

```agda
record [_]_⊢_ (f : X → Y) (P : X → ℙ⁺ 𝔸) (Q : Y → ℙ⁺ 𝔸) : Type (level-of X ⊔ level-of Y ⊔ ℓA) where
  field
    realiser : ↯⁺ 𝔸
    tracks   : ∀ x (a : ↯ ⌞ 𝔸 ⌟) (ah : a ∈ P x) → realiser ⋆ a ∈ Q (f x)

  realiser↓ : ∀ {x} (a : ↯ ⌞ 𝔸 ⌟) (ah : a ∈ P x) → ⌞ realiser ⋆ a ⌟
  realiser↓ a ah = Q _ .defined (tracks _ a ah)
```

<!--
```agda
private unquoteDecl eqv' = declare-record-iso eqv' (quote [_]_⊢_)

open [_]_⊢_ hiding (tracks) public

-- Evil hack to change the visibility of the arguments to tracks in
-- RHSes: instead of using the projection from that record we define a
-- new record with the first two arguments made implicit (with the same
-- name), convert the actual record to this new one, and export a copy
-- of the new projection; since this is all done in a module
-- parametrised by a [ f ] P ⊢ Q, the new definition is basically a
-- projection.
--
-- Since copies of postfix identifiers can be used postfix this works.

module _ {f : X → Y} {P : X → ℙ⁺ 𝔸} {Q : Y → ℙ⁺ 𝔸} (i : [ f ] P ⊢ Q) where
  private
    module i = [_]_⊢_ i
    record hack : Type (level-of X ⊔ level-of Y ⊔ ℓA) where
      field
        tracks   : ∀ {x} {a : ↯ ⌞ 𝔸 ⌟} (ah : a ∈ P x) → i.realiser ⋆ a ∈ Q (f x)

    from : hack
    from = record { tracks = i.tracks _ _ }

  open hack from public

instance
  tracks-to-term : ∀ {V : Type} {P : X → ℙ⁺ 𝔸} {Q : Y → ℙ⁺ 𝔸} {f : X → Y} → To-term V ([ f ] P ⊢ Q)
  tracks-to-term = record { to = λ x → const (x .realiser) }

  tracks-to-part : ∀ {P : X → ℙ⁺ 𝔸} {Q : Y → ℙ⁺ 𝔸} {f : X → Y} → To-part ([ f ] P ⊢ Q) ⌞ 𝔸 ⌟
  tracks-to-part = record { to-part = λ x → x .realiser .fst }

private
  variable P Q R : X → ℙ⁺ 𝔸

  subst-∈ : (P : ℙ⁺ 𝔸) {x y : ↯ ⌞ 𝔸 ⌟} → x ∈ P → y ≡ x → y ∈ P
  subst-∈ P hx p = subst (_∈ P) (sym p) hx
```
-->

## Basic structural rules

```agda
id⊢ : [ id ] P ⊢ P
id⊢ {P = P} = record where
  realiser = val ⟨ x ⟩ x

  tracks x a ha = subst-∈ (P x) ha (abs-β _ [] (a , P x .defined ha))

_∘⊢_ : ∀ {f g} → [ g ] Q ⊢ R → [ f ] P ⊢ Q → [ g ∘ f ] P ⊢ R
_∘⊢_ {R = R} {P = P} α β = record where
  realiser = val ⟨ x ⟩ α `· (β `· x)

  tracks x a ha = subst-∈ (R _) (α .tracks (β .tracks ha)) $
    (val ⟨ x ⟩ α `· (β `· x)) ⋆ a ≡⟨ abs-β _ [] (a , P _ .defined ha) ⟩
    α ⋆ (β ⋆ a)                   ∎
```

## Conjunction

```agda
_∧T_ : (P Q : X → ℙ⁺ 𝔸) → X → ℙ⁺ 𝔸
(P ∧T Q) x .mem a = elΩ do
  Σ[ u ∈ ↯ ⌞ 𝔸 ⌟ ] Σ[ v ∈ ↯ ⌞ 𝔸 ⌟ ]
    a ≡ `pair ⋆ u ⋆ v × u ∈ P x × v ∈ Q x
(P ∧T Q) x .defined = rec! λ u v α rx ry →
  subst ⌞_⌟ (sym α) (`pair↓₂ (P _ .defined rx) (Q _ .defined ry))

π₁⊢ : [ id ] (P ∧T Q) ⊢ P
π₁⊢ {P = P} {Q = Q} = record where
  realiser = `fst

  tracks x = elim! λ a p q α pp qq → subst-∈ (P _) pp $
    `fst ⋆ a               ≡⟨ ap (`fst ⋆_) α ⟩
    `fst ⋆ (`pair ⋆ p ⋆ q) ≡⟨ `fst-β (P _ .defined pp) (Q _ .defined qq) ⟩
    p                      ∎

π₂⊢ : [ id ] (P ∧T Q) ⊢ Q
π₂⊢ {P = P} {Q = Q} = record where
  realiser = `snd

  tracks x = elim! λ a p q α pp qq → subst-∈ (Q _) qq $
    `snd ⋆ a               ≡⟨ ap (`snd ⋆_) α ⟩
    `snd ⋆ (`pair ⋆ p ⋆ q) ≡⟨ `snd-β (P _ .defined pp) (Q _ .defined qq) ⟩
    q                      ∎
```
