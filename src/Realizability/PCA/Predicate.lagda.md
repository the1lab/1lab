---
description: |
  Predicates valued in PCAs.
---
<!--
```agda
open import 1Lab.Prelude
open import Data.Fin
open import Data.Vec.Base
open import Data.Sum.Base

open import Realizability.PAS
open import Realizability.PCA
```
-->
```agda
module Realizability.PCA.Predicate {ℓ : Level} {A : Type ℓ} (pca : PCA-on A) where
```

<!--
```agda
open PCA pca

private variable
  ℓ' : Level
  X : Type ℓ'
  P Q R : X → Val → Ω
```
-->


```agda
record Realizer {X : Type ℓ'} (P Q : X → Val → Ω) : Type (ℓ ⊔ ℓ') where
  no-eta-equality
  field
    code : A
    code-def : ∣ code ↓ ∣
    track-def : ∀ (x : X) (a : Val) → ∣ P x a ∣ → ∣ (code ⋆ a .elt) ↓ ∣
    tracks : ∀ (x : X) (a : Val) → (a∈px : ∣ P x a ∣) → ∣ Q x (value (code ⋆ a .elt) (track-def x a a∈px)) ∣

  code-val : Val
  code-val = value code code-def

  track-val : (x : X) (a : Val) → ∣ P x a ∣ → Val
  track-val x a a∈px = value (code ⋆ a .elt) (track-def x a a∈px)

open Realizer
```

```agda
_≤ₐ_ : (X → Val → Ω) → (X → Val → Ω) → Type _
P ≤ₐ Q = ∥ Realizer P Q ∥

realize
  : (f : A)
  → (f↓ : ∣ f ↓ ∣)
  → (∀ (x : X) (a : Val) → ∣ P x a ∣ → ∃[ v ∈ Val ] (f ⋆ a .elt ≡ v .elt) × ∣ Q x v ∣)
  → P ≤ₐ Q
realize {P = P} {Q = Q} f f↓ f-rz = inc rz where
  rz : Realizer P Q
  rz .code = f
  rz .code-def = f↓
  rz .track-def x a a∈px =
    rec! (λ v p v∈qx → subst (λ e → ∣ e ↓ ∣) (sym p) (v .def)) (f-rz x a a∈px)
  rz .tracks x a a∈px =
    rec! (λ v p v∈qx → subst (λ v → ∣ Q x v ∣) (ext (sym p)) v∈qx) (f-rz x a a∈px)


id-realize
  : (∀ (x : X) (a : Val) → ∣ P x a ∣ → ∣ Q x a ∣)
  → P ≤ₐ Q
id-realize h = realize “id” id-def λ x a a∈px → inc (a , id-eval (a .elt) , h x a a∈px)
```

```agda
≤ₐ-refl : P ≤ₐ P
≤ₐ-refl = id-realize (λ x a a∈px → a∈px)


≤ₐ-trans : P ≤ₐ Q → Q ≤ₐ R → P ≤ₐ R
≤ₐ-trans p≤q q≤r = do
  f ← p≤q
  g ← q≤r
  realize (“comp” ⋆ g .code ⋆ f .code)
    (comp-def₂ (g .code-def) (f .code-def))
    (λ x a a∈px →
      let fa∈qx = f .tracks x a a∈px in
      let gfa∈rx = g .tracks x _ fa∈qx in
      inc (_ , comp-eval (g .code) (f .code) (a .elt) , gfa∈rx))
```

## Predicates form a pre-lattice

```agda
topₐ : X → Val → Ω
topₐ _ _ = ⊤Ω

botₐ : X → Val → Ω
botₐ _ _ = ⊥Ω

topₐ-≤ : P ≤ₐ topₐ
topₐ-≤ = id-realize λ x a a∈px → tt

botₐ-≤ : botₐ ≤ₐ P
botₐ-≤ = id-realize λ x a ff → absurd ff
```

```agda
_∧ₐ_ : (X → Val → Ω) → (X → Val → Ω) → (X → Val → Ω)
(P ∧ₐ Q) x a = elΩ (Σ[ l ∈ Val ] Σ[ r ∈ Val ] ((a .elt ≡ “pair” ⋆ l .elt ⋆ r .elt) × ∣ P x l ∣ × ∣ Q x r ∣))

∧ₐ-≤l : (P ∧ₐ Q) ≤ₐ P
∧ₐ-≤l = realize “fst” fst-def λ x a → rec! λ l r p l∈px r∈qx →
    inc (l , ap (“fst” ⋆_) p ∙ fst-pair-eval _ _ (r .def) , l∈px)

∧ₐ-≤r : (P ∧ₐ Q) ≤ₐ Q
∧ₐ-≤r = realize “snd” snd-def λ x a → rec! λ l r p l∈px r∈qx →
    inc (r , ap (“snd” ⋆_) p ∙ snd-pair-eval _ _ (l .def) , r∈qx)

∧ₐ-greatest : P ≤ₐ Q → P ≤ₐ R → P ≤ₐ (Q ∧ₐ R)
∧ₐ-greatest p≤q p≤r = do
  f ← p≤q
  g ← p≤r
  realize
    (term (⟨ x ⟩
      “pair” “⋆” (code-val f “⋆” x) “⋆” (code-val g “⋆” x)))
    abs-def
    λ x a a∈px →
      inc (pair-val (track-val f x a a∈px) (track-val g x a a∈px) ,
        abs-eval (a .def) ,
        inc (_ , _ , refl , f .tracks _ _ a∈px , g .tracks _ _ a∈px))
```

```agda
_∨ₐ_ : (X → Val → Ω) → (X → Val → Ω) → (X → Val → Ω)
(P ∨ₐ Q) x a = elΩ $
    (Σ[ l ∈ Val ] (a .elt ≡ “inl” ⋆ l .elt) × ∣ P x l ∣) ⊎
    (Σ[ r ∈ Val ] (a .elt ≡ “inr” ⋆ r .elt) × ∣ Q x r ∣)

∨ₐ-≤l : P ≤ₐ (P ∨ₐ Q)
∨ₐ-≤l = realize “inl” inl-def λ x a a∈px →
  inc (value (“inl” ⋆ a .elt) (inl-def₁ (a .def)) ,
    refl ,
    inc (inl (a , refl , a∈px)))

∨ₐ-least : P ≤ₐ R → Q ≤ₐ R → (P ∨ₐ Q) ≤ₐ R
∨ₐ-least p≤r q≤r = do
  f ← p≤r
  g ← q≤r
  realize (“elim” ⋆ f .code ⋆ g .code) (elim-def₂ (f .code-def) (g .code-def))
    λ x a → rec! [
      (λ (v , p , v∈px) →
        inc (track-val f x v v∈px ,
          ap₂ _⋆_ refl p ∙ elim-inl-eval _ _ _ (g .code-def) ,
          f .tracks x v v∈px)) ,
      (λ (v , p , v∈qx) →
        inc (track-val g x v v∈qx ,
          ap₂ _⋆_ refl p ∙ elim-inr-eval _ _ _ (f .code-def) ,
          g .tracks x v v∈qx))
    ]
```
