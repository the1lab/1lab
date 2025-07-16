<!--
```agda
open import Cat.Instances.Assemblies
open import Cat.Diagram.Coproduct
open import Cat.Prelude

open import Data.Partial.Total
open import Data.Partial.Base
open import Data.Vec.Base using ([] ; _∷_)
open import Data.Sum hiding ([_,_])

open import Realisability.PCA

import Realisability.PCA.Sugar
import Realisability.Data.Sum
import Realisability.Base
```
-->

```agda
module Cat.Instances.Assemblies.Colimits {ℓA} (𝔸 : PCA ℓA) where
```

<!--
```agda
open Realisability.PCA.Sugar 𝔸
open Realisability.Data.Sum 𝔸
open Realisability.Base 𝔸

open is-coproduct
open Coproduct

private variable
  ℓ ℓ' : Level
  X Y Z : Assembly 𝔸 ℓ
```
-->

```agda
_⊎Asm_ : Assembly 𝔸 ℓ → Assembly 𝔸 ℓ' → Assembly 𝔸 (ℓ ⊔ ℓ')
(X ⊎Asm Y) .Ob         = ⌞ X ⌟ ⊎ ⌞ Y ⌟
(X ⊎Asm Y) .has-is-set = hlevel 2

(X ⊎Asm Y) .realisers (inl x) = record
  { mem     = λ e → elΩ (Σ[ a ∈ ↯ ⌞ 𝔸 ⌟ ] (e ≡ `inl ⋆ a × [ X ] a ⊩ x))
  ; defined = rec! λ _ a p → subst ⌞_⌟ (sym a) (`inl↓₁(X .defined p))
  }

(X ⊎Asm Y) .realisers (inr x) = record
  { mem     = λ e → elΩ (Σ[ a ∈ ↯ ⌞ 𝔸 ⌟ ] (e ≡ `inr ⋆ a × [ Y ] a ⊩ x))
  ; defined = rec! λ _ a p → subst ⌞_⌟ (sym a) (`inr↓₁ (Y .defined p))
  }

(X ⊎Asm Y) .realised (inl x) = do
  (p , rx) ← X .realised x
  inc (`inl ⋆ p , inc (p , refl , rx))

(X ⊎Asm Y) .realised (inr x) = do
  (p , rx) ← Y .realised x
  inc (`inr ⋆ p , inc (p , refl , rx))
```

```agda
asm-inl : Assembly-hom X (X ⊎Asm Y)
asm-inl = to-assembly-hom record where
  map       = inl
  realiser  = `inl
  tracks ha = inc (_ , refl , ha)

asm-inr : Assembly-hom Y (X ⊎Asm Y)
asm-inr = to-assembly-hom record where
  map       = inr
  realiser  = `inr
  tracks ha = inc (_ , refl , ha)
```

```agda
Assembly-coproducts : has-coproducts (Assemblies 𝔸 ℓ)
Assembly-coproducts A B .coapex = A ⊎Asm B
Assembly-coproducts A B .ι₁ = asm-inl
Assembly-coproducts A B .ι₂ = asm-inr
Assembly-coproducts A B .has-is-coproduct .[_,_] {Q = Q} f g = record where
  map = λ where
    (inl a) → f · a
    (inr b) → g · b

  tracked = do
    ft ← f .tracked
    gt ← g .tracked
    let
      f↓ = ft .realiser .snd
      g↓ = gt .realiser .snd
    inc record where
      realiser = `match ⋆ ft ⋆ gt , `match↓₂ f↓ g↓

      tracks = λ where
        {inl x} ha → □-out (Q .realisers _ .mem _ .is-tr) do
          (e , α , e⊩x) ← ha
          pure $ subst⊩ Q (ft .tracks e⊩x) $
            ap₂ _%_ refl α ∙ `match-βl (A .defined e⊩x) f↓ g↓

        {inr x} ha → □-out (Q .realisers _ .mem _ .is-tr) do
          (e , α , e⊩x) ← ha
          pure $ subst⊩ Q (gt .tracks e⊩x) $
            ap₂ _%_ refl α ∙ `match-βr (B .defined e⊩x) f↓ g↓

Assembly-coproducts A B .has-is-coproduct .[]∘ι₁ = trivial!
Assembly-coproducts A B .has-is-coproduct .[]∘ι₂ = trivial!
Assembly-coproducts A B .has-is-coproduct .unique p q = ext λ where
  (inl x) → ap map p · x
  (inr x) → ap map q · x
```
