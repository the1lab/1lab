open import 1Lab.Univalence.SIP.Record.Base
open import 1Lab.Univalence.SIP.Auto
open import 1Lab.Univalence.SIP
open import 1Lab.Reflection
open import 1Lab.Type.Sigma
open import 1Lab.Univalence
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

open import Agda.Builtin.List

open import Data.List

module 1Lab.Univalence.SIP.Record.Prop where
  module _
    {ℓ ℓ₁ ℓ₁' ℓ₂}
    (R : Type ℓ → Type ℓ₁) -- Structure record
    (ι : IsHomT ℓ₁' R) -- Equivalence record
    (fs : RecordFields R ι) -- Prior fields
    (P : (X : Type ℓ) → fields→prod fs X → Type ℓ₂) -- Property type
    (f : {X : Type ℓ} (r : R X) → P X (project-fields fs r)) -- Property projection
    where

    prev = project-fields fs
    Prev = fields→prod fs

    PropHelperCenterType : Type _
    PropHelperCenterType =
      (A B : Σ R) (e : A .fst ≃ B .fst)
      (p : PathP (λ i → Prev (ua e i)) (prev (A .snd)) (prev (B .snd)))
      → PathP (λ i → P (ua e i) (p i)) (f (A .snd)) (f (B .snd))

    PropHelperContractType : PropHelperCenterType → Type _
    PropHelperContractType c =
      (A B : Σ R) (e : A .fst ≃ B .fst)
      {p₀ : PathP (λ i → Prev (ua e i)) (prev (A .snd)) (prev (B .snd))}
      (q : PathP (λ i → R (ua e i)) (A .snd) (B .snd))
      (p : p₀ ≡ (λ i → prev (q i)))
      → PathP (λ k → PathP (λ i → P (ua e i) (p k i)) (f (A .snd)) (f (B .snd)))
        (c A B e p₀)
        (λ i → f (q i))

    PropHelperType : Type _
    PropHelperType =
      Σ[ X ∈ PropHelperCenterType ] (PropHelperContractType X)

    derivePropHelper : isPropProperty R ι fs P → PropHelperType
    derivePropHelper propP .fst A B e p =
      isHLevelPathP' 0 (propP _) (f (A .snd)) (f (B .snd)) .centre
    derivePropHelper propP .snd A B e q p =
      isHLevelPathP' 0 (isHLevelPathP 1 (propP _)) _ _ .centre
