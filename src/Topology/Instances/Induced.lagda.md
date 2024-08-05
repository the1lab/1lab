---
description: |
  Induced topologies
---
<!--
```agda
open import Cat.Displayed.Cartesian
open import Cat.Prelude

open import Data.Power

open import Topology.Base
```
-->
```agda
module Topology.Instances.Induced where
```

# Induced topologies

<!--
```agda
private variable
  ℓ ℓ' : Level

open Topology-on
open is-continuous
```
-->

```agda
Induced
  : ∀ {X : Type ℓ} {Y : Type ℓ'}
  → (f : X → Y)
  → Topology-on Y
  → Topology-on X
Induced {X = X} {Y = Y} f Y-top = X-top where
  module Y = Topology-on Y-top

  X-top : Topology-on X
  X-top .Opens = Direct-image (Preimage f) Y.Opens
  X-top .∩-open =
    rec! λ U U-open U∈f⁻¹ V V-open V∈f⁻¹ →
      pure $
        U ∩ V ,
        Y.∩-open U-open V-open ,
        ap₂ _∩_ U∈f⁻¹ V∈f⁻¹
  X-top .⋃ˢ-open S S⊆Opens =
    pure $
      ⋃ˢ S* ,
      Y.⋃ˢ-open S* (λ V V-open → V-open .fst) ,
      ℙ-ext S*-⊆ S*-⊇
    where
      S* : ℙ (ℙ Y)
      S* = Y.Opens ∩ Preimage (Preimage f) S

      S*-⊆ : Preimage f (⋃ˢ S*) ⊆ ⋃ˢ S
      S*-⊆ =
        ⋃-⊆ (λ U → Preimage f (U .fst)) (⋃ˢ S) λ (V , V∈S*) →
        ⋃ˢ-inc S (Preimage f V) (V∈S* .snd)

      S*-⊇ : ⋃ˢ S ⊆ Preimage f (⋃ˢ S*)
      S*-⊇ =
        ⋃ˢ-⊆ S (Preimage f (⋃ˢ S*)) λ U U∈S →
        rec! (λ V V-open f[V]=U x x∈U →
          pure $
            (V , (V-open , subst (λ A → ∣ S A ∣) (sym f[V]=U) U∈S)) ,
            subst (λ A → ∣ A x ∣) (sym f[V]=U) x∈U)
          (S⊆Opens U U∈S)
  X-top .maximal-open =
    pure (maximal , Y.maximal-open , refl)
```

```agda
induced-continuous
  : ∀ {X : Type ℓ} {Y : Type ℓ'} {f : X → Y}
  → {Y-top : Topology-on Y}
  → is-continuous f (Induced f Y-top) Y-top
induced-continuous .reflect-open {U = U} U-open =
  pure (U , U-open , refl)
```

```agda
Topologies-fibration : ∀ {ℓ} → Cartesian-fibration (Topologies-on ℓ)
Topologies-fibration {ℓ} .Cartesian-fibration.has-lift f Y-top = cart where
  open Cartesian-lift
  open is-cartesian

  cart : Cartesian-lift (Topologies-on ℓ) f Y-top
  cart .x' = Induced f Y-top
  cart .lifting = induced-continuous
  cart .cartesian .universal {u = Z} {u' = Z-top} g fg-cont .reflect-open {U = U} =
    rec! λ V V-open f[V]=U →
      subst (is-open Z-top)
        (funext λ z → f[V]=U $ₚ g z)
        (fg-cont .reflect-open V-open)
  cart .cartesian .commutes _ _ = prop!
  cart .cartesian .unique _ _ = prop!
```
