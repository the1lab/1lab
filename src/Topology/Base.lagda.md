---
description: |
  The basic theory of topological spaces.
---
<!--
```agda
open import Cat.Prelude

open import Data.Power

open import 1Lab.Reflection hiding (absurd)
```
-->
```agda
module Topology.Base where
```

```agda
record is-topology {o ℓ} (X : Type o) (is-open : (X → Ω) → Type ℓ) : Type (lsuc o ⊔ ℓ) where
  field
    ∩-open : ∀ {U V : X → Ω} → is-open U → is-open V → is-open (U ∩ V)
    ⋃-open : {I : Type o} → (Uᵢ : I → X → Ω) → (∀ i → is-open (Uᵢ i)) → is-open (⋃ Uᵢ)
    maximal-open : is-open maximal
    has-is-set : is-set X
    is-open-is-prop : ∀ {U} → is-prop (is-open U)

  minimal-open : is-open minimal
  minimal-open =
    subst is-open
      (ext (λ _ → Ω-ua (rec! (λ ff tt → ff)) λ ff → inc (lift ff , tt)))
      (⋃-open {I = Lift _ ⊥} (λ _ _ → ⊤Ω) (λ ff → absurd (Lift.lower ff)))

record Topological-space (o ℓ : Level) : Type (lsuc o ⊔ lsuc ℓ) where
  field
    Ob : Type o
    is-open : (Ob → Ω) → Type ℓ
    has-is-topology : is-topology Ob is-open

  open is-topology has-is-topology public
```

<!--
```agda
private variable
  o ℓ o' ℓ' : Level
  X Y Z : Topological-space o ℓ

instance
  Underlying-Topological-space : ∀ {o ℓ} → Underlying (Topological-space o ℓ)
  Underlying-Topological-space .Underlying.ℓ-underlying = _
  Underlying-Topological-space .Underlying.⌞_⌟ = Topological-space.Ob

  open hlevel-projection

  Topological-space-ob-hlevel-proj : hlevel-projection (quote Topological-space.Ob)
  Topological-space-ob-hlevel-proj .has-level   = quote Topological-space.has-is-set
  Topological-space-ob-hlevel-proj .get-level _ = pure (lit (nat 2))
  Topological-space-ob-hlevel-proj .get-argument (_ ∷ _ ∷ arg _ t ∷ _) = pure t
  Topological-space-ob-hlevel-proj .get-argument _                     = typeError []

  Topological-space-open-hlevel-proj : hlevel-projection (quote Topological-space.is-open)
  Topological-space-open-hlevel-proj .has-level   = quote Topological-space.is-open-is-prop
  Topological-space-open-hlevel-proj .get-level _ = pure (lit (nat 1))
  Topological-space-open-hlevel-proj .get-argument (_ ∷ _ ∷ arg _ t ∷ _) = pure t
  Topological-space-open-hlevel-proj .get-argument _                     = typeError []

```
-->

```agda
record Continuous
  {o ℓ o' ℓ'}
  (X : Topological-space o ℓ) (Y : Topological-space o' ℓ')
  : Type (o ⊔ o' ⊔ ℓ ⊔ ℓ') where
  no-eta-equality
  private
    module X = Topological-space X
    module Y = Topological-space Y
  field
    hom : X.Ob → Y.Ob
    reflect-open : ∀ {U} → Y.is-open U → X.is-open (λ x → U (hom x))

open Continuous
```

<!--
```agda
unquoteDecl H-Level-Continuous = declare-record-hlevel 2 H-Level-Continuous (quote Continuous)

instance
  Funlike-Continuous : Funlike (Continuous X Y) ⌞ X ⌟ λ _ → ⌞ Y ⌟
  Funlike-Continuous = record { _#_ = hom }

Continuous-pathp
  : ∀ {o ℓ o' ℓ'} {P : I → Topological-space o ℓ} {Q : I → Topological-space o' ℓ'}
  → {f : Continuous (P i0) (Q i0)} {g : Continuous (P i1) (Q i1)}
  → PathP (λ i → ⌞ P i ⌟ → ⌞ Q i ⌟) (apply f) (apply g)
  → PathP (λ i → Continuous (P i) (Q i)) f g
Continuous-pathp q i .hom a = q i a
Continuous-pathp {P = P} {Q} {f} {g} q i .Continuous.reflect-open {U} U-open =
  is-prop→pathp
    (λ i →
      Π-is-hlevel' {A = ⌞ Q i ⌟ → Ω} {B = λ U → Q.is-open i U → P.is-open i λ x → U (q i x)} 1 λ _ →
      Π-is-hlevel 1 λ _ → P.is-open-is-prop i)
    (λ U-open → f .reflect-open U-open)
    (λ U-open → g .reflect-open U-open)
    i U-open
  where
    module P i = Topological-space (P i)
    module Q i = Topological-space (Q i)

instance
  Extensional-Continuous
    : ∀ {o ℓ o' ℓ' ℓr} {P : Topological-space o ℓ} {Q : Topological-space o' ℓ'}
    → ⦃ sa : Extensional (⌞ P ⌟ → ⌞ Q ⌟) ℓr ⦄
    → Extensional (Continuous P Q) ℓr
  Extensional-Continuous {Q = Q} ⦃ sa ⦄ =
    injection→extensional! Continuous-pathp sa

```
-->

```agda
idᶜ : Continuous X X
idᶜ .hom x = x
idᶜ .reflect-open U-open = U-open

_∘ᶜ_ : Continuous Y Z → Continuous X Y → Continuous X Z
(f ∘ᶜ g) .hom x = f # (g # x)
(f ∘ᶜ g) .reflect-open U-open = g .reflect-open (f .reflect-open U-open)

Top : ∀ (o ℓ : Level) → Precategory (lsuc o ⊔ lsuc ℓ) (o ⊔ ℓ)
Top o ℓ .Precategory.Ob = Topological-space o ℓ
Top o ℓ .Precategory.Hom = Continuous
Top o ℓ .Precategory.Hom-set _ _ = hlevel 2
Top o ℓ .Precategory.id = idᶜ
Top o ℓ .Precategory._∘_ = _∘ᶜ_
Top o ℓ .Precategory.idr _ = trivial!
Top o ℓ .Precategory.idl _ = trivial!
Top o ℓ .Precategory.assoc _ _ _ = trivial!
```
