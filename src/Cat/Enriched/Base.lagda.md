<!--
```agda
open import Cat.Monoidal.Base
open import Cat.Instances.Functor
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Enriched.Base where
```

# Enriched Categories

```agda
record Enriched-precategory
  {o ℓ} {V : Precategory o ℓ}
  (V-monoidal : Monoidal-category V)
  (o' : Level) : Type (o ⊔ ℓ ⊔ lsuc o') where
  private
    module V = Cat.Reasoning V
    open Monoidal-category V-monoidal
  field
    Obv : Type o'
    Homv : Obv → Obv → V.Ob
    idv : ∀ {Γ x} → V.Hom Γ (Homv x x ⊗ Γ)
    _∘v_ : ∀ {Γ Δ Ψ x y z}
         → V.Hom Δ (Homv y z ⊗ Ψ) → V.Hom Γ (Homv x y ⊗ Δ) → V.Hom Γ (Homv x z ⊗ Ψ)

  infixr 40 _∘v_

  field
    idlv : ∀ {Γ Δ x y} → (f : V.Hom Γ (Homv x y ⊗ Δ)) → idv ∘v f ≡ f
    idrv : ∀ {Γ Δ x y} → (f : V.Hom Γ (Homv x y ⊗ Δ)) → f ∘v idv ≡ f
    assocv : ∀ {Γ Δ Ψ Θ w x y z}
           → (f : V.Hom Ψ (Homv y z ⊗ Θ)) → (g : V.Hom Δ (Homv x y ⊗ Ψ)) → (h : V.Hom Γ (Homv w x ⊗ Δ))
           → f ∘v (g ∘v h) ≡ (f ∘v g) ∘v h
    idv-natural : ∀ {Γ Δ x} → (σ : V.Hom Γ Δ) → idv V.∘ σ ≡ (Homv x x ▶ σ) V.∘ idv
    ∘v-naturall : ∀ {Γ Δ Ψ Θ x y z}
                → (σ : V.Hom Ψ Θ)
                → (f : V.Hom Δ (Homv y z ⊗ Ψ)) → (g : V.Hom Γ (Homv x y ⊗ Δ))
                → (Homv x z ▶ σ) V.∘ (f ∘v g) ≡ ((Homv y z ▶ σ) V.∘ f) ∘v g
    ∘v-natural-inner : ∀ {Γ Δ Ψ Θ x y z}
                → (f : V.Hom Ψ (Homv y z ⊗ Θ))
                → (σ : V.Hom Δ Ψ)
                → (g : V.Hom Γ (Homv x y ⊗ Δ))
                → f ∘v ((Homv x y ▶ σ) V.∘ g) ≡ (f V.∘ σ) ∘v g
    ∘v-naturalr : ∀ {Γ Δ Ψ Θ x y z}
                → (f : V.Hom Ψ (Homv y z ⊗ Θ)) → (g : V.Hom Δ (Homv x y ⊗ Ψ))
                → (σ : V.Hom Γ Δ)
                → (f ∘v g) V.∘ σ ≡ (f ∘v (g V.∘ σ))
```

```agda
record make-enriched-precategory
  {o ℓ} {V : Precategory o ℓ}
  (V-monoidal : Monoidal-category V)
  (o' : Level) : Type (o ⊔ ℓ ⊔ lsuc o') where
  private
    module V = Cat.Reasoning V
    open Monoidal-category V-monoidal
  field
    Obv : Type o'
    Homv : Obv → Obv → V.Ob
    idv : ∀ {x} → V.Hom Unit (Homv x x)
    -- Minor annoyance, but is this a bigger problem???
    ∘v : ∀ {x y z} → V.Hom (Homv x y ⊗ Homv y z) (Homv x z)
    idlv : ∀ {x y} → ∘v V.∘ (idv {x} ◀ Homv x y) ≡ λ←
    idrv : ∀ {x y} → ∘v V.∘ (Homv x y ▶ idv {y}) ≡ ρ←
    assocv : ∀ {w x y z}
           → ∘v V.∘ (∘v ⊗₁ V.id)
           ≡ ∘v V.∘ (V.id ⊗₁ ∘v) V.∘ α→ (Homv w x) (Homv x y) (Homv y z)

module _
  {ov ℓv}
  {V : Precategory ov ℓv} {V-monoidal : Monoidal-category V}
  where
  private
    module V = Cat.Reasoning V
    module [V,V] = Cat.Reasoning (Cat[ V , V ])
    open Monoidal-category V-monoidal

  -- Pain and suffering.
  to-enriched-precategory
    : ∀ {o} → make-enriched-precategory V-monoidal o
    → Enriched-precategory V-monoidal o
  to-enriched-precategory mk = ecat where
    open make-enriched-precategory mk

    ecat : Enriched-precategory V-monoidal _
    ecat .Enriched-precategory.Obv = Obv
    ecat .Enriched-precategory.Homv = Homv
    ecat .Enriched-precategory.idv = (idv ◀ _) V.∘ λ→
    ecat .Enriched-precategory._∘v_ f g =
      {!!}
      -- (∘v ◀ _) V.∘ α← _ _ _ V.∘ (_ ▶ f) V.∘ g
    ecat .Enriched-precategory.idlv f = {!!}
      -- ((∘v ◀ _) V.∘ α← _ _ _ V.∘ (_ ▶ (idv ◀ _) V.∘ λ→) V.∘ f) ≡⟨ {!λ→-natural ?!} ⟩
      -- (((∘v V.∘ (idv ◀ _)) ◀ _) V.∘ α← _ _ _ V.∘ λ→ V.∘ f) ≡⟨ {!λ→-natural ?!} ⟩
      -- ((λ← ◀ _) V.∘ α← _ _ _ V.∘ λ→ V.∘ f) ≡⟨ {!f!} ⟩
      -- ((λ← ◀ _) V.∘ α← _ _ _ V.∘ λ→ V.∘ f) ≡⟨ {!λ→-natural ?!} ⟩
      -- f ∎
    ecat .Enriched-precategory.idrv f = {!!}
    ecat .Enriched-precategory.assocv = {!!}
    ecat .Enriched-precategory.idv-natural = {!!}
    ecat .Enriched-precategory.∘v-naturall = {!!}
    ecat .Enriched-precategory.∘v-natural-inner = {!!}
    ecat .Enriched-precategory.∘v-naturalr = {!!}
```


```agda
record Enriched-functor
  {o ℓ o' o''} {V : Precategory o ℓ} {V-monoidal : Monoidal-category V}
  (C : Enriched-precategory V-monoidal o') (D : Enriched-precategory V-monoidal o'')
  : Type (o ⊔ ℓ ⊔ o' ⊔ o'')
  where
  private
    module V = Precategory V
    open Monoidal-category V-monoidal
    module C = Enriched-precategory C
    module D = Enriched-precategory D
  field
    Fv₀ : C.Obv → D.Obv
    Fv₁ : ∀ {Γ Δ x y} → V.Hom Γ (C.Homv x y ⊗ Δ) → V.Hom Γ (D.Homv (Fv₀ x) (Fv₀ y) ⊗ Δ)
    Fv-id : ∀ {Γ x} → Fv₁ (C.idv {Γ} {x}) ≡ D.idv
    Fv-∘ : ∀ {Γ Δ Ψ x y z}
         → (f : V.Hom Δ (C.Homv y z ⊗ Ψ)) → (g : V.Hom Γ (C.Homv x y ⊗ Δ))
         → Fv₁ (f C.∘v g) ≡ Fv₁ f D.∘v Fv₁ g
    Fv-naturall :  ∀ {Γ Δ Ψ x y}
                → (σ : V.Hom Δ Ψ)
                → (f : V.Hom Γ (C.Homv x y ⊗ Δ))
                → (D.Homv (Fv₀ x) (Fv₀ y) ▶ σ) V.∘ Fv₁ f ≡ Fv₁ ((C.Homv x y ▶ σ) V.∘ f)
    Fv-naturalr :  ∀ {Γ Δ Ψ x y}
                → (f : V.Hom Δ (C.Homv x y ⊗ Ψ))
                → (σ : V.Hom Γ Δ)
                → (Fv₁ f V.∘ σ) ≡ Fv₁ (f V.∘ σ)

open Enriched-functor
```

```agda
module _
  {ov ℓv}
  {V : Precategory ov ℓv} {V-monoidal : Monoidal-category V}
  where
  private
    module V = Precategory V
    open Monoidal-category V-monoidal

  Idv
    : ∀ {o} {C : Enriched-precategory V-monoidal o}
    → Enriched-functor C C
  Idv {C = C} = func module Idv where

    func : Enriched-functor _ _
    func .Fv₀ x = x
    func .Fv₁ f = f
    func .Fv-id = refl
    func .Fv-∘ f g = refl
    func .Fv-naturall f σ = refl
    func .Fv-naturalr f σ = refl

  _Fv∘_
    : ∀ {oc od oe}
    → {C : Enriched-precategory V-monoidal oc}
    → {D : Enriched-precategory V-monoidal od}
    → {E : Enriched-precategory V-monoidal oe}
    → Enriched-functor D E → Enriched-functor C D → Enriched-functor C E
  _Fv∘_ {C = C} {D = D} {E = E} F G = func module ∘Fv where

    func : Enriched-functor _ _
    func .Fv₀ x = F .Fv₀ (G .Fv₀ x)
    func .Fv₁ f = F .Fv₁ (G .Fv₁ f)
    func .Fv-id =
      ap (F .Fv₁) (G .Fv-id) ∙ F .Fv-id
    func .Fv-∘ f g =
      ap (F .Fv₁) (G .Fv-∘ f g) ∙ F .Fv-∘ (G .Fv₁ f) (G .Fv₁ g)
    func .Fv-naturall f σ =
      F .Fv-naturall f (G .Fv₁ σ)
      ∙ ap (F .Fv₁) (G .Fv-naturall f σ)
    func .Fv-naturalr f σ =
      F .Fv-naturalr (G .Fv₁ f) σ
      ∙ ap (F .Fv₁) (G .Fv-naturalr f σ)

  infixr 30 _Fv∘_
```


```agda
record _=>v_ 
  {o ℓ o' o''} {V : Precategory o ℓ} {V-monoidal : Monoidal-category V}
  {C : Enriched-precategory V-monoidal o'} {D : Enriched-precategory V-monoidal o''}
  (F G : Enriched-functor C D)
  : Type (o ⊔ ℓ ⊔ o' ⊔ o'') where
  private
    module V = Precategory V
    open Monoidal-category V-monoidal
    module C = Enriched-precategory C
    module D = Enriched-precategory D
  field
    ηv : ∀ Γ x → V.Hom Γ (D.Homv (F .Fv₀ x) (G .Fv₀ x) ⊗ Γ)
    is-naturalv : ∀ {Γ Δ x y} → (f : V.Hom Γ (C.Homv x y ⊗ Δ))
                → ηv _ y D.∘v F .Fv₁ f ≡ G .Fv₁ f D.∘v ηv _ x
    ηv-natural : ∀ {Γ Δ x}
               → (σ : V.Hom Γ Δ)
               → ηv _ x V.∘ σ ≡ (D.Homv (F .Fv₀ x) (G .Fv₀ x) ▶ σ) V.∘ ηv _ x

infix 20 _=>v_
open _=>v_
```

```agda
module _
  {ov ℓv oc od}
  {V : Precategory ov ℓv} {V-monoidal : Monoidal-category V}
  {C : Enriched-precategory V-monoidal oc}
  {D : Enriched-precategory V-monoidal od}
  {F G : Enriched-functor C D}
  where
  private
    module V = Precategory V
    open Monoidal-category V-monoidal
    module C = Enriched-precategory C
    module D = Enriched-precategory D

  Enriched-nat-path
    : {α β : F =>v G}
    → (∀ Γ x → α .ηv Γ x ≡ β .ηv Γ x)
    → α ≡ β
  Enriched-nat-path p i .ηv Γ x = p Γ x i
  Enriched-nat-path {α = α} {β = β} p i .is-naturalv f =
    is-prop→pathp
      (λ i → V.Hom-set _ _ (p _ _ i D.∘v F .Fv₁ f) (G .Fv₁ f D.∘v p _ _ i))
      (α .is-naturalv f)
      (β .is-naturalv f) i
  Enriched-nat-path {α = α} {β = β} p i .ηv-natural σ =
    is-prop→pathp
      (λ i → V.Hom-set _ _ ((p _ _ i) V.∘ σ) ((_ ▶ σ) V.∘ (p _ _ i)))
      (α .ηv-natural σ) (β .ηv-natural σ) i
  
  private unquoteDecl eqv = declare-record-iso eqv (quote _=>v_)
  
  Enriched-nat-is-set : is-set (F =>v G)
  Enriched-nat-is-set = Iso→is-hlevel 2 eqv (hlevel 2)
```
