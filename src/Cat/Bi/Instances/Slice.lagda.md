<!--
```agda
open import Cat.Functor.Naturality
open import Cat.Functor.Bifunctor
open import Cat.Functor.Base
open import Cat.Prelude renaming (module Precategory to Pc)
open import Cat.Bi.Base renaming (module Prebicategory to Pb)

import Cat.Functor.Reasoning
import Cat.Bi.Reasoning as Bi

open make-natural-iso
open Make-bifunctor
open _=>_
```
-->

```agda
module Cat.Bi.Instances.Slice
  {o o' ℓ₁ ℓ₁' ℓ₂ ℓ₂'} {B : Prebicategory o ℓ₁ ℓ₂} {C : Prebicategory o' ℓ₁' ℓ₂'}
  (F : Lax-functor B C)
  where
```

<!--
```agda
open Bi C

private
  module B = Bi B
  module F = Lax-functor F
  module Fr {A B} = Cat.Functor.Reasoning (F.P₁ {A} {B})
```
-->

# Lax slices of bicategories

```agda
  Bislice₀ : Ob → Type _
  Bislice₀ X = Σ[ A ∈ B ] (F.₀ A ↦ X)
```

```agda
Bislice₁ : ∀ {X} → Bislice₀ X → Bislice₀ X → Precategory (ℓ₁ ⊔ ℓ₂') (ℓ₂ ⊔ ℓ₂')
Bislice₁ (Y , f) (Z , g) .Pc.Ob      = Σ[ p ∈ Y B.↦ Z ] (f ⇒ g ⊗ F.₁ p)
Bislice₁ (Y , f) (Z , g) .Pc.Hom (p₀ , θ₀) (p₁ , θ₁) = Σ[ α ∈ p₀ B.⇒ p₁ ] (g ▶ F.₂ α ∘ θ₀ ≡ θ₁)
Bislice₁ (Y , f) (Z , g) .Pc.Hom-set _ _ = hlevel 2
Bislice₁ (Y , f) (Z , g) .Pc.id = record
  { fst = B.Hom.id
  ; snd = ▶.eliml F.P₁.F-id
  }
Bislice₁ (Y , f) (Z , g) .Pc._∘_ (α₀ , p) (α₁ , q) = record
  { fst = α₀ B.∘ α₁
  ; snd = ▶.pushl (F.P₁.F-∘ _ _) ∙ Hom.cdr q ∙ p
  }
Bislice₁ (Y , f) (Z , g) .Pc.idr _ = Σ-prop-path! (B.Hom.idr _)
Bislice₁ (Y , f) (Z , g) .Pc.idl _ = Σ-prop-path! (B.Hom.idl _)
Bislice₁ (Y , f) (Z , g) .Pc.assoc _ _ _ = Σ-prop-path! (B.Hom.assoc _ _ _)
```

```agda
bislice-compose : ∀ {X} {A B C : Bislice₀ X} → Bifunctor (Bislice₁ B C) (Bislice₁ A B) (Bislice₁ A C)
bislice-compose {X} {A , f} {B , g} {C , h} = make-bifunctor mk where
  mk : Make-bifunctor {C = Bislice₁ (B , g) (C , h)} {Bislice₁ (A , f) (B , g)} {Bislice₁ (A , f) (C , h)}
  mk .F₀ (p₀ , θ₀) (p₁ , θ₁) = record
    { fst = p₀ B.⊗ p₁
    ; snd = _ ▶ F.γ→ _ ∘ α→ _ ∘ θ₀ ◀ _ ∘ θ₁
    }
  mk .lmap {p₀ , θ₀} {p₁ , θ₁} {p₂ , θ₂} (α₀ , p) = record where
    fst = α₀ B.◀ _
    snd =
      h ▶ F.₂ (α₀ B.◀ p₂) ∘ h ▶ F.γ→ _ ∘ α→ _ ∘ θ₀ ◀ _ ∘ θ₂
        ≡⟨ Hom.extendl (▶.weave (Hom.car (ap F.₂ (B.compose.lmap-◆ _)) ∙∙ sym (F.γ→nat _ _) ∙∙ Hom.cdr (▶.elimr F.P₁.F-id))) ⟩
      h ▶ F.γ→ _ ∘ h ▶ (F.₂ α₀ ◀ _) ∘ α→ _ ∘ θ₀ ◀ _ ∘ θ₂
        ≡⟨ Hom.extend-inner (sym associator-◀-▶) ⟩
      h ▶ F.γ→ _ ∘ α→ _ ∘ (h ▶ _) ◀ _ ∘ θ₀ ◀ _ ∘ θ₂
        ≡⟨ Hom.cddr (Hom.pulll (◀.collapse p)) ⟩
      h ▶ F.γ→ _ ∘ α→ _ ∘ θ₁ ◀ _ ∘ θ₂
        ∎
  mk .rmap {p₀ , θ₀} {p₁ , θ₁} {p₂ , θ₂} (α₀ , p) = record where
    fst = _ B.▶ α₀
    snd =
      h ▶ F.₂ (p₂ B.▶ α₀) ∘ h ▶ F.γ→ _ ∘ α→ _ ∘ θ₂ ◀ F.₁ p₀ ∘ θ₀
        ≡⟨ Hom.extendl (▶.weave (Hom.car (ap F.₂ (B.compose.rmap-◆ _)) ∙∙ sym (F.γ→nat _ _) ∙∙ Hom.cdr (◀.eliml F.P₁.F-id))) ⟩
      h ▶ F.γ→ _ ∘ h ▶ (F.₁ p₂ ▶ F.₂ α₀) ∘ α→ _ ∘ θ₂ ◀ F.₁ p₀ ∘ θ₀
        ≡⟨ Hom.extend-inner (sym (▶-assoc.to .is-natural _ _ _)) ⟩
      h ▶ F.γ→ _ ∘ α→ _ ∘ (h ⊗ F.₁ p₂) ▶ F.₂ α₀ ∘ θ₂ ◀ F.₁ p₀ ∘ θ₀
        ≡⟨ Hom.cddr (Hom.extendl (compose.rlmap _ _)) ⟩
      h ▶ F.γ→ _ ∘ α→ _ ∘ θ₂ ◀ F.₁ p₁ ∘ g ▶ F.₂ α₀ ∘ θ₀
        ≡⟨ Hom.cdddr p ⟩
      h ▶ F.γ→ _ ∘ α→ _ ∘ θ₂ ◀ F.₁ p₁ ∘ θ₁
        ∎
  mk .lmap-id = Σ-prop-path! (B.◀.elim refl)
  mk .rmap-id = Σ-prop-path! (B.▶.elim refl)
  mk .lmap-∘ f g = Σ-prop-path! (B.◀.expand refl)
  mk .rmap-∘ f g = Σ-prop-path! (B.▶.expand refl)
  mk .lrmap f g = Σ-prop-path! (B.compose.lrmap _ _)

private
  bislice-id : ∀ {X A} → ⌞ Bislice₁ {X} A A ⌟
  bislice-id = record
    { fst = B.id
    ; snd = _ ▶ F.υ→ ∘ ρ→ _
    }

Bislice : Ob → Prebicategory {!   !} {!   !} {!   !}
Bislice X .Pb.Ob  = Bislice₀ X
Bislice X .Pb.Hom = Bislice₁
Bislice X .Pb.id = bislice-id
Bislice X .Pb.compose  = bislice-compose
Bislice X .Pb.unitor-l {A , f} {B , g} = to-natural-iso mk where
  mk : make-natural-iso Id (Bifunctor.Right bislice-compose (Pb.id (Bislice X)))
  mk .eta (p₀ , θ₀) = record where
    fst = B.λ→ _

    rem₁ : Hom.is-invertible (g ▶ F.₂ (B.λ← _))
    rem₁ = F-map-invertible (Bifunctor.Right compose _) (F-map-invertible F.P₁ (B.Hom.iso→invertible (B.λ≅ B.Hom.Iso⁻¹)))

    snd = sym $ Hom.invertible→monic rem₁ _ _ $
      g ▶ F.₂ (B.λ← p₀) ∘ g ▶ F.γ→ _ ∘ α→ _ ∘ (g ▶ _ ∘ ρ→ g) ◀ F.₁ p₀ ∘ θ₀
        ≡⟨ Hom.cdddr (◀.pushl refl) ⟩
      g ▶ F.₂ (B.λ← p₀) ∘ g ▶ F.γ→ _ ∘ α→ _ ∘ (g ▶ _) ◀ F.₁ p₀ ∘ ρ→ g ◀ F.₁ p₀ ∘ θ₀
        ≡⟨ Hom.cddr (Hom.extendl associator-◀-▶) ⟩
      g ▶ F.₂ (B.λ← p₀) ∘ g ▶ F.γ→ _ ∘ g ▶ (F.υ→ ◀ F.₁ p₀) ∘ α→ _ ∘ ρ→ g ◀ F.₁ p₀ ∘ θ₀
        ≡⟨ ▶.pulll3 (F.left-unit p₀) ⟩
      g ▶ λ← (F.₁ p₀) ∘ α→ (g , id , F.₁ p₀) ∘ ρ→ g ◀ F.₁ p₀ ∘ θ₀
        ≡⟨ Hom.pulll triangle-α→ ⟩
      ρ← g ◀ F.₁ p₀ ∘ ρ→ g ◀ F.₁ p₀ ∘ θ₀
        ≡⟨ ◀.cancell ρ≅.invr ⟩
      θ₀
        ≡⟨ ▶.insertl (Fr.annihilate B.λ≅.invr) ⟩
      g ▶ F.₂ (B.λ← p₀) ∘ g ▶ F.₂ (B.λ→ p₀) ∘ θ₀ ∎

  mk .inv x = record where
    fst = B.λ← _

    snd =
        Hom.cdddr (◀.pushl refl)
      ∙ Hom.cddr (Hom.extendl associator-◀-▶)
      ∙ ▶.pulll3 (F.left-unit _)
      ∙ Hom.pulll triangle-α→
      ∙ Hom.cancell (◀.annihilate ρ≅.invr)

  mk .eta∘inv _     = Σ-prop-pathp! B.λ≅.invl
  mk .inv∘eta _     = Σ-prop-pathp! B.λ≅.invr
  mk .natural _ _ _ = Σ-prop-pathp! (sym (B.λ→nat _))

Bislice X .Pb.unitor-r {A , f} {B , g} = to-natural-iso mk where
  mk : make-natural-iso Id (Bifunctor.Left bislice-compose bislice-id)
  mk .eta (p₀ , θ₀) = record where
    fst = B.ρ→ _
    snd =
      g ▶ F.₂ (B.ρ→ _) ∘ θ₀
        ≡⟨ {!   !} ⟩
      g ▶ F.γ→ _ ∘ α→ _ ∘ θ₀ ◀ _ ∘ f ▶ F.υ→ ∘ ρ→ f
        ∎
  mk .inv (p₀ , θ₀) = record where
    fst = B.ρ← _
    snd =
      g ▶ F.₂ (B.ρ← _) ∘ g ▶ F.γ→ _ ∘ α→ _ ∘ θ₀ ◀ _ ∘ f ▶ F.υ→ ∘ ρ→ f
        ≡⟨ {!   !} ⟩
      θ₀
        ∎
  mk .eta∘inv _     = Σ-prop-pathp! B.ρ≅.invl
  mk .inv∘eta _     = Σ-prop-pathp! B.ρ≅.invr
  mk .natural _ _ _ = Σ-prop-pathp! (sym (B.ρ→nat _))

Bislice X .Pb.associator {A , f} {B , g} {C , h} {D , i} = to-natural-iso mk where
  mk : make-natural-iso (compose-assocˡ Bislice₁ bislice-compose) (compose-assocʳ Bislice₁ bislice-compose)
  mk .eta ((p₀ , θ₀) , (p₁ , θ₁) , p₂ , θ₂) = record where
    fst = B.α→ _
    snd =
      i ▶ F.₂ (B.α→ _) ∘ i ▶ F.γ→ _ ∘ α→ _ ∘ (i ▶ F.γ→ _ ∘ α→ _ ∘ θ₀ ◀ _ ∘ θ₁) ◀ _ ∘ θ₂
        ≡⟨ {!   !} ⟩
      i ▶ F.γ→ _ ∘ α→ _ ∘ θ₀ ◀ _ ∘ h ▶ F.γ→ _ ∘ α→ _ ∘ θ₁ ◀ _ ∘ θ₂
        ∎
  mk .inv ((p₀ , θ₀) , (p₁ , θ₁) , p₂ , θ₂) = record where
    fst = B.α← _
    snd =
      i ▶ F.₂ (B.α← _) ∘ i ▶ F.γ→ _ ∘ α→ _ ∘ θ₀ ◀ _ ∘ h ▶ F.γ→ _ ∘ α→ _ ∘ θ₁ ◀ _ ∘ θ₂
        ≡⟨ {!   !} ⟩
      i ▶ F.γ→ _ ∘ α→ _ ∘ (i ▶ F.γ→ _ ∘ α→ _ ∘ θ₀ ◀ _ ∘ θ₁) ◀ _ ∘ θ₂
        ∎
  mk .eta∘inv _ = Σ-prop-path! B.α≅.invl
  mk .inv∘eta _ = Σ-prop-path! B.α≅.invr
  mk .natural _ _ _ = Σ-prop-path! (sym (B.α→nat _ _ _))
Bislice X .Pb.triangle f g = Σ-prop-path! (B.triangle _ _)
Bislice X .Pb.pentagon f g h i = Σ-prop-path! (B.pentagon _ _ _ _)
```
