<!--
```agda
open import 1Lab.Reflection.HLevel
open import 1Lab.Reflection hiding (def ; absurd)

open import Cat.Functor.Adjoint
open import Cat.Prelude

open import Data.Partial.Total
open import Data.Partial.Base

open import Realisability.PCA

import Realisability.Data.Pair
import Realisability.PCA.Sugar
import Realisability.Base

open Functor
open _=>_
open _⊣_
```
-->

```agda
module Cat.Instances.Assemblies
  {ℓA} {A : Type ℓA} ⦃ _ : H-Level A 2 ⦄ {_%_ : ↯ A → ↯ A → ↯ A} (p : is-pca _%_)
  where
```

<!--
```agda
open Realisability.Data.Pair p
open Realisability.PCA.Sugar p
open Realisability.Base p

private variable
  ℓ ℓ' : Level
```
-->

# Assemblies over a PCA

```agda
record Assembly ℓ : Type (lsuc ℓ ⊔ ℓA) where
  field
    Ob         : Type ℓ
    has-is-set : is-set Ob
    realisers  : Ob → ℙ⁺ A
    realised   : ∀ x → ∃[ a ∈ ↯ A ] (a ∈ realisers x)
```

<!--
```agda
open Assembly

private variable
  X Y Z : Assembly ℓ

instance
  Underlying-Assembly : Underlying (Assembly ℓ)
  Underlying-Assembly = record { ⌞_⌟ = Assembly.Ob }

  hlevel-proj-asm : hlevel-projection (quote Assembly.Ob)
  hlevel-proj-asm .hlevel-projection.has-level = quote Assembly.has-is-set
  hlevel-proj-asm .hlevel-projection.get-level _ = pure (quoteTerm (suc (suc zero)))
  hlevel-proj-asm .hlevel-projection.get-argument (_ ∷ c v∷ _) = pure c
  {-# CATCHALL #-}
  hlevel-proj-asm .hlevel-projection.get-argument _ = typeError []

module _ (X : Assembly ℓ) (a : ↯ A) (x : ⌞ X ⌟) where open Ω (X .realisers x .mem a) renaming (∣_∣ to [_]_⊩_) public
```
-->

```agda
record Assembly-hom (X : Assembly ℓ) (Y : Assembly ℓ') : Type (ℓA ⊔ ℓ ⊔ ℓ') where
  field
    map     : ⌞ X ⌟ → ⌞ Y ⌟
    tracked : ∥ [ map ] X .realisers ⊢ Y .realisers ∥
```

<!--
```agda
open Assembly-hom public

private unquoteDecl eqv = declare-record-iso eqv (quote Assembly-hom)

instance
  H-Level-Assembly-hom : ∀ {n} → H-Level (Assembly-hom X Y) (2 + n)
  H-Level-Assembly-hom = basic-instance 2 $ Iso→is-hlevel 2 eqv (hlevel 2)

  Extensional-Assembly-hom : ∀ {ℓr} ⦃ _ : Extensional (⌞ X ⌟ → ⌞ Y ⌟) ℓr ⦄ → Extensional (Assembly-hom X Y) ℓr
  Extensional-Assembly-hom ⦃ e ⦄ = injection→extensional! (λ p → Iso.injective eqv (Σ-prop-path! p)) e

  Funlike-Assembly-hom : Funlike (Assembly-hom X Y) ⌞ X ⌟ λ _ → ⌞ Y ⌟
  Funlike-Assembly-hom = record { _·_ = λ f x → f .map x }

module _ where
  open Precategory
```
-->

```agda
  Assemblies : ∀ ℓ → Precategory (lsuc ℓ ⊔ ℓA) (ℓA ⊔ ℓ)
  Assemblies ℓ .Ob      = Assembly ℓ
  Assemblies ℓ .Hom     = Assembly-hom
  Assemblies ℓ .Hom-set x y = hlevel 2
  Assemblies ℓ .id      = record
    { map     = λ x → x
    ; tracked = inc id⊢
    }
  Assemblies ℓ ._∘_ f g = record
    { map     = λ x → f · (g · x)
    ; tracked = ⦇ f .tracked ∘⊢ g .tracked ⦈
    }
  Assemblies ℓ .idr   f     = ext λ _ → refl
  Assemblies ℓ .idl   f     = ext λ _ → refl
  Assemblies ℓ .assoc f g h = ext λ _ → refl
```

## Classical assemblies

```agda
∇ : ∀ {ℓ} (X : Type ℓ) ⦃ _ : H-Level X 2 ⦄ → Assembly ℓ
∇ X .Ob          = X
∇ X .has-is-set  = hlevel 2
∇ X .realisers x = record
  { mem     = def
  ; defined = λ x → x
  }
∇ X .realised x = inc (expr ⟨ x ⟩ x , abs↓ _ _)

Cofree : Functor (Sets ℓ) (Assemblies ℓ)
Cofree .F₀ X = ∇ ⌞ X ⌟
Cofree .F₁ f = record
  { map     = f
  ; tracked = inc record
    { realiser = val ⟨ x ⟩ x
    ; tracks   = λ a ha → subst ⌞_⌟ (sym (abs-β _ [] (a , ha))) ha
    }
  }
Cofree .F-id    = ext λ _ → refl
Cofree .F-∘ f g = ext λ _ → refl

Forget : Functor (Assemblies ℓ) (Sets ℓ)
Forget .F₀ X    = el! ⌞ X ⌟
Forget .F₁ f    = f ·_
Forget .F-id    = refl
Forget .F-∘ f g = refl

Forget⊣∇ : Forget {ℓ} ⊣ Cofree
Forget⊣∇ .unit .η X = record
  { map     = λ x → x
  ; tracked = inc record
    { realiser = val ⟨ x ⟩ x
    ; tracks   = λ a ha → subst ⌞_⌟ (sym (abs-β _ [] (a , X .realisers _ .defined ha))) (X .realisers _ .defined ha)
    }
  }
Forget⊣∇ .unit .is-natural x y f = ext λ _ → refl
Forget⊣∇ .counit .η X a = a
Forget⊣∇ .counit .is-natural x y f = refl
Forget⊣∇ .zig = refl
Forget⊣∇ .zag = ext λ _ → refl
```

## The assembly of booleans

```agda
𝟚 : Assembly lzero
𝟚 .Ob = Bool
𝟚 .has-is-set  = hlevel 2
𝟚 .realisers true  = record
  { mem     = λ x → elΩ (`true .fst ≡ x)
  ; defined = rec! λ p → subst ⌞_⌟ p (`true .snd)
  }
𝟚 .realisers false = record
  { mem     = λ x → elΩ (`false .fst ≡ x)
  ; defined = rec! λ p → subst ⌞_⌟ p (`false .snd)
  }
𝟚 .realised true  = inc (`true .fst , inc refl)
𝟚 .realised false = inc (`false .fst , inc refl)
```

```agda
non-constant-nabla-map
  : (f : Assembly-hom (∇ Bool) 𝟚)
  → f · true ≠ f · false
  → `true .fst ≡ `false .fst
non-constant-nabla-map f x = case f .tracked of λ where
  record { realiser = (fp , f↓) ; tracks = t } →
    let
      a = t {true}  (`true .fst) (`true .snd)
      b = t {false} (`true .fst) (`true .snd)

      cases
        : ∀ b b' (x : ↯ A)
        → [ 𝟚 ] x ⊩ b → [ 𝟚 ] x ⊩ b'
        → b ≠ b' → `true .fst ≡ `false .fst
      cases = λ where
        true true   p → rec! λ rb rb' t≠t → absurd (t≠t refl)
        true false  p → rec! λ rb rb' _   → rb ∙ sym rb'
        false true  p → rec! λ rb rb' _   → rb' ∙ sym rb
        false false p → rec! λ rb rb' f≠f → absurd (f≠f refl)
    in cases (f · true) (f · false) _ a b x
```
