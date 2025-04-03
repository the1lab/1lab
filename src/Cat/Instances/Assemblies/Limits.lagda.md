<!--
```agda
open import Cat.Instances.Assemblies
open import Cat.Diagram.Equaliser
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Prelude

open import Data.Partial.Total
open import Data.Partial.Base
open import Data.Vec.Base using ([] ; _∷_)

open import Realisability.PCA

import Realisability.Data.Pair
import Realisability.PCA.Sugar
import Realisability.Base
```
-->

```agda
module Cat.Instances.Assemblies.Limits {ℓA} (𝔸 : PCA ℓA) where
```

<!--
```agda
open Realisability.Data.Pair 𝔸
open Realisability.PCA.Sugar 𝔸
open Realisability.Base 𝔸

open is-equaliser
open is-product
open Equaliser
open Terminal
open Product

private variable
  ℓ ℓ' : Level
  X Y Z : Assembly 𝔸 ℓ
```
-->

# Finite limits of assemblies

```agda
_×Asm_ : Assembly 𝔸 ℓ → Assembly 𝔸 ℓ' → Assembly 𝔸 (ℓ ⊔ ℓ')
(X ×Asm Y) .Ob         = ⌞ X ⌟ × ⌞ Y ⌟
(X ×Asm Y) .has-is-set = hlevel 2

(X ×Asm Y) .realisers (x , y) = record where
  mem p = elΩ $
    Σ[ a ∈ ↯ ⌞ 𝔸 ⌟ ] Σ[ b ∈ ↯ ⌞ 𝔸 ⌟ ]
      p ≡ `pair ⋆ a ⋆ b × [ X ] a ⊩ x × [ Y ] b ⊩ y

  defined : {a : ↯ ⌞ 𝔸 ⌟} → a ∈ mem → ⌞ a ⌟
  defined = rec! λ a b p rx ry →
    subst ⌞_⌟ (sym p) (`pair↓₂ (X .defined rx) (Y .defined ry))

(X ×Asm Y) .realised (x , y) = do
  (px , rx) ← X .realised x
  (py , ry) ← Y .realised y
  pure (`pair ⋆ px ⋆ py , inc (px , py , refl , rx , ry))
```

```agda
Assemblies-products : has-products (Assemblies 𝔸 ℓ)
Assemblies-products X Y .apex = X ×Asm Y
Assemblies-products X Y .π₁ = to-assembly-hom record where
  map (x , _) = x
  realiser    = `fst
  tracks x    = elim! λ a p q α rx ry → subst⊩ X rx $
    `fst ⋆ a                ≡⟨ ap (`fst ⋆_) α ⟩
    `fst ⋆ (`pair ⋆ p ⋆ q)  ≡⟨ `fst-β (X .defined rx) (Y .defined ry) ⟩
    p                       ∎

Assemblies-products X Y .π₂ = to-assembly-hom record where
  map (_ , x) = x
  realiser    = `snd
  tracks x    = elim! λ a p q α rx ry → subst⊩ Y ry $
    ap (`snd ⋆_) α ∙ `snd-β (X .defined rx) (Y .defined ry)

Assemblies-products X Y .has-is-product .⟨_,_⟩ {Q = Q} f g = record where
  map x = f · x , g · x

  tracked = do
    rf ← f .tracked
    rg ← g .tracked
    inc record where
      realiser = val ⟨ x ⟩ `pair `· (rf `· x) `· (rg `· x)

      tracks x a qx = inc
        ( rf ⋆ a , rg ⋆ a , abs-β _ _ (a , Q .defined qx)
        , rf .tracks qx , rg .tracks qx )

Assemblies-products X Y .has-is-product .π₁∘⟨⟩ = ext λ _ → refl
Assemblies-products X Y .has-is-product .π₂∘⟨⟩ = ext λ _ → refl
Assemblies-products X Y .has-is-product .unique p q = ext λ a →
  ap map p · a ,ₚ ap map q · a
```

```agda
Assemblies-terminal : Terminal (Assemblies 𝔸 ℓ)
Assemblies-terminal .top .Ob = Lift _ ⊤
Assemblies-terminal .top .has-is-set = hlevel 2
Assemblies-terminal .top .realisers _ = record { mem = def ; defined = λ x → x }
Assemblies-terminal .top .realised x = inc (val ⟨ x ⟩ x)

Assemblies-terminal .has⊤ X .centre = to-assembly-hom record where
  map    _      = lift tt
  realiser      = val ⟨ x ⟩ x
  tracks x a ha = subst ⌞_⌟ (sym (abs-β _ [] (a , X .defined ha))) (X .defined ha)

Assemblies-terminal .has⊤ X .paths x = trivial!
```

```agda
Equ-asm : (f g : Assembly-hom X Y) → Assembly 𝔸 _
Equ-asm {X = X} f g .Ob = Σ[ x ∈ X ] (f · x ≡ g · x)
Equ-asm {X = X} f g .has-is-set = hlevel 2
Equ-asm {X = X} f g .realisers (x , _) = X .realisers x
Equ-asm {X = X} f g .realised  (x , _) = X .realised x

Assemblies-equalisers : has-equalisers (Assemblies 𝔸 ℓ)
Assemblies-equalisers f g .apex = Equ-asm f g
Assemblies-equalisers {a = A} f g .equ = to-assembly-hom record where
  map (x , _)   = x
  realiser      = val ⟨ x ⟩ x
  tracks x a ha = subst⊩ A ha (abs-β _ [] (a , A .defined ha))

Assemblies-equalisers f g .has-is-eq .equal = ext λ x p → p
Assemblies-equalisers {a = A} f g .has-is-eq .universal {e' = e'} p =
  record where
    map x  = e' · x , ap map p · x
    tracked = do
      et ← e' .tracked
      inc record { [_]_⊢_ et }

Assemblies-equalisers f g .has-is-eq .factors = trivial!
Assemblies-equalisers f g .has-is-eq .unique p = ext λ a →
  Σ-prop-path! (ap map p · a)
```
