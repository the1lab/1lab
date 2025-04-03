<!--
```agda
open import Cat.Instances.Assemblies
open import Cat.Diagram.Exponential
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Prelude

open import Data.Partial.Total
open import Data.Partial.Base
open import Data.Vec.Base using ([] ; _∷_)

open import Realisability.PCA

import Cat.Instances.Assemblies.Limits

import Realisability.Data.Pair
import Realisability.PCA.Sugar
import Realisability.Base

open is-exponential
open Exponential
```
-->

```agda
module Cat.Instances.Assemblies.Exponentials {ℓA} (𝔸 : PCA ℓA) where
```

<!--
```agda
open Realisability.Data.Pair 𝔸
open Realisability.PCA.Sugar 𝔸
open Realisability.Base 𝔸

open Cat.Instances.Assemblies.Limits 𝔸

private variable
  ℓ ℓ' : Level
  X Y Z : Assembly 𝔸 ℓ
```
-->

# Exponentials in assemblies

```agda
_⇒Asm_ : Assembly 𝔸 ℓ → Assembly 𝔸 ℓ' → Assembly 𝔸 _
(X ⇒Asm Y) .Ob         = Assembly-hom X Y
(X ⇒Asm Y) .has-is-set = hlevel 2
(X ⇒Asm Y) .realisers f = record
  { mem     = λ e → el (⌞ e ⌟ × □ ((x : ⌞ X ⌟) (a : ↯ ⌞ 𝔸 ⌟) (ah : [ X ] a ⊩ x) → [ Y ] e % a ⊩ f · x)) (hlevel 1)
  ; defined = fst
  }
(X ⇒Asm Y) .realised f = do
  record { realiser = r ; tracks = t } ← f .tracked
  pure (r .fst , r .snd , inc t)
```

```agda
asm-ev : Assembly-hom ((X ⇒Asm Y) ×Asm X) Y
asm-ev {X = X} {Y = Y} = to-assembly-hom record where
  map (f , x) = (f · x)

  realiser = val ⟨ u ⟩ `fst `· u `· (`snd `· u)

  tracks   = elim! λ f a x p q α pp p⊩f q⊩a → subst⊩ Y (p⊩f _ _ q⊩a) $
    (val ⟨ u ⟩ `fst `· u `· (`snd `· u)) ⋆ x           ≡⟨ abs-β _ [] (_ , subst ⌞_⌟ (sym α) (`pair↓₂ pp (X .defined q⊩a))) ⟩
    `fst ⋆ ⌜ x ⌝ ⋆ (`snd ⋆ ⌜ x ⌝)                      ≡⟨ ap! α ⟩
    `fst ⋆ (`pair ⋆ p ⋆ q) ⋆ (`snd ⋆ (`pair ⋆ p ⋆ q))  ≡⟨ ap₂ _%_ (`fst-β pp (X .defined q⊩a)) (`snd-β pp (X .defined q⊩a)) ⟩
    p ⋆ q                                              ∎
```

```agda
curry-asm : Assembly-hom (X ×Asm Y) Z → Assembly-hom X (Y ⇒Asm Z)
curry-asm {X = X} {Y = Y} {Z = Z} h .map x = record where
  map y   = h · (x , y)
```

<!--
```agda
  tracked = do
    record { realiser = `h ; tracks = t } ← h .tracked
    (u , u⊩x) ← X .realised x

    inc record where
      realiser = val ⟨ v ⟩ `h `· (`pair `· const (u , X .defined u⊩x) `· v)

      tracks x a a⊩x = subst⊩ Z (t _ _ (inc (u , a , refl , u⊩x , a⊩x))) $
        abs-β _ [] (_ , Y .defined a⊩x)
```
-->

```agda
curry-asm {X = X} {Y = Y} {Z = Z} h .tracked = do
  record { realiser = `h ; tracks = t } ← h .tracked
  inc record where
    realiser = val ⟨ u ⟩ ⟨ v ⟩ `h `· (`pair `· u `· v)

    tracks x a a⊩x = record where
      fst = subst ⌞_⌟ (sym (abs-βₙ [] ((_ , X .defined a⊩x) ∷ []))) (abs↓ _ _)
      snd = inc λ y b b⊩y → subst⊩ Z (t _ _ (inc (_ , _ , refl , a⊩x , b⊩y))) $
        abs-βₙ [] ((b , Y .defined b⊩y) ∷ (a , X .defined a⊩x) ∷ [])
```

<details>
<summary>All that remains is to show that evaluation and currying are
inverses, which is true at the level of the underlying sets.</summary>

```agda
Assemblies-exp : ∀ A B → Exponential (Assemblies 𝔸 ℓA) Assemblies-products Assemblies-terminal A B
Assemblies-exp A B .B^A = A ⇒Asm B
Assemblies-exp A B .ev = asm-ev
Assemblies-exp A B .has-is-exp .ƛ = curry-asm
Assemblies-exp A B .has-is-exp .commutes m = ext λ x y → refl
Assemblies-exp A B .has-is-exp .unique m' p = ext λ x y → ap map p · (x , y)

Assemblies-cc : Cartesian-closed (Assemblies 𝔸 ℓA) _ _
Assemblies-cc = record { has-exp = Assemblies-exp }
```

</details>
