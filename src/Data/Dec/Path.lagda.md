```agda
open import 1Lab.Path.IdentitySystem
open import 1Lab.Reflection.HLevel
open import 1Lab.HLevel.Retracts
open import 1Lab.HLevel
open import 1Lab.Path
open import 1Lab.Type

open import Data.Dec.Base
open import Data.List.Base

module Data.Dec.Path where
```

```agda
module Dec-path {ℓ} {A : Type ℓ} where
  Code : Dec A → Dec A → Type ℓ
  Code (yes x) (yes y) = x ≡ y
  Code (yes x) (no ¬x) = absurd (¬x x)
  Code (no ¬x) (yes x) = absurd (¬x x)
  Code (no ¬x) (no ¬y) = Lift _ ⊤

  Code-refl : ∀ x → Code x x
  Code-refl (yes x) = refl
  Code-refl (no x) = lift tt

  decode : ∀ x y → Code x y → x ≡ y
  decode (yes x) (yes y) p = ap yes p
  decode (yes x) (no ¬x) p = absurd (¬x x)
  decode (no ¬x) (yes x) p = absurd (¬x x)
  decode (no ¬x) (no ¬y) p = ap no (funext (λ x → absurd (¬y x)))

  Code-ids : is-identity-system Code Code-refl
  Code-ids .to-path = decode _ _
  Code-ids .to-path-over {yes x} {yes y} p = λ i j → p (i ∧ j)
  Code-ids .to-path-over {yes x} {no ¬x} p = absurd (¬x x)
  Code-ids .to-path-over {no ¬x} {yes x} p = absurd (¬x x)
  Code-ids .to-path-over {no ¬x} {no ¬y} p = refl

  Code-hlevel : ∀ {n} → is-hlevel A (suc n) → ∀ x y → is-hlevel (Code x y) n
  Code-hlevel a-hl (yes x) (yes y) = Path-is-hlevel' _ a-hl x y
  Code-hlevel a-hl (yes x) (no ¬x) = absurd (¬x x)
  Code-hlevel a-hl (no ¬x) (yes x) = absurd (¬x x)

  Code-hlevel {zero} a-hl (no ¬x) (no ¬y)  =
    contr (lift tt) (λ x i → lift tt)
  Code-hlevel {suc n} a-hl (no ¬x) (no ¬y) =
    is-prop→is-hlevel-suc (λ x y i → lift tt)

Dec-is-hlevel : ∀ {ℓ} n {A : Type ℓ} → is-hlevel A (suc n) → is-hlevel (Dec A) (suc n)
Dec-is-hlevel n ahl =
  identity-system→hlevel n Dec-path.Code-ids $
    Dec-path.Code-hlevel ahl

instance
  H-Level-Dec : ∀ {n} {ℓ} {A : Type ℓ} ⦃ hl : H-Level A (suc n) ⦄
              → H-Level (Dec A) (suc n)
  H-Level-Dec {n} = hlevel-instance (Dec-is-hlevel n (hlevel (suc n)))

  decomp-dec : ∀ {ℓ} {A : Type ℓ} → hlevel-decomposition (Dec A)
  decomp-dec = decomp (quote Dec-is-hlevel) (`level-minus 1 ∷ `search ∷ [])
```
