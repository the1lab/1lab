<!--
```agda
open import 1Lab.Prelude

open import Homotopy.Space.Suspension
open import Homotopy.Connectedness
open import Homotopy.Truncation
open import Homotopy.Base

open import Data.Set.Truncation
```
-->

```agda
module Homotopy.Space.Suspension.Properties where
```

# Properties of suspensions

## Connectedness {defines="connectedness-of-suspensions"}

This section contains the aforementioned proof that suspension increases
the [[connectedness]] of a space.

```agda
Susp-is-connected : ∀ {ℓ} {A : Type ℓ} n → is-n-connected A n → is-n-connected (Susp A) (suc n)
Susp-is-connected 0 a-conn = inc N
Susp-is-connected 1 a-conn = ∥-∥-proj do
  pt ← a-conn
  pure $ is-connected∙→is-connected λ where
    N           → inc refl
    S           → inc (sym (merid pt))
    (merid x i) → is-prop→pathp (λ i → ∥_∥.squash {A = merid x i ≡ N})
      (inc refl) (inc (sym (merid pt))) i
Susp-is-connected {A = A} (suc (suc n)) a-conn =
  n-Tr-elim
    (λ _ → is-n-connected (Susp A) (3 + n))
    (λ _ → is-prop→is-hlevel-suc {n = suc n} (hlevel 1))
    (λ x → contr (inc N) (n-Tr-elim _ (λ _ → is-hlevel-suc (2 + n) (n-Tr-is-hlevel (2 + n) _ _))
      (Susp-elim _ refl (ap n-Tr.inc (merid x)) λ pt →
        commutes→square (ap (refl ∙_) (rem₂ .snd _ ∙ sym (rem₂ .snd _))))))
    (conn' .centre)
  where
    conn' : is-contr (n-Tr A (2 + n))
    conn' = is-n-connected-Tr (1 + n) a-conn

    rem₁ : is-equiv λ b a → b
    rem₁ = is-n-connected→n-type-const
      {B = n-Tr.inc {n = 3 + n} N ≡ inc S} {A = A}
      (suc n) hlevel! a-conn

    rem₂ : Σ (inc N ≡ inc S) (λ p → ∀ x → ap n-Tr.inc (merid x) ≡ p)
    rem₂ = _ , λ x → sym (rem₁ .is-eqv _ .centre .snd) $ₚ x
```
