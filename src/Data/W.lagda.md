```agda
open import 1Lab.Prelude

open import Data.Power
open import Data.Nat
open import Data.Sum

module Data.W where
```

# Well-founded trees

```
data W {ℓ ℓ′} (A : Type ℓ) (B : A → Type ℓ′) : Type (ℓ ⊔ ℓ′) where
  sup : (x : A) (f : B x → W A B) → W A B

data Acc {ℓ ℓ′} {A : Type ℓ} (R : A → A → Type ℓ′) (x : A) : Type (ℓ ⊔ ℓ′) where
  acc : (∀ y → R y x → Acc R y) → Acc R x

Acc-is-prop
  : ∀ {ℓ ℓ′} {A : Type ℓ} {R : A → A → Type ℓ′} {x : A}
  → is-prop (Acc R x)
Acc-is-prop (acc x) (acc y) = ap acc $ funext λ a → funext λ r →
  Acc-is-prop (x a r) (y a r)

record Ordinal-on {ℓ} (A : Type ℓ) : Type (lsuc ℓ) where
  field
    rel       : A → A → Type ℓ
    rel-prop  : ∀ {a b} → is-prop (rel a b)
    rel-wf    : ∀ a → Acc rel a
    rel-ext   : ∀ {a b} → (∀ c → rel c a ≃ rel c b) → a ≡ b
    rel-trans : ∀ {a b c} → rel a b → rel b c → rel a c

open Ordinal-on

<-split : ∀ {m n} → m < suc n → (m < n) ⊎ (m ≡ n)
<-split {zero} {zero} (s≤s m<sn) = inr refl
<-split {zero} {suc n} w = inl (s≤s 0≤x)
<-split {suc m} {suc n} (s≤s m<sn) with <-split m<sn
... | inl m<n = inl (s≤s m<n)
... | inr m=n = inr (ap suc m=n)

ω : Ordinal-on Nat
ω .rel = _<_
ω .rel-prop = ≤-prop
ω .rel-wf = go where
  go : ∀ a → Acc _<_ a
  go zero = acc λ { y () }
  go (suc a) with go a
  ... | acc access = acc λ y y<sa →
    Equiv.from (⊎-universal {C = λ _ → Acc _<_ y})
      ((λ x → access y x) , λ p → subst (Acc _<_) (sym p) (acc access))
      (<-split y<sa)
ω .rel-ext = go where
  go : ∀ {a b} → (∀ c → (c < a) ≃ (c < b)) → a ≡ b
  go {zero} {zero} w = refl
  go {zero} {suc b} w with Equiv.from (w b) ≤-refl
  go {zero} {suc b} w | ()
  go {suc a} {zero} w with Equiv.to (w a) ≤-refl
  go {suc a} {zero} w | ()
  go {suc a} {suc b} w = ap suc $ go λ c → prop-ext!
    (λ wit → ≤-peel (Equiv.to   (w (suc c)) (s≤s wit)))
    (λ wit → ≤-peel (Equiv.from (w (suc c)) (s≤s wit)))
ω .rel-trans (s≤s p) (s≤s (s≤s q)) = s≤s (≤-trans p (≤-trans q ≤-ascend))

{-
module _ {ℓ ℓ′} {A : Type ℓ} {B : A → Type ℓ′} where
  W-elim
    : ∀ {ℓ′′} (C : W A B → Type ℓ′′)
    → ( ∀ (x : A) (f : B x → W A B)
      → (∀ i → C (f i))
      → C (sup x f))
    → ∀ x → C x
  W-elim C unsup (sup x f) = unsup x f λ i → W-elim C unsup (f i)

  _<_ : W A B → W A B → Type _
  x < sup i f = ∃[ j ∈ B i ] (f j ≡ x)

  W-well-founded : ∀ a → Acc _<_ a
  W-well-founded (sup x f) = acc λ y y<sup →
    ∥-∥-rec Acc-is-prop (λ { (j , p) → subst (Acc _<_) p (W-well-founded (f j)) })
      y<sup
-}
