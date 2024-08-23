---
description: |
  Addition of ordinals.
---
<!--
```agda
open import 1Lab.Prelude

open import Data.Wellfounded.Base
open import Data.Sum

open import Order.Ordinal

import Order.Ordinal.Reasoning
```
-->
```agda
module Order.Ordinal.Instances.Plus where
```

# Addition of ordinals

```agda
_+ₒ_ : ∀ {o ℓ o' ℓ'} → Ordinal o ℓ → Ordinal o' ℓ' → Ordinal (o ⊔ o') (ℓ ⊔ ℓ')
_+ₒ_ {ℓ = ℓ} {ℓ' = ℓ'} X Y = ord module +ₒ where
  module X = Order.Ordinal.Reasoning X
  module Y = Order.Ordinal.Reasoning Y

  _≺_ : ⌞ X ⌟ ⊎ ⌞ Y ⌟ → ⌞ X ⌟ ⊎ ⌞ Y ⌟ → Type _
  inl x ≺ inl x' = Lift ℓ' (x X.≺ x')
  inl x ≺ inr y' = Lift _ ⊤
  inr y ≺ inl x' = Lift _ ⊥
  inr y ≺ inr y' = Lift ℓ (y Y.≺ y')

  ord : Ordinal _ _
  ord .Ordinal.Ob = ⌞ X ⌟ ⊎ ⌞ Y ⌟
  ord .Ordinal._≺_ = _≺_
  ord .Ordinal.≺-wf = go where
    wrapperl : ∀ x → Acc X._≺_ x → Acc _≺_ (inl x)
    workerl : ∀ x → (∀ xₒ → xₒ X.≺ x → Acc X._≺_ xₒ) → ∀ a → a ≺ inl x → Acc _≺_ a

    wrapperl x (acc rec) = acc (workerl x rec)
    workerl x rec (inl xₒ) (lift xₒ≺x) = wrapperl xₒ (rec xₒ xₒ≺x)

    wrapperr : ∀ y → Acc Y._≺_ y → Acc _≺_ (inr y)
    workerr : ∀ y → (∀ yₒ → yₒ Y.≺ y → Acc Y._≺_ yₒ) → ∀ a → a ≺ inr y → Acc _≺_ a

    wrapperr y (acc rec) = acc (workerr y rec)
    workerr y rec (inl xₒ) (lift tt) = wrapperl xₒ (X.≺-wf xₒ)
    workerr y rec (inr yₒ) (lift yₒ≺y) = wrapperr yₒ (rec yₒ yₒ≺y)

    go : (xy : ⌞ X ⌟ ⊎ ⌞ Y ⌟) → Acc _≺_ xy
    go (inl x) = wrapperl x (X.≺-wf x)
    go (inr y) = wrapperr y (Y.≺-wf y)
  ord .Ordinal.≺-ext {inl x} {inl x'} p q =
    ap inl $ X.≺-ext
      (λ xₒ xₒ≺x → Lift.lower (p (inl xₒ) (lift xₒ≺x)))
      (λ xₒ xₒ≺x' → Lift.lower (q (inl xₒ) (lift xₒ≺x')))
  ord .Ordinal.≺-ext {inl x} {inr y'} p q =
    absurd (X.≺-irrefl (Lift.lower $ q (inl x) (lift tt)))
  ord .Ordinal.≺-ext {inr y} {inl x'} p q =
    absurd (X.≺-irrefl (Lift.lower $ p (inl x') (lift tt)))
  ord .Ordinal.≺-ext {inr y} {inr y'} p q =
      ap inr $ Y.≺-ext
      (λ yₒ yₒ≺y → Lift.lower (p (inr yₒ) (lift yₒ≺y)))
      (λ yₒ yₒ≺y' → Lift.lower (q (inr yₒ) (lift yₒ≺y')))
  ord .Ordinal.≺-trans {inl xₒ} {inl x₁} {inl x₂} (lift xₒ≺x₁) (lift x₁≺x₂) = lift (X.≺-trans xₒ≺x₁ x₁≺x₂)
  ord .Ordinal.≺-trans {inl xₒ} {inl x₁} {inr y₂} _ _ = lift tt
  ord .Ordinal.≺-trans {inl xₒ} {inr y₁} {inl x₂} _ (lift ff) = absurd ff
  ord .Ordinal.≺-trans {inl xₒ} {inr y₁} {inr y₂} _ _ = lift tt
  ord .Ordinal.≺-trans {inr yₒ} {inl x₁} {_} (lift ff) _ = absurd ff
  ord .Ordinal.≺-trans {inr yₒ} {inr y₁} {inl x₂} _ (lift ff) = absurd ff
  ord .Ordinal.≺-trans {inr yₒ} {inr y₁} {inr y₂} (lift yₒ≺y₁) (lift y₁≺y₂) = lift (Y.≺-trans yₒ≺y₁ y₁≺y₂)
  ord .Ordinal.≺-is-prop {inl x} {inl x'} = hlevel 1
  ord .Ordinal.≺-is-prop {inl x} {inr y'} = hlevel 1
  ord .Ordinal.≺-is-prop {inr y} {inl x'} = hlevel 1
  ord .Ordinal.≺-is-prop {inr y} {inr y'} = hlevel 1
```
