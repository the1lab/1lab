

<!--
```agda
open import Cat.Prelude
open import Order.Base
open import Data.Id.Base
open import Data.Set.Truncation

import Order.Reasoning as Pr

open import Cat.Diagram.Coproduct
open import Cat.Diagram.Initial

open import Data.Sum
open import 1Lab.Type using (⊥)


open Coproduct
open is-coproduct
open Initial


```
-->

```agda
module Order.Instances.Coproduct where
```

# Coproducts of posets

The coproduct of two [[partially ordered sets]] $P , Q$ is also a partially ordered set.

[partially ordered sets]: Order.Base.html


```agda
_⊎ᵖ_ : ∀ {o o' ℓ} → Poset o ℓ → Poset o' ℓ → Poset _ _
P ⊎ᵖ Q = po module ⊎ᵖ where
  module P = Pr P
  module Q = Pr Q
    
  po : Poset _ _
  po .Poset.Ob = P.Ob ⊎ Q.Ob
  po .Poset._≤_ (inl x) (inl y) = x P.≤ y
  po .Poset._≤_ (inr x) (inr y) = x Q.≤ y
  po .Poset._≤_ (inl x) (inr y) = Lift _ ⊥
  po .Poset._≤_ (inr x) (inl y) = Lift _ ⊥
  po .Poset.≤-thin {inl x} {inl y} = hlevel!
  po .Poset.≤-thin {inr x} {inr y} = hlevel!
  po .Poset.≤-refl {inl x} = P.≤-refl
  po .Poset.≤-refl {inr x} = Q.≤-refl
  po .Poset.≤-trans {inl x} {inl y} {inl z} = P.≤-trans
  po .Poset.≤-trans {inr x} {inr y} {inr z} = Q.≤-trans
  po .Poset.≤-antisym {inl x} {inl y} x≤y y≤x = ap inl (P.≤-antisym x≤y y≤x)
  po .Poset.≤-antisym {inr x} {inr y} x≤y y≤x = ap inr (Q.≤-antisym x≤y y≤x)

{-# DISPLAY ⊎ᵖ.po a b = a ⊎ᵖ b #-}
infixr 15 _⊎ᵖ_
```

<!--
```agda
module _ {o o' ℓ} {P : Poset o ℓ} {Q : Poset o' ℓ} where
```
-->
```agda
  Inlᵖ : Monotone P (P ⊎ᵖ Q)
  Inlᵖ .hom = inl
  Inlᵖ .pres-≤ x≤y = x≤y

  Inrᵖ : Monotone Q (P ⊎ᵖ Q)
  Inrᵖ .hom = inr
  Inrᵖ .pres-≤ x≤y = x≤y

  Matchᵖ : ∀ {o ℓ} {R : Poset o ℓ} → Monotone P R → Monotone Q R → Monotone (P ⊎ᵖ Q) R
  Matchᵖ f g .hom (inl x) = f # x
  Matchᵖ f g .hom (inr x) = g # x
  Matchᵖ f g .pres-≤ {inl x} {inl y} = f .pres-≤
  Matchᵖ f g .pres-≤ {inr x} {inr y} = g .pres-≤
```

We can show that this really is the coproduct in $\Pos$.

```agda
Posets-has-coproducts : ∀ {o ℓ} → has-coproducts (Posets o ℓ)
Posets-has-coproducts P Q .coapex = P ⊎ᵖ Q
Posets-has-coproducts P Q .in₀ = Inlᵖ
Posets-has-coproducts P Q .in₁ = Inrᵖ
Posets-has-coproducts P Q .has-is-coproduct .is-coproduct.[_,_] = Matchᵖ
Posets-has-coproducts P Q .has-is-coproduct .in₀∘factor = trivial!
Posets-has-coproducts P Q .has-is-coproduct .in₁∘factor = trivial!
Posets-has-coproducts P Q .has-is-coproduct .unique other α β = ext λ where
  (inl x) → happly (ap hom α) x
  (inr x) → happly (ap hom β) x

Posets-initial : ∀ {o ℓ} → Initial (Posets o ℓ)
Posets-initial .bot = 𝟘ᵖ
Posets-initial .has⊥ P .centre .hom ()
Posets-initial .has⊥ P .centre .pres-≤ ()
Posets-initial .has⊥ P .paths f = ext λ ()
```