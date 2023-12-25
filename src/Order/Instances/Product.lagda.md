

<!--
```agda
open import 1Lab.Type using (⊥)

open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Prelude

open import Data.Set.Truncation
open import Data.Id.Base
open import Data.Sum

open import Order.Base

import Order.Reasoning as Pr

open is-product
open Terminal
open Product
```
-->

```agda
module Order.Instances.Product where
```
# Products of posets

The product of two [[partially ordered sets]] $P , Q$ is a
poset.

[partially ordered sets]: Order.Base.html


```agda
_×ᵖ_ : ∀ {o o' ℓ ℓ'} → Poset o ℓ → Poset o' ℓ' → Poset (o ⊔ o') (ℓ ⊔ ℓ')
P ×ᵖ Q = po module ×ᵖ where
  module P = Pr P
  module Q = Pr Q
    
  po : Poset _ _
  po .Poset.Ob = P.Ob × Q.Ob
  po .Poset._≤_ (x , x') (y , y') = x P.≤ y × x' Q.≤ y'
  po .Poset.≤-thin = hlevel!
  po .Poset.≤-refl = P.≤-refl , Q.≤-refl
  po .Poset.≤-trans (f≤g , f≤g') (g≤h , g≤h') = P.≤-trans f≤g g≤h , Q.≤-trans f≤g' g≤h'
  po .Poset.≤-antisym (f≤g , f≤g') (g≤f , g≤f') = ext (P.≤-antisym f≤g g≤f , Q.≤-antisym f≤g' g≤f')

{-# DISPLAY ×ᵖ.po a b = a ×ᵖ b #-}
infixr 20 _×ᵖ_

```

<!--
```agda
module _ {o o' ℓ ℓ'} {P : Poset o ℓ} {Q : Poset o' ℓ'} where
```
-->

```agda
  Fstᵖ : Monotone (P ×ᵖ Q) P
  Fstᵖ .hom = fst
  Fstᵖ .pres-≤ = fst

  Sndᵖ : Monotone (P ×ᵖ Q) Q
  Sndᵖ .hom = snd
  Sndᵖ .pres-≤ = snd

  Pairᵖ : ∀ {o ℓ} {R : Poset o ℓ} → Monotone R P → Monotone R Q → Monotone R (P ×ᵖ Q)
  Pairᵖ f g .hom x = f # x , g # x
  Pairᵖ f g .pres-≤ x≤y = f .pres-≤ x≤y , g .pres-≤ x≤y
```

We can show that this really is the product in $\Pos$.

```agda
Posets-has-products : ∀ {o ℓ} → has-products (Posets o ℓ)
Posets-has-products P Q .apex = P ×ᵖ Q 
Posets-has-products P Q .π₁ = Fstᵖ
Posets-has-products P Q .π₂ = Sndᵖ
Posets-has-products P Q .has-is-product .⟨_,_⟩ = Pairᵖ
Posets-has-products P Q .has-is-product .π₁∘factor = trivial!
Posets-has-products P Q .has-is-product .π₂∘factor = trivial!
Posets-has-products P Q .has-is-product .unique other α β = ext λ x → happly (ap hom α) x , happly (ap hom β) x

Posets-terminal : ∀ {o ℓ} → Terminal (Posets o ℓ)
Posets-terminal .top = 𝟙ᵖ
Posets-terminal .has⊤ P .centre .hom _ = lift tt
Posets-terminal .has⊤ P .centre .pres-≤ _ = lift tt
Posets-terminal .has⊤ P .paths f = trivial!
```
