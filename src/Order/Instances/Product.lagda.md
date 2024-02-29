

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

Specialising the construction of [[pointwise orderings]], we can show
that the [[product]] of two [[partial orders]] $P, Q$ is given by
equipping the product of their underlying sets with an ordering given on
components:

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
  po .Poset.≤-trans   (f≤g , f≤g') (g≤h , g≤h') =
    P.≤-trans f≤g g≤h , Q.≤-trans f≤g' g≤h'
  po .Poset.≤-antisym (f≤g , f≤g') (g≤f , g≤f') = ext $
    P.≤-antisym f≤g g≤f , Q.≤-antisym f≤g' g≤f'

{-# DISPLAY ×ᵖ.po a b = a ×ᵖ b #-}
infixr 20 _×ᵖ_

```

<!--
```agda
module _ {o o' ℓ ℓ'} {P : Poset o ℓ} {Q : Poset o' ℓ'} where
```
-->

```agda
  fstᵖ : Monotone (P ×ᵖ Q) P
  fstᵖ .hom    = fst
  fstᵖ .pres-≤ = fst

  sndᵖ : Monotone (P ×ᵖ Q) Q
  sndᵖ .hom    = snd
  sndᵖ .pres-≤ = snd

  pairᵖ
    : ∀ {o ℓ} {R : Poset o ℓ}
    → Monotone R P
    → Monotone R Q
    → Monotone R (P ×ᵖ Q)
  pairᵖ f g .hom      x = f # x , g # x
  pairᵖ f g .pres-≤ x≤y = f .pres-≤ x≤y , g .pres-≤ x≤y
```

It's straightforward to show this really is the product in $\Pos$.

```agda
Posets-has-products : ∀ {o ℓ} → has-products (Posets o ℓ)
Posets-has-products P Q .apex = P ×ᵖ Q
Posets-has-products P Q .π₁ = fstᵖ
Posets-has-products P Q .π₂ = sndᵖ
Posets-has-products P Q .has-is-product .⟨_,_⟩     = pairᵖ
Posets-has-products P Q .has-is-product .π₁∘factor = trivial!
Posets-has-products P Q .has-is-product .π₂∘factor = trivial!
Posets-has-products P Q .has-is-product .unique other α β =
  ext λ x → α #ₚ x , β #ₚ x
```

As a related observation, we can show that the unique partial order on
the set with one element is the [[terminal object]] in $\Pos$.

```agda
Posets-terminal : ∀ {o ℓ} → Terminal (Posets o ℓ)
Posets-terminal .top = 𝟙ᵖ
Posets-terminal .has⊤ P .centre .hom    _ = lift tt
Posets-terminal .has⊤ P .centre .pres-≤ _ = lift tt
Posets-terminal .has⊤ P .paths f = trivial!
```
