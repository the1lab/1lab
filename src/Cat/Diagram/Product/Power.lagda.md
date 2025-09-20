<!--
```agda
open import Cat.Diagram.Product.Indexed
open import Cat.Diagram.Limit.Product
open import Cat.Functor.Adjoint.Hom
open import Cat.Diagram.Limit.Base
open import Cat.Functor.Naturality
open import Cat.Instances.Discrete
open import Cat.Instances.Product
open import Cat.Diagram.Terminal
open import Cat.Functor.Adjoint
open import Cat.Instances.Sets
open import Cat.Functor.Hom
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Diagram.Product.Power where
```

# Power {defines="power powered well-powered cotensor cotensored"}

Powering is the formal dual to [[copowering|copower]].

<!--
```agda
module Powers
  {o ℓ} {C : Precategory o ℓ}
  (prods : (S : Set ℓ) → has-products-indexed-by C ∣ S ∣)
  where

  open Indexed-product
  open Cat.Reasoning C
  open Functor
```
-->


```agda
  _⋔_ : Set ℓ → Ob → Ob
  X ⋔ A = prods X (λ _ → A) .ΠF
```

Powers satisfy the universal property that, for $X: \Sets_\kappa$ and
$A: \cC$, we have a natural isomorphism

$$
\hom_\cC(-, X \pitchfork A) \cong \hom_{\Sets}(X, \hom_\cC(-, A)).
$$

```agda
  power-hom-iso
    : ∀ {X A}
    → Hom-into C (X ⋔ A) ≅ⁿ (unopF $ opFʳ (Hom-into (Sets ℓ ^op) X)) F∘ Hom-into C A
  power-hom-iso {X} {A} = iso→isoⁿ
    (λ _ → equiv→iso (hom-iso (prods X (λ _ → A))))
    (λ _ → ext λ _ _ → sym $ assoc _ _ _)
```

```agda
  Powering : Functor (Sets ℓ ^op ×ᶜ C) C
  Powering .F₀ (X , A) = X ⋔ A
  Powering .F₁ {X , A} {Y , B} (idx , obj) = prods Y (λ _ → B) .tuple λ i →
    obj ∘ prods X (λ _ → A) .π (idx i)
  Powering .F-id {X , A} = sym $ prods X (λ _ → A) .unique _ λ i → id-comm
  Powering .F-∘ {z = Z , C} f g = sym $ prods Z (λ _ → C) .unique _ λ i →
    pulll (prods _ _ .commute) ∙ extendr (prods _ _ .commute)
```

```agda
  ∏! : (Idx : Type ℓ) ⦃ hl : H-Level Idx 2 ⦄ (F : Idx → Ob) → Ob
  ∏! Idx F = ΠF (prods (el! Idx) F)

  module ∏! (Idx : Type ℓ) ⦃ hl : H-Level Idx 2 ⦄ (F : Idx → Ob) =
    Indexed-product (prods (el! Idx) F)

  _⋔!_ : (Idx : Type ℓ) ⦃ hl : H-Level Idx 2 ⦄ → Ob → Ob
  S ⋔! X = el! S ⋔ X

  module ⋔! (Idx : Type ℓ) ⦃ hl : H-Level Idx 2 ⦄ (X : Ob) =
    Indexed-product (prods (el! Idx) (λ _ → X))
```


<!--
```agda
complete→powering
  : ∀ {o ℓ} {C : Precategory o ℓ}
  → is-complete ℓ ℓ C → Functor (Sets ℓ ^op ×ᶜ C) C
complete→powering lim = Powers.Powering λ S F → Limit→IP _ F (lim _)
```
-->
