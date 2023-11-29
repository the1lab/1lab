<!--
```agda
open import Cat.Instances.Sets
open import Cat.Functor.Base
open import Cat.Prelude

open import Order.Morphism
open import Order.Base

import Cat.Reasoning
```
-->

```agda
module Order.Univalent where
```

# The Category of Posets is Univalent

```agda
Poset-path : ∀ {o ℓ} {P Q : Poset o ℓ} → P Posets.≅ Q → P ≡ Q
Poset-path {P = P} {Q} f = path where
  module P = Poset P
  module Q = Poset Q
  open Posets

  P≃Q : ⌞ P ⌟ ≃ ⌞ Q ⌟
  P≃Q = iso→equiv (F-map-iso Forget-poset f)

  ob : ∀ i → Type _
  ob i = ua P≃Q i

  order : PathP (λ i → ob i → ob i → Type _) P._≤_ Q._≤_
  order i x y = Glue (unglue (∂ i) x Q.≤ unglue (∂ i) y) λ where
    (i = i0) → x P.≤ y , iso→≤-equiv f
    (i = i1) → x Q.≤ y , _ , id-equiv

  order-thin : ∀ i x y → is-prop (order i x y)
  order-thin i = coe0→i (λ i → (x y : ob i) → is-prop (order i x y)) i hlevel!

  ob-set : ∀ i → is-set (ob i)
  ob-set i = coe0→i (λ i → is-set (ob i)) i hlevel!

  path : P ≡ Q
  path i .Poset.Ob      = ob i
  path i .Poset._≤_ x y = order i x y
  path i .Poset.≤-thin {x} {y} =
    is-prop→pathp
      (λ i →
        Π-is-hlevel² {A = ob i} {B = λ _ → ob i} 1 λ x y →
        is-prop-is-prop {A = order i x y})
      (λ _ _ → P.≤-thin)
      (λ _ _ → Q.≤-thin) i x y
  path i .Poset.≤-refl {x = x} =
    is-prop→pathp
      (λ i → Π-is-hlevel {A = ob i} 1 λ x → order-thin i x x)
        (λ _ → P.≤-refl)
        (λ _ → Q.≤-refl) i x
  path i .Poset.≤-trans {x} {y} {z} x≤y y≤z =
    is-prop→pathp
      (λ i →
        Π-is-hlevel³ {A = ob i} {B = λ _ → ob i} {C = λ _ _ → ob i} 1 λ x y z →
        Π-is-hlevel² {A = order i x y} {B = λ _ → order i y z} 1 λ _ _ →
        order-thin i x z)
      (λ _ _ _ → P.≤-trans)
      (λ _ _ _ → Q.≤-trans) i x y z x≤y y≤z
  path i .Poset.≤-antisym {x} {y} x≤y y≤x =
    is-prop→pathp
      (λ i →
        Π-is-hlevel² {A = ob i } {B = λ _ → ob i} 1 λ x y →
        Π-is-hlevel² {A = order i x y} {B = λ _ → order i y x} 1 λ _ _ →
        ob-set i x y)
      (λ _ _ → P.≤-antisym)
      (λ _ _ → Q.≤-antisym) i x y x≤y y≤x
```

```agda
Posets-is-category : ∀ {o ℓ} → is-category (Posets o ℓ)
Posets-is-category .to-path = Poset-path
Posets-is-category .to-path-over f =
  Posets.≅-pathp refl (Poset-path f)
    (Monotone-pathp (funextP (λ x → path→ua-pathp _ refl)))
```
