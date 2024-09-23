<!--
```agda
open import Algebra.Group.Cat.FinitelyComplete
open import Algebra.Group.Cat.Base
open import Algebra.Group.Concrete

open import Cat.Functor.Equivalence.Path
open import Cat.Diagram.Limit.Finite
open import Cat.Diagram.Product
open import Cat.Prelude

open import Homotopy.Connectedness.Automation
open import Homotopy.Connectedness

open ConcreteGroup
open is-product
open Product
```
-->

```agda
module Algebra.Group.Concrete.FinitelyComplete {ℓ} where
```

# Finite limits of concrete groups

Since the category of [[concrete groups]] is equivalent to the
[[category of groups]], and the latter is [[finitely complete]], then
so is the former.

```agda
ConcreteGroups-finitely-complete : Finitely-complete (ConcreteGroups ℓ)
ConcreteGroups-finitely-complete = subst Finitely-complete
  (sym (eqv→path ConcreteGroups-is-category Groups-is-category _ π₁F-is-equivalence))
  Groups-finitely-complete
```

However, the construction of binary [[products]] of concrete groups
(corresponding to the [[direct product of groups]]) is natural enough to
spell out explicitly: one can simply take the product of the underlying
groupoids!

```agda
Direct-product-concrete : ConcreteGroup ℓ → ConcreteGroup ℓ → ConcreteGroup ℓ
Direct-product-concrete G H .B = B G ×∙ B H
Direct-product-concrete G H .has-is-connected = is-connected→is-connected∙ $
  ×-is-n-connected 2
    (is-connected∙→is-connected (G .has-is-connected))
    (is-connected∙→is-connected (H .has-is-connected))
Direct-product-concrete G H .has-is-groupoid = ×-is-hlevel 3
  (G .has-is-groupoid)
  (H .has-is-groupoid)

ConcreteGroups-products
  : (X Y : ConcreteGroup ℓ) → Product (ConcreteGroups ℓ) X Y
ConcreteGroups-products X Y = prod where
  prod : Product (ConcreteGroups ℓ) X Y
  prod .apex = Direct-product-concrete X Y
  prod .π₁ = fst∙
  prod .π₂ = snd∙
  prod .has-is-product .⟨_,_⟩ f g .fst x = f # x , g # x
  prod .has-is-product .⟨_,_⟩ f g .snd = f .snd ,ₚ g .snd
  prod .has-is-product .π₁∘⟨⟩ = funext∙ (λ _ → refl) (∙-idr _)
  prod .has-is-product .π₂∘⟨⟩ = funext∙ (λ _ → refl) (∙-idr _)
  prod .has-is-product .unique {Q} {f} {g} {u} p1 p2 =
    funext∙ (λ x → p1 #ₚ x ,ₚ p2 #ₚ x) (fix ◁ square)
    where
      square : Square
        (p1 #ₚ pt Q ,ₚ p2 #ₚ pt Q) ((fst∙ ∘∙ u) .snd ,ₚ (snd∙ ∘∙ u) .snd)
        (f .snd ,ₚ g .snd) refl
      square i = p1 i .snd ,ₚ p2 i .snd

      fix : u .snd ≡ ((fst∙ ∘∙ u) .snd ,ₚ (snd∙ ∘∙ u) .snd)
      fix i = ∙-idr (ap fst (u .snd)) (~ i) ,ₚ ∙-idr (ap snd (u .snd)) (~ i)
```

Similarly, the [[terminal]] concrete group is just the unit type.

```agda
Terminal-concrete : ConcreteGroup ℓ
Terminal-concrete .B = Lift _ ⊤ , _
Terminal-concrete .has-is-connected = is-connected→is-connected∙ (n-connected 2)
Terminal-concrete .has-is-groupoid = hlevel 3
```
