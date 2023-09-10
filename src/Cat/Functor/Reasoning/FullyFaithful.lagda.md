<!--
```agda
open import Cat.Functor.Properties
open import Cat.Prelude hiding (injective)

import Cat.Functor.Reasoning as Fr
import Cat.Reasoning
```
-->

```agda
module
  Cat.Functor.Reasoning.FullyFaithful
  {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'}
  (F : Functor C D) (ff : is-fully-faithful F)
  where
```

# Reasoning for ff functors

<!-- TODO [Amy 2022-12-14]
Write something informative here
-->

This module contains a few short combinators for reasoning about the
actions of [[fully faithful functors]] on morphisms and isomorphisms.

<!--
```agda
open Fr F public
private
  module C = Cat.Reasoning C
  module D = Cat.Reasoning D

private variable
  a b c d : C.Ob
  α β γ δ : D.Ob
  f g g' h i : C.Hom a b
  w x x' y z : D.Hom α β

module _ {a} {b} where
  open Equiv (F₁ {a} {b} , ff) public

iso-equiv : ∀ {a b} → (a C.≅ b) ≃ (F₀ a D.≅ F₀ b)
iso-equiv {a} {b} = (F-map-iso {x = a} {b} , is-ff→F-map-iso-is-equiv {F = F} ff)

module iso {a} {b} =
  Equiv (F-map-iso {x = a} {b} , is-ff→F-map-iso-is-equiv {F = F} ff)
```
-->

```agda
from-id : w ≡ D.id → from w ≡ C.id
from-id p = injective₂ (ε _ ∙ p) F-id

from-∘ : from (w D.∘ x) ≡ from w C.∘ from x
from-∘ = injective (ε _ ∙ sym (F-∘ _ _ ∙ ap₂ D._∘_ (ε _) (ε _)))

ipushr : x D.∘ F₁ g ≡ x' → from (w D.∘ x) C.∘ g ≡ from (w D.∘ x')
ipushr p = injective (F-∘ _ _ ·· ap₂ D._∘_ (ε _) refl ·· D.pullr p ∙ sym (ε _))

ε-lswizzle : w D.∘ x ≡ D.id → w D.∘ F₁ (from (x D.∘ y)) ≡ y
ε-lswizzle = D.lswizzle (ε _)

ε-expand : w D.∘ x ≡ y → F₁ (from w C.∘ from x) ≡ y
ε-expand p = F-∘ _ _ ·· ap₂ D._∘_ (ε _) (ε _) ·· p

ε-twist : F₁ f D.∘ x ≡ y D.∘ F₁ g → f C.∘ from x ≡ from y C.∘ g
ε-twist {f = f} {g = g} p = injective $ swap $
  ap (F₁ f D.∘_) (ε _) ·· p ·· ap (D._∘ F₁ g) (sym (ε _))

inv∘l : x D.∘ F₁ f ≡ y → from x C.∘ f ≡ from y
inv∘l x = sym (ε-twist (D.eliml F-id ∙ sym x)) ∙ C.idl _

whackl : x D.∘ F₁ f ≡ F₁ g → from x C.∘ f ≡ g
whackl p = sym (ε-twist (D.idr _ ∙ sym p)) ∙ C.elimr (from-id refl)

whackr : F₁ f D.∘ x ≡ F₁ g → f C.∘ from x ≡ g
whackr p = ε-twist (p ∙ sym (D.idl _)) ∙ C.eliml (from-id refl)
```
