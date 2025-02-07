<!--
```agda
open import Cat.Functor.Equivalence.Path
open import Cat.Instances.Shape.Terminal
open import Cat.Functor.Equivalence
open import Cat.Instances.Product
open import Cat.Prelude
```
-->

```agda
module Cat.Instances.Shape.Terminal.Properties where
```

# Properties

We note that the [[terminal category]] is a unit to the categorical product.

```agda
⊤Cat-unit : ∀ {o h} {C : Precategory o h} → ⊤Cat ×ᶜ C ≡ C
⊤Cat-unit = sym $ Precategory-path Cat⟨ !F , Id ⟩ Cat⟨!F,Id⟩-is-iso where
  open is-precat-iso
  open is-iso
  Cat⟨!F,Id⟩-is-iso : is-precat-iso Cat⟨ !F , Id ⟩
  Cat⟨!F,Id⟩-is-iso .has-is-ff  .is-eqv (tt , f) .centre = f , refl
  Cat⟨!F,Id⟩-is-iso .has-is-iso .is-eqv (tt , a) .centre = a , refl
  Cat⟨!F,Id⟩-is-iso .has-is-ff  .is-eqv (tt , f) .paths (g , p) i = p (~ i) .snd , λ j → p (~ i ∨ j)
  Cat⟨!F,Id⟩-is-iso .has-is-iso .is-eqv (tt , a) .paths (b , p) i = p (~ i) .snd , λ j → p (~ i ∨ j)
```
