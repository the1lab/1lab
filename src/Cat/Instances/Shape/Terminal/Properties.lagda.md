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
<!--
```agda
open is-precat-iso
open is-iso
```
-->

# Properties

We note that the [[terminal category]] is a unit to the categorical
product.

```agda
⊤Cat-unit
  : ∀ {o h} {C : Precategory o h}
  → is-precat-iso {C = ⊤Cat ×ᶜ C} Cat⟨ !F , Id ⟩
⊤Cat-unit .has-is-ff  .is-eqv (tt , f) .centre = f , refl
⊤Cat-unit .has-is-iso .is-eqv (tt , a) .centre = a , refl
⊤Cat-unit .has-is-ff  .is-eqv (tt , f) .paths (g , p) i =
  p (~ i) .snd , λ j → p (~ i ∨ j)
⊤Cat-unit .has-is-iso .is-eqv (tt , a) .paths (b , p) i =
  p (~ i) .snd , λ j → p (~ i ∨ j)
```

It is likewise isomorphic to its opposite.

```agda
⊤Cat-idemp : is-precat-iso {C = ⊤Cat ^op} {D = ⊤Cat} !F
⊤Cat-idemp  .has-is-ff  .is-eqv _ .centre = _ , refl
⊤Cat-idemp  .has-is-iso .is-eqv _ .centre = _ , refl
⊤Cat-idemp  .has-is-ff  .is-eqv _ .paths (_ , _) = refl
⊤Cat-idemp  .has-is-iso .is-eqv _ .paths (_ , _) = refl
```
