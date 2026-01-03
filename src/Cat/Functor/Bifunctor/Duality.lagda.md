<!--
```agda
open import Cat.Functor.Bifunctor
open import Cat.Instances.Product
open import Cat.Functor.Base
open import Cat.Prelude
```
-->

```agda
module Cat.Functor.Bifunctor.Duality
  {o₁ h₁ o₂ h₂ o₃ h₃ : _}
  {C : Precategory o₁ h₁}
  {D : Precategory o₂ h₂}
  {E : Precategory o₃ h₃}
  (F : Functor (C ×ᶜ D) E)
  where
```

<!--
```agda
private
  module C = Precategory C
  module D = Precategory D
  module E = Precategory E
  module F where
    open Cat.Functor.Bifunctor F public
```
-->

# Duality {defines="opposite-bifunctor"}

When considering the `opposite functor`{.Agda ident="Functor.op"} of a bifunctor, 
$\cC \times \cD \to \cE$  we would prefer to get a bifunctor 
$\cC\op \times \cD\op \to \cE\op$ (see also [[opposite product category]]).

```agda
bop : Functor ((C ^op) ×ᶜ (D ^op)) (E ^op)
bop .Functor.F₀ = F.F₀
bop .Functor.F₁ = F.F₁
bop .Functor.F-id = F.F-id
bop .Functor.F-∘ (f , f') (g , g') = F.F-∘ (g , g') (f , f')
```

This is compatible with fixing objects in the following sense:

```agda
bop-Left : ∀ {d : D.Ob} → Functor.op (F.Left d) ≡ (Left bop) d
bop-Left = Functor-path (λ x → refl) (λ f → refl)

bop-Right : ∀ {c : C.Ob} → Functor.op (F.Right c) ≡ (Right bop) c
bop-Right = Functor-path (λ x → refl) (λ f → refl)
```
