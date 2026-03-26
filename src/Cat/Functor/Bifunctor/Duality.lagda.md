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
  (F : Bifunctor C D E)
  where
```

<!--
```agda
private
  module C = Precategory C
  module D = Precategory D
  module E = Precategory E
  module F = Bifunctor F
open Make-bifunctor
```
-->

# Duality {defines="opposite-bifunctor"}

When considering the `opposite functor`{.Agda ident="Functor.op"} of a bifunctor,
$\cC \times \cD \to \cE$  we would prefer to get a bifunctor
$\cC\op \times \cD\op \to \cE\op$ (see also [[opposite product category]]).

```agda
bop : Bifunctor (C ^op) (D ^op) (E ^op)
bop = make-bifunctor λ where
  .F₀   → F.F₀
  .lmap → F.lmap
  .rmap → F.rmap
  .lmap-id → F.lmap-id
  .rmap-id → F.rmap-id
  .lmap-∘ f g → F.lmap-∘ _ _
  .rmap-∘ f g → F.rmap-∘ _ _
  .lrmap  f g → F.rlmap g f
```

This is compatible with fixing objects in the following sense:

```agda
bop-Left : ∀ {d : D.Ob} → Functor.op (F.Left d) ≡ Bifunctor.Left bop d
bop-Left = Functor-path (λ x → refl) (λ f → refl)

bop-Right : ∀ {c : C.Ob} → Functor.op (F.Right c) ≡ Bifunctor.Right bop c
bop-Right = Functor-path (λ x → refl) (λ f → refl)
```
