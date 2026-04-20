<!--
```agda
open import Cat.Instances.Discrete
open import Cat.Functor.Bifunctor
open import Cat.Instances.Functor
open import Cat.Morphism
open import Cat.Bi.Base
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Bi.Instances.Discrete {o ℓ} (C : Precategory o ℓ) where
```

<!--
```agda
private module C = Cat.Reasoning C
open Make-bifunctor
open Prebicategory
open Functor
```
-->

# Locally discrete bicategories {defines="locally-discrete-bicategory"}

Let $\cC$ be a precategory. We can define a prebicategory $\bf{C}$ by
letting the hom-1-categories of $\bf{C}$ be the [[discrete categories]] on
the Hom-sets of $\cC$.

```agda
private
  BHom : C.Ob → C.Ob → Precategory _ _
  BHom x y = Disc! (C.Hom x y)

  Bcompose : ∀ {x y z} → Bifunctor (BHom y z) (BHom x y) (BHom x z)
  Bcompose = make-bifunctor λ where
    .F₀ A B → A C.∘ B
    .lmap → apᵢ (C._∘ _)
    .rmap → apᵢ (_ C.∘_)
    .lmap-id    → refl
    .rmap-id    → refl
    .lmap-∘ f g → prop!
    .rmap-∘ f g → prop!
    .lrmap  f g → prop!

Locally-discrete : Prebicategory o ℓ ℓ
Locally-discrete .Ob  = C.Ob
Locally-discrete .Hom = BHom
Locally-discrete .id  = C.id
Locally-discrete .compose = Bcompose
Locally-discrete .unitor-l = to-natural-iso ni where
  ni : make-natural-iso _ _
  ni .make-natural-iso.eta x = Id≃path.from $ sym (C.idl x)
  ni .make-natural-iso.inv x = Id≃path.from $ C.idl x
  ni .make-natural-iso.eta∘inv x = prop!
  ni .make-natural-iso.inv∘eta x = prop!
  ni .make-natural-iso.natural x y f = prop!
Locally-discrete .unitor-r = to-natural-iso ni where
  ni : make-natural-iso _ _
  ni .make-natural-iso.eta x = Id≃path.from $ sym (C.idr x)
  ni .make-natural-iso.inv x = Id≃path.from $ C.idr x
  ni .make-natural-iso.eta∘inv x = prop!
  ni .make-natural-iso.inv∘eta x = prop!
  ni .make-natural-iso.natural x y f = prop!
Locally-discrete .associator = to-natural-iso ni where
  ni : make-natural-iso _ _
  ni .make-natural-iso.eta x = Id≃path.from $ sym (C.assoc _ _ _)
  ni .make-natural-iso.inv x = Id≃path.from $ C.assoc _ _ _
  ni .make-natural-iso.eta∘inv x = prop!
  ni .make-natural-iso.inv∘eta x = prop!
  ni .make-natural-iso.natural x y f = prop!
Locally-discrete .triangle f g = prop!
Locally-discrete .pentagon f g h i = prop!
```
