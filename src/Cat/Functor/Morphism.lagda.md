<!--
```agda
open import 1Lab.Prelude hiding (id; _∘_)
open import Cat.Base

import Cat.Reasoning
```
-->

```agda
module Cat.Functor.Morphism
  {oc ℓc od ℓd}
  {C : Precategory oc ℓc} {D : Precategory od ℓd}
  (F : Functor C D)
  where
```

<!--
```agda
private
  module C = Cat.Reasoning C
  module D = Cat.Reasoning D
open Functor F public

private variable
  x y z : C.Ob
  f g h : C.Hom x y
```
-->

# Functors and Morphisms

```agda
F-inverses : C.Inverses f g → D.Inverses (F₁ f) (F₁ g)
F-inverses inv = record
  { invl = sym (F-∘ _ _) ∙ ap F₁ inv.invl ∙ F-id
  ; invr = sym (F-∘ _ _) ∙ ap F₁ inv.invr ∙ F-id
  }
  where module inv = C.Inverses inv

F-invertible : C.is-invertible f → D.is-invertible (F₁ f)
F-invertible inv = record
  { inv = F₁ inv.inv
  ; inverses = F-inverses inv.inverses
  }
  where module inv = C.is-invertible inv

F-≅ : ∀ {x y} → x C.≅ y → F₀ x D.≅ F₀ y
F-≅ f = record
  { to = F₁ f.to
  ; from = F₁ f.from
  ; inverses = F-inverses f.inverses
  }
  where module f = C._≅_ f
```
