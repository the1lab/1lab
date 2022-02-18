```agda
open import 1Lab.Prelude

open import Cat.Base

module Cat.Instances.Terminal where
```

<!--
```agda
open Precategory
```
-->

The **terminal category** is the category with a single object, and only
trivial morphisms.

```agda
⊤Cat : Precategory lzero lzero
⊤Cat .Ob = ⊤
⊤Cat .Hom _ _ = ⊤
⊤Cat .Hom-set _ _ _ _ _ _ _ _ = tt
⊤Cat .Precategory.id = tt
⊤Cat .Precategory._∘_ _ _ = tt
⊤Cat .idr _ _ = tt
⊤Cat .idl _ _ = tt
⊤Cat .assoc _ _ _ _ = tt

module _ {o h} {A : Precategory o h} where
  private module A = Precategory A
  open Functor

  const! : Ob A → Functor ⊤Cat A
  const! x .F₀ _ = x
  const! x .F₁ _ = A.id
  const! x .F-id = refl
  const! x .F-∘ _ _ = sym (A.idl _)
```
