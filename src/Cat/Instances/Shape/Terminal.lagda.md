<!--
```agda
open import 1Lab.Prelude

open import Cat.Functor.Naturality
open import Cat.Functor.Compose
open import Cat.Functor.Base
open import Cat.Groupoid
open import Cat.Morphism
open import Cat.Base

import Cat.Reasoning
```
-->

```agda
module Cat.Instances.Shape.Terminal where
```

<!--
```agda
open Precategory
```
-->

:::{.definition #terminal-category}
The **terminal category** is the category with a single object, and only
trivial morphisms.
:::

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
```

The ony morphism in the terminal category is the identity, so the
terminal category is a [[pregroupoid]].

```agda
⊤Cat-is-pregroupoid : is-pregroupoid ⊤Cat
⊤Cat-is-pregroupoid _ = id-invertible ⊤Cat
```

<!--
```agda
module _ {o h} {C : Precategory o h} where
  private module C = Cat.Reasoning C
  open Functor
  open _=>_
```
-->

There is a unique functor from any category $\cC$ into the terminal
category.

```agda
  !F : Functor C ⊤Cat
  !F .F₀ _ = tt
  !F .F₁ _ = tt
  !F .F-id = refl
  !F .F-∘ _ _ = refl

  !F-unique : ∀ {F : Functor C ⊤Cat} → F ≡ !F
  !F-unique = Functor-path (λ _ → refl) (λ _ → refl)
```

Conversely, functors $\top \to \cC$ are determined by their behaviour
on a single object.

```agda
  !Const : C.Ob → Functor ⊤Cat C
  !Const c .F₀ _ = c
  !Const c .F₁ _ = C.id
  !Const c .F-id = refl
  !Const c .F-∘ _ _ = sym (C.idl _)

  !Const-η : ∀ (F G : Functor ⊤Cat C) → F .F₀ tt ≡ G .F₀ tt → F ≡ G
  !Const-η F G p =
    Functor-path
      (λ _ → p)
      (λ _ i → hcomp (∂ i) λ where
        j (i = i0) → F .F-id (~ j)
        j (i = i1) → G .F-id (~ j)
        j (j = i0) → C.id)
```

Natural isomorphisms between functors $\top \to \cC$
correspond to isomorphisms in $\cC$.

```agda
  !constⁿ
    : ∀ {F G : Functor ⊤Cat C}
    → C.Hom (F .F₀ tt) (G .F₀ tt)
    → F => G
  !constⁿ {F = F} {G = G} f .η _ = f
  !constⁿ {F = F} {G = G} f .is-natural _ _ _ =
    C.elimr (F .F-id) ∙ C.introl (G .F-id)

  !const-isoⁿ
    : ∀ {F G : Functor ⊤Cat C}
    → F .F₀ tt C.≅ G .F₀ tt
    → F ≅ⁿ G
  !const-isoⁿ {F = F} {G = G} f =
    iso→isoⁿ (λ _ → f) (λ _ → C.eliml (G .F-id) ∙ C.intror (F .F-id))
```
