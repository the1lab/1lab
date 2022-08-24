```agda
open import Cat.Instances.Functor
open import Cat.Diagram.Terminal
open import Cat.Monoidal.Base
open import Cat.Prelude

import Cat.Functor.Bifunctor as Bifunctor
import Cat.Diagram.Product
import Cat.Reasoning as Cr

module Cat.Monoidal.Instances.Cartesian where
```

<!--
```agda
open _=>_
```
-->

# Cartesian monoidal categories

Unlike with [categories] and [bicategories], there is no handy example
of [monoidal category] that is as canonical as how the collection of all
$n$-categories is an $(n+1)$-category. However, we do have _a_ certain
canonical pool of examples to draw from: all the _Cartesian monoidal
categories_, also known as _finite-products categories_.

[categories]: Cat.Base.html
[bicategories]: Cat.Bi.Base.html
[monoidal category]: Cat.Monoidal.Base.html

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} where
  open Cat.Diagram.Product C
  open Monoidal-category
  open make-natural-iso
  open Cr C
```
-->

```agda
  Cartesian-monoidal : (∀ A B → Product A B) → Terminal C → Monoidal-category C
  Cartesian-monoidal prods term = mon where
    open Cartesian prods
    open Terminal term
    mon : Monoidal-category C
    mon .-⊗- = ×-functor
    mon .Unit = top
```

There's nothing much to say about this result: It's pretty much just
banging out the calculation. Our tensor product functor is the Cartesian
product functor, and the tensor unit is the terminal object (the empty
product). Associators and units are the evident maps, which are coherent
by the properties of limits. Translating this intuitive explanation to a
formal proof requires a _lot_ of calculation, however:

```agda
    mon .unitor-l = to-natural-iso ni where
      ni : make-natural-iso _ _
      ni .eta x = ⟨ ! , id ⟩
      ni .inv x = π₂
      ni .eta∘inv x = Product.unique₂ (prods _ _)
        (pulll π₁∘⟨⟩ ∙ sym (!-unique _)) (cancell π₂∘⟨⟩) (!-unique₂ _ _) (idr _)
      ni .inv∘eta x = π₂∘⟨⟩
      ni .natural x y f = Product.unique₂ (prods _ _)
        (pulll π₁∘⟨⟩ ∙ pullr π₁∘⟨⟩ ∙ idl _) (pulll π₂∘⟨⟩ ∙ cancelr π₂∘⟨⟩)
        (!-unique₂ _ _) (pulll π₂∘⟨⟩ ∙ idl f)
    mon .unitor-r = to-natural-iso ni where
      ni : make-natural-iso _ _
      ni .eta x = ⟨ id , ! ⟩
      ni .inv x = π₁
      ni .eta∘inv x = Product.unique₂ (prods _ _)
        (pulll π₁∘⟨⟩ ∙ idl _) (pulll π₂∘⟨⟩ ∙ sym (!-unique _))
        (idr _) (sym (!-unique _))
      ni .inv∘eta x = π₁∘⟨⟩
      ni .natural x y f = Product.unique₂ (prods _ _)
        (pulll π₁∘⟨⟩ ·· pullr π₁∘⟨⟩ ·· idr f)
        (pulll π₂∘⟨⟩ ·· pullr π₂∘⟨⟩ ·· idl !)
        (pulll π₁∘⟨⟩ ∙ idl f)
        (!-unique₂ _ _)
    mon .associator = to-natural-iso ni where
      ni : make-natural-iso _ _
      ni .eta x = ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
      ni .inv x = ⟨ ⟨ π₁ , π₁ ∘ π₂ ⟩ , π₂ ∘ π₂ ⟩
      ni .eta∘inv x = Product.unique₂ (prods _ _)
        (pulll π₁∘⟨⟩ ·· pullr π₁∘⟨⟩ ·· π₁∘⟨⟩)
        (pulll π₂∘⟨⟩ ∙ Product.unique₂ (prods _ _)
          (pulll π₁∘⟨⟩ ·· pullr π₁∘⟨⟩ ·· π₂∘⟨⟩)
          (pulll π₂∘⟨⟩ ∙ π₂∘⟨⟩)
          refl refl)
        (idr _) (idr _)
      ni .inv∘eta x = Product.unique₂ (prods _ _)
        (pulll π₁∘⟨⟩ ∙ Product.unique₂ (prods _ _)
          (pulll π₁∘⟨⟩ ∙ π₁∘⟨⟩)
          (pulll π₂∘⟨⟩ ·· pullr π₂∘⟨⟩ ·· π₁∘⟨⟩) refl refl)
        (pulll π₂∘⟨⟩ ·· pullr π₂∘⟨⟩ ·· π₂∘⟨⟩)
        (idr _) (idr _)
      ni .natural x y f = Product.unique₂ (prods _ _)
        (pulll π₁∘⟨⟩ ∙ pullr π₁∘⟨⟩)
        (pulll π₂∘⟨⟩ ∙ Product.unique (prods _ _) _
          (pulll (pulll π₁∘⟨⟩) ·· pullr π₂∘⟨⟩ ·· pullr π₁∘⟨⟩)
          (pulll (pulll π₂∘⟨⟩) ·· pullr π₂∘⟨⟩ ·· pullr π₂∘⟨⟩))
        (pulll π₁∘⟨⟩ ·· pullr π₁∘⟨⟩ ·· extendl π₁∘⟨⟩)
        (pulll π₂∘⟨⟩ ∙ Product.unique (prods _ _) _
          (pulll π₁∘⟨⟩ ·· pullr π₁∘⟨⟩ ·· extendl π₂∘⟨⟩)
          (pulll π₂∘⟨⟩ ∙ π₂∘⟨⟩))
    mon .triangle = Product.unique (prods _ _) _
      (pulll π₁∘⟨⟩ ·· pullr π₁∘⟨⟩ ·· π₁∘⟨⟩ ∙ introl refl)
      (pulll π₂∘⟨⟩ ·· pullr π₂∘⟨⟩ ·· idl _)
    mon .pentagon = Product.unique₂ (prods _ _)
      (pulll π₁∘⟨⟩ ∙ pullr (pulll π₁∘⟨⟩))
      (pulll π₂∘⟨⟩ ∙ pullr (pulll π₂∘⟨⟩ ·· pullr π₂∘⟨⟩ ·· pulll π₂∘⟨⟩) ∙ idl _)
      (pulll π₁∘⟨⟩ ∙ Product.unique₂ (prods _ _)
        (pulll π₁∘⟨⟩ ∙ π₁∘⟨⟩)
        (pulll π₂∘⟨⟩ ∙ pullr π₂∘⟨⟩)
        (pulll π₁∘⟨⟩ ∙ Product.unique (prods _ _) _
          (pulll π₁∘⟨⟩ ·· pulll π₁∘⟨⟩ ·· π₁∘⟨⟩ ∙ eliml refl)
          ( pulll π₂∘⟨⟩ ∙ pullr (pulll π₂∘⟨⟩ ·· pullr π₂∘⟨⟩ ·· pulll π₁∘⟨⟩)
          ∙ pulll π₁∘⟨⟩))
        (pulll π₂∘⟨⟩ ·· pulll (pullr π₂∘⟨⟩) ·· pullr (pullr π₂∘⟨⟩ ∙ pulll π₁∘⟨⟩)
        ∙ extendl π₂∘⟨⟩))
      (pulll π₂∘⟨⟩ ∙ pullr π₂∘⟨⟩ ∙ assoc _ _ _)
```
