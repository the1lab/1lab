<!--
```agda
open import Cat.Instances.Product
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Prelude

import Cat.Functor.Reasoning
import Cat.Reasoning
```
-->

```agda
module Cat.Cartesian where
```

# Cartesian categories

::: {.definition #cartesian-category}
A **Cartesian category** is one that admits all binary [[products]] and
a [[terminal object]], hence all finite products.
:::

```agda
record Cartesian-category {o ℓ} (C : Precategory o ℓ) : Type (o ⊔ ℓ) where
  field
    products : has-products C
    terminal : Terminal C
```

<!--
```agda
  open Cat.Reasoning   C          public
  open Binary-products C products public
  open Terminal          terminal public
```
-->

<!--
```agda
module
  _ {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'}
    (F : Functor C D) (ccart : Cartesian-category C) (dcart : Cartesian-category D)
  where

  private
    module F = Cat.Functor.Reasoning F
    module C = Cartesian-category ccart
    module D = Cartesian-category dcart
```
-->

If $F : \cC \to \cD$ is a functor between Cartesian categories, we can
define a **product comparison** map $F(a \times b) \to F(a) \times
F(b)$. This map is an isomorphism precisely when $F$ preserves products
in the sense that $F$ takes product diagrams to product diagrams. We say
that $F$ is a **Cartesian functor** if it preserves the terminal object
and its product comparison map is an isomorphism.

```agda
  product-comparison : ∀ a b → D.Hom (F.₀ (a C.⊗₀ b)) (F.₀ a D.⊗₀ F.₀ b)
  product-comparison a b = D.⟨ F.₁ C.π₁ , F.₁ C.π₂ ⟩

  record Cartesian-functor : Type (o ⊔ o' ⊔ ℓ ⊔ ℓ') where
    field
      ×-comparison-is-iso : ∀ a b → D.is-invertible (product-comparison a b)
      pres-terminal       : is-terminal D (F.₀ C.top)

    pres-product : ∀ {a b} → is-product D {A = F.₀ a} {B = F.₀ b} (F.₁ C.π₁) (F.₁ C.π₂)
    pres-product = is-product-iso-apex (×-comparison-is-iso _ _)
      D.π₁∘⟨⟩ D.π₂∘⟨⟩ D.has-is-product
```

<!--
```agda
    module comparison {a} {b} = D.is-invertible (×-comparison-is-iso a b)
    module preserved  {a} {b} = is-product (pres-product {a} {b})

    π₁inv : ∀ {a} {b} → F.₁ C.π₁ D.∘ comparison.inv {a} {b} ≡ D.π₁
    π₁inv = D.invertible→epic (×-comparison-is-iso _ _) _ _ (D.cancelr comparison.invr ∙ sym D.π₁∘⟨⟩)

    π₂inv : ∀ {a} {b} → F.₁ C.π₂ D.∘ comparison.inv {a} {b} ≡ D.π₂
    π₂inv = D.invertible→epic (×-comparison-is-iso _ _) _ _ (D.cancelr comparison.invr ∙ sym D.π₂∘⟨⟩)

    comparison-nat
      : is-natural-transformation (D.×-functor F∘ (F F× F)) (F F∘ C.×-functor) λ (a , b) → comparison.inv {a} {b}
    comparison-nat (a , b) (a' , b') (f , g) = Product.unique₂
      record { has-is-product = pres-product }
      preserved.π₁∘⟨⟩ preserved.π₂∘⟨⟩
      (F.extendl C.π₁∘⟨⟩ ∙ ap₂ D._∘_ refl π₁inv)
      (F.extendl C.π₂∘⟨⟩ ∙ ap₂ D._∘_ refl π₂inv)
```
-->
