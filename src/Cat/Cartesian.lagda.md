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

::: {.definition #cartesian-functor alias="product-comparison-map"}
If $F : \cC \to \cD$ is a functor between [[Cartesian categories]], we
can define a **product comparison** map
$$
\left\langle F(\pi_1),\, F(\pi_2) \right\rangle
  : F(a \times b) \to F(a) \times F(b)
$$
which is an isomorphism precisely when $F$ *preserves products*, in the
coherent sense that the image under $F$ of a product diagram in $\cC$,
i.e. the span
$$
F(a) \xot{F(\pi_1)} F(a \times b) \xto{F(\pi_2)} F(b)
$$
becomes a product diagram in $\cD$. We say that $F$ is a **Cartesian
functor** if it preserves the [[terminal object]], and its product
comparison map is an isomorphism.
:::

```agda
  product-comparison : ∀ a b → D.Hom (F.₀ (a C.⊗₀ b)) (F.₀ a D.⊗₀ F.₀ b)
  product-comparison a b = D.⟨ F.₁ C.π₁ , F.₁ C.π₂ ⟩

  record Cartesian-functor : Type (o ⊔ o' ⊔ ℓ ⊔ ℓ') where
    field
      pres-products : ∀ a b → D.is-invertible (product-comparison a b)
      pres-terminal : is-terminal D (F.₀ C.top)

    image-is-product
      : ∀ {a b} → is-product D {A = F.₀ a} {B = F.₀ b} (F.₁ C.π₁) (F.₁ C.π₂)
    image-is-product = is-product-iso-apex (pres-products _ _)
      D.π₁∘⟨⟩ D.π₂∘⟨⟩ D.has-is-product
```

<!--
```agda
    module comparison {a} {b} = D.is-invertible (pres-products a b)
    module preserved  {a} {b} = is-product (image-is-product {a} {b})
```
-->

We can establish some useful algebraic properties of the *inverse* of
the comparison map, namely that composing it with the projections
$F(\pi_1)$ and $F(\pi_2)$ recovers the product projections in $\cD$.
This is a corollary of `image-is-product`{.Agda}.

```agda
    π₁inv : ∀ {a} {b} → F.₁ C.π₁ D.∘ comparison.inv {a} {b} ≡ D.π₁
    π₁inv =
      F.₁ C.π₁ D.∘ comparison.inv                       ≡⟨ ap₂ D._∘_ refl (D.intror (sym (D.⟨⟩-unique (D.idr _) (D.idr _)))) ⟩
      F.₁ C.π₁ D.∘ comparison.inv D.∘ D.⟨ D.π₁ , D.π₂ ⟩ ≡⟨ preserved.π₁∘⟨⟩ ⟩
      D.π₁                                              ∎

    π₂inv : ∀ {a} {b} → F.₁ C.π₂ D.∘ comparison.inv {a} {b} ≡ D.π₂
    π₂inv =
      F.₁ C.π₂ D.∘ comparison.inv                       ≡⟨ ap₂ D._∘_ refl (D.intror (sym (D.⟨⟩-unique (D.idr _) (D.idr _)))) ⟩
      F.₁ C.π₂ D.∘ comparison.inv D.∘ D.⟨ D.π₁ , D.π₂ ⟩ ≡⟨ preserved.π₂∘⟨⟩ ⟩
      D.π₂                                              ∎
```

Finally, we can show that, if each product comparison map is an
isomorphism, then this becomes a [[natural isomorphism]] between the two
functors $(\cC \times \cC) \to \cD$
$$
\begin{align*}
(a, b) &\mapsto F(a \times_\cC b)    \\
(a, b) &\mapsto F(a) \times_\cD F(b)
\end{align*}
$$
obtained by respectively taking a product in $\cC$ and applying $F$, and
applying $F$ and taking a product in $\cD$.

```agda
    comparison-nat : is-natural-transformation
      (D.×-functor F∘ (F F× F)) (F F∘ C.×-functor)
      λ (a , b) → comparison.inv {a} {b}

    comparison-nat (a , b) (a' , b') (f , g) = Product.unique₂
      record { has-is-product = image-is-product }
      preserved.π₁∘⟨⟩ preserved.π₂∘⟨⟩
      (F.extendl C.π₁∘⟨⟩ ∙ ap₂ D._∘_ refl π₁inv)
      (F.extendl C.π₂∘⟨⟩ ∙ ap₂ D._∘_ refl π₂inv)
```
