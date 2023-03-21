```agda
open import Cat.Diagram.Product
open import Cat.Prelude

import Cat.Reasoning
import Cat.Functor.Reasoning as Func

module Cat.Diagram.Product.Functor where
```

# Product Preserving Functors

A functor $F : \cC \to \cD$ **preserves products** if, for every product
$B \leftarrow X \rightarrow B$ in $\cC$, the corresponding diagram in
$\cD$ is also a product.

<!--
```agda
module _ {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'} where
  private
    module C = Cat.Reasoning C
    module D = Cat.Reasoning D
    open Functor
    open is-product
```
-->

```agda
  preserves-products : Functor C D → Type _
  preserves-products F =
    ∀ {x a b} {p1 : C.Hom x a} {p2 : C.Hom x b}
    → is-product C p1 p2 → is-product D (F .F₁ p1) (F .F₁ p2)
```

# Preservation of chosen products

Let $F : \cC \to \cD$ be a functor, and let $\cC$ and $\cD$ be equipped
with a choice of products. If we wish to show that $F$ preserves
products, then it suffices to show that $F$ takes chosen products in
$\cC$ to chosen products in $\cD$.

```agda
  module _ (C-prod : has-products C) (D-prod : has-products D) (F : Functor C D) where
    private
      module C-prod = Binary-products C C-prod
      module D-prod = Binary-products D D-prod
```

First, note that there is a canonical morphism
$F (X \times Y) \to F X \times F Y$, defined using the universal property
of the product.

```agda
    into-product : ∀ a b → D.Hom (F .F₀ (a C-prod.⊗₀ b)) (F .F₀ a D-prod.⊗₀ F .F₀ b)
    into-product _ _ =  D-prod.⟨ F .F₁ C-prod.π₁ , F .F₁ C-prod.π₂ ⟩
```

If this canonical morphism is invertible, and the inverse commutes with
projections, then $F$ preserves products.

```agda
    preserves-chosen-products→preserves-products
      : (invert : ∀ a b → D.is-invertible (into-product a b))
      → (∀ {a b} (open D.is-invertible (invert a b))
         → F .F₁ C-prod.π₁ D.∘ inv ≡ D-prod.π₁)
      → (∀ {a b} (open D.is-invertible (invert a b))
         → F .F₁ C-prod.π₂ D.∘ inv ≡ D-prod.π₂)
      → preserves-products F
```

<details>
<summary>The proof of this fact is unenlightening, so we opt to omit it.
</summary>

```agda
    preserves-chosen-products→preserves-products apex-iso π₁-comm π₂-comm {x} {a} {b} {p1} {p2} p =
      preserved where
      module C-product-iso p = C._≅_ (C-prod.product-iso p)
      module apex-iso {a} {b} = D.is-invertible (apex-iso a b)
      module p = is-product p

      product-iso-to-path : F .F₁ (C-product-iso.to p) ≡ apex-iso.inv D.∘ D-prod.⟨ F .F₁ p1 , F .F₁ p2 ⟩
      product-iso-to-path =
        D.introl apex-iso.invr
        ·· D.pullr (D-prod.⟨⟩∘ _)
        ·· ap₂ D._∘_ refl
            (ap₂ D-prod.⟨_,_⟩
              (Func.collapse F C-prod.π₁∘⟨⟩)
              (Func.collapse F C-prod.π₂∘⟨⟩))

      preserved : is-product D (F .F₁ p1) (F .F₁ p2)
      preserved .⟨_,_⟩ f g =
        F .F₁ (C-product-iso.from p) D.∘ apex-iso.inv D.∘ D-prod.⟨ f , g ⟩
      preserved .π₁∘factor {z} {f} {g} =
        F .F₁ p1 D.∘ (F .F₁ (C-product-iso.from p) D.∘ apex-iso.inv D.∘ D-prod.⟨ f , g ⟩) ≡⟨ Func.pulll F p.π₁∘factor ⟩
        (F .F₁ C-prod.π₁ D.∘ apex-iso.inv D.∘ D-prod.⟨ f , g ⟩)                           ≡⟨ D.pulll π₁-comm ⟩
        (D-prod.π₁ D.∘ D-prod.⟨ f , g ⟩)                                                  ≡⟨ D-prod.π₁∘⟨⟩ ⟩
        f                                                                                 ∎
      preserved .π₂∘factor {z} {f} {g} =
        F .F₁ p2 D.∘ (F .F₁ (C-product-iso.from p) D.∘ apex-iso.inv D.∘ D-prod.⟨ f , g ⟩) ≡⟨ Func.pulll F p.π₂∘factor ⟩
        (F .F₁ C-prod.π₂ D.∘ apex-iso.inv D.∘ D-prod.⟨ f , g ⟩)                           ≡⟨ D.pulll π₂-comm ⟩
        (D-prod.π₂ D.∘ D-prod.⟨ f , g ⟩)                                                  ≡⟨ D-prod.π₂∘⟨⟩ ⟩
        g                                                                                 ∎
      preserved .unique {p1 = p1'} {p2 = p2'} other q r =
        other                                                                                                      ≡⟨ D.insertl (Func.annihilate F (C-product-iso.invr p)) ⟩
        (F .F₁ (C-product-iso.from p) D.∘ F .F₁ (C-product-iso.to p) D.∘ other)                                    ≡⟨ ap₂ D._∘_ refl (D.pushl product-iso-to-path) ⟩
        (F .F₁ (C-product-iso.from p) D.∘ apex-iso.inv D.∘ ⌜ D-prod.⟨ F .F₁ p1 , F .F₁ p2 ⟩ D.∘ other ⌝)           ≡⟨ ap! (D-prod.⟨⟩∘ other) ⟩
        (F .F₁ (C-product-iso.from p) D.∘ apex-iso.inv D.∘ ⌜ D-prod.⟨ F .F₁ p1 D.∘ other , F .F₁ p2 D.∘ other ⟩ ⌝) ≡⟨ ap! (ap₂ D-prod.⟨_,_⟩ q r) ⟩
        F .F₁ (C-product-iso.from p) D.∘ apex-iso.inv D.∘ D-prod.⟨ p1' , p2' ⟩                                     ∎
```
</details>
