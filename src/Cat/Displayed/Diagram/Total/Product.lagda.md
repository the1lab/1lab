---
description: |
  Total products.
---
<!--
```agda
open import Cat.Diagram.Product
open import Cat.Displayed.Total
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Reasoning
```
-->
```agda
module Cat.Displayed.Diagram.Total.Product where
```

<!--
```agda
open Total-hom
```
-->

# Total Products

<!--
```agda
module _
  {ob ℓb oe ℓe} {B : Precategory ob ℓb}
  (E : Displayed B oe ℓe)
  where
  open Cat.Reasoning B
  open Displayed E
```
-->

:::{.definition #total-product-diagram}
Let $\cE \liesover \cB$ be a [[displayed category]], and
$P, \pi_1 : P \to A, \pi_2 : P \to B$ be a [[product diagram|product]] in $\cB$.
A diagram $P' : \cE_{P}, \pi_1' : P' \to_{\pi_1} A', \pi_2' : P' \to_{\pi_2} B'$
is a **total product diagram** if it satisfies a displayed version of the
universal property of the product.
:::


```agda
  record is-total-product
      {x y p} {x' : Ob[ x ]} {y' : Ob[ y ]} {p' : Ob[ p ]}
      {π₁ : Hom p x} {π₂ : Hom p y}
      (prod : is-product B π₁ π₂)
      (π₁' : Hom[ π₁ ] p' x') (π₂' : Hom[ π₂ ] p' y')
      : Type (ob ⊔ ℓb ⊔ oe ⊔ ℓe)
      where
      no-eta-equality
      open is-product prod
      field
        ⟨_,_⟩'
          : ∀ {a a'} {f : Hom a x} {g : Hom a y}
          → (f' : Hom[ f ] a' x') (g' : Hom[ g ] a' y')
          → Hom[ ⟨ f , g ⟩ ] a' p'
        π₁∘⟨⟩'
          : ∀ {a a'} {f : Hom a x} {g : Hom a y}
          → {f' : Hom[ f ] a' x'} {g' : Hom[ g ] a' y'}
          → π₁' ∘' ⟨ f' , g' ⟩' ≡[ π₁∘⟨⟩ ] f'
        π₂∘⟨⟩'
          : ∀ {a a'} {f : Hom a x} {g : Hom a y}
          → {f' : Hom[ f ] a' x'} {g' : Hom[ g ] a' y'}
          → π₂' ∘' ⟨ f' , g' ⟩' ≡[ π₂∘⟨⟩ ] g'
        unique'
          : ∀ {a a'} {f : Hom a x} {g : Hom a y}
          → {f' : Hom[ f ] a' x'} {g' : Hom[ g ] a' y'}
          → {other : Hom a p} {p1 : π₁ ∘ other ≡ f} {p2 : π₂ ∘ other ≡ g}
          → {other' : Hom[ other ] a' p'}
          → (p1' : (π₁' ∘' other') ≡[ p1 ] f')
          → (p2' : (π₂' ∘' other') ≡[ p2 ] g')
          → other' ≡[ unique p1 p2 ] ⟨ f' , g' ⟩'
```

:::{.definition #total-product}
A **total product** of $A'$ and $B'$ in $\cE$ consists of a choice
of a total product diagram.
:::


```agda
  record Total-product
    {x y}
    (prod : Product B x y)
    (x' : Ob[ x ]) (y' : Ob[ y ])
    : Type (ob ⊔ ℓb ⊔ oe ⊔ ℓe) where
    no-eta-equality
    open Product prod
    field
      apex' : Ob[ apex ]
      π₁' : Hom[ π₁ ] apex' x'
      π₂' : Hom[ π₂ ] apex' y'
      has-is-total-product : is-total-product has-is-product π₁' π₂'

    open is-total-product has-is-total-product
```

## Total products and total categories

<!--
```agda
module _
  {ob ℓb oe ℓe} {B : Precategory ob ℓb}
  {E : Displayed B oe ℓe}
  where
  open Cat.Reasoning B
  open Displayed E

  private module ∫E = Cat.Reasoning (∫ E)
```
-->

As the name suggests, a total product diagram in $\cE$ induces
to a product diagram in the [[total category]] of $\cE$.

```agda
  is-total-product→total-is-product
    : ∀ {x y p} {x' : Ob[ x ]} {y' : Ob[ y ]} {p' : Ob[ p ]}
    → {π₁ : ∫E.Hom (p , p') (x , x')} {π₂ : ∫E.Hom (p , p') (y , y')}
    → {prod : is-product B (π₁ .hom) (π₂ .hom)}
    → is-total-product E prod (π₁ .preserves) (π₂ .preserves)
    → is-product (∫ E) π₁ π₂
```

<details>
<summary>The proof is largely shuffling data about, so we elide the details.
</summary>
```agda
  is-total-product→total-is-product {π₁ = π₁} {π₂ = π₂} {prod = prod} total-prod = ∫prod where
    open is-product prod
    open is-total-product total-prod

    ∫prod : is-product (∫ E) π₁ π₂
    ∫prod .is-product.⟨_,_⟩ f g =
      total-hom ⟨ f .hom , g .hom ⟩ ⟨ f .preserves , g .preserves ⟩'
    ∫prod .is-product.π₁∘⟨⟩ =
      total-hom-path E π₁∘⟨⟩ π₁∘⟨⟩'
    ∫prod .is-product.π₂∘⟨⟩ =
      total-hom-path E π₂∘⟨⟩ π₂∘⟨⟩'
    ∫prod .is-product.unique p1 p2 =
      total-hom-path E
        (unique (ap hom p1) (ap hom p2))
        (unique' (ap preserves p1) (ap preserves p2))
```
</details>

::: warning
Note that a product diagram in a total category does **not** necessarily
yield a product diagram in the base category. For a counterexample, consider
the following displayed category:

\begin{tikzcd}
  \bullet \\
  \\
  \bullet
  \arrow[from=1-1, lies over, to=3-1]
  \arrow["f"', from=3-1, to=3-1, loop, in=305, out=235, distance=10mm]
\end{tikzcd}

The total category is equivalent to the [[terminal category]], and thus has
products. However, the base category does not have products, as the uniqueness
condition fails!
:::
