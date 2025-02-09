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

  private variable
    a x y p : Ob
    a' x' y' p' : Ob[ a ]
    f g other : Hom a x
    f' g' : Hom[ f ] a' x'
```
-->

:::{.definition #total-product-diagram}
Let $\cE \liesover \cB$ be a [[displayed category]], and
$P, \pi_1 : P \to X, \pi_2 : P \to Y$ be a [[product diagram|product]] in $\cB$.
A diagram $P', \pi_{1}', \pi_{2}'$ of the shape

~~~{.quiver}
\begin{tikzcd}
  {P'} && {Y'} \\
  & {X'} \\
  P && Y \\
  & X
  \arrow["{\pi_2'}"{description, pos=0.4}, from=1-1, to=1-3]
  \arrow["{\pi_1'}"{description}, from=1-1, to=2-2]
  \arrow[from=1-1, lies over, to=3-1]
  \arrow[from=1-3, lies over, to=3-3]
  \arrow[from=2-2, lies over, to=4-2]
  \arrow["{\pi_2}"{description, pos=0.3}, from=3-1, to=3-3]
  \arrow["{\pi_1}"{description}, from=3-1, to=4-2]
\end{tikzcd}
~~~

is a **total product diagram** if it satisfies a displayed version of the
universal property of the product.


```agda
  record is-total-product
      {π₁ : Hom p x} {π₂ : Hom p y}
      (prod : is-product B π₁ π₂)
      (π₁' : Hom[ π₁ ] p' x') (π₂' : Hom[ π₂ ] p' y')
      : Type (ob ⊔ ℓb ⊔ oe ⊔ ℓe)
      where
      no-eta-equality
      open is-product prod
```

More explicitly, suppose that we had a triple $(A', f', g')$ displayed
over $(A, f, g)$, as in the following diagram.

~~~{.quiver}
\begin{tikzcd}
  \textcolor{rgb,255:red,92;green,92;blue,214}{{A'}} \\
  && {P'} && {Y'} \\
  \textcolor{rgb,255:red,92;green,92;blue,214}{A} &&& {X'} \\
  && P && Y \\
  &&& X
  \arrow["{g'}", color={rgb,255:red,92;green,92;blue,214}, curve={height=-12pt}, from=1-1, to=2-5]
  \arrow[color={rgb,255:red,92;green,92;blue,214}, lies over, from=1-1, to=3-1]
  \arrow["{f'}"{description}, color={rgb,255:red,92;green,92;blue,214}, curve={height=18pt}, from=1-1, to=3-4]
  \arrow["{\pi_2'}"{description, pos=0.4}, from=2-3, to=2-5]
  \arrow["{\pi_1'}"{description}, from=2-3, to=3-4]
  \arrow[from=2-3, lies over, to=4-3]
  \arrow[from=2-5, lies over, to=4-5]
  \arrow["g"{description, pos=0.3}, color={rgb,255:red,92;green,92;blue,214}, curve={height=-12pt}, from=3-1, to=4-5]
  \arrow["f"{description}, color={rgb,255:red,92;green,92;blue,214}, curve={height=18pt}, from=3-1, to=5-4]
  \arrow[from=3-4, lies over, to=5-4]
  \arrow["{\pi_2}"{description, pos=0.3}, from=4-3, to=4-5]
  \arrow["{\pi_1}"{description}, from=4-3, to=5-4]
\end{tikzcd}
~~~

$P$ is a product, so there exists a unique $\langle f, g \rangle : A \to P$
that commutes with $\pi_1$ and $\pi_2$.

~~~{.quiver}
\begin{tikzcd}
  \textcolor{rgb,255:red,92;green,92;blue,214}{{A'}} \\
  && {P'} && {Y'} \\
  \textcolor{rgb,255:red,92;green,92;blue,214}{A} &&& {X'} \\
  && P && Y \\
  &&& X
  \arrow["{g'}", color={rgb,255:red,92;green,92;blue,214}, curve={height=-12pt}, from=1-1, to=2-5]
  \arrow[color={rgb,255:red,92;green,92;blue,214}, lies over, from=1-1, to=3-1]
  \arrow["{f'}"{description}, color={rgb,255:red,92;green,92;blue,214}, curve={height=18pt}, from=1-1, to=3-4]
  \arrow["{\pi_2'}"{description, pos=0.4}, from=2-3, to=2-5]
  \arrow["{\pi_1'}"{description}, from=2-3, to=3-4]
  \arrow[from=2-3, lies over, to=4-3]
  \arrow[from=2-5, lies over, to=4-5]
  \arrow["{\langle f,g \rangle}"{description}, color={rgb,255:red,214;green,92;blue,92}, from=3-1, to=4-3]
  \arrow["g"{description, pos=0.3}, color={rgb,255:red,92;green,92;blue,214}, curve={height=-12pt}, from=3-1, to=4-5]
  \arrow["f"{description}, color={rgb,255:red,92;green,92;blue,214}, curve={height=18pt}, from=3-1, to=5-4]
  \arrow[from=3-4, lies over, to=5-4]
  \arrow["{\pi_2}"{description, pos=0.3}, from=4-3, to=4-5]
  \arrow["{\pi_1}"{description}, from=4-3, to=5-4]
\end{tikzcd}
~~~

This leaves a conspicuous gap in the upstairs portion of the diagram between
$A'$ and $P'$; $(P', \pi_1', \pi_2')$ is a total product precisely when we
have a unique lift of $\langle f, g \rangle$ that commutes with $\pi_1'$
and $\pi_2'$.


```agda
      field
        ⟨_,_⟩'
          : (f' : Hom[ f ] a' x') (g' : Hom[ g ] a' y')
          → Hom[ ⟨ f , g ⟩ ] a' p'
        π₁∘⟨⟩'
          : π₁' ∘' ⟨ f' , g' ⟩' ≡[ π₁∘⟨⟩ ] f'
        π₂∘⟨⟩'
          : π₂' ∘' ⟨ f' , g' ⟩' ≡[ π₂∘⟨⟩ ] g'
        unique'
          : {p1 : π₁ ∘ other ≡ f} {p2 : π₂ ∘ other ≡ g}
          → {other' : Hom[ other ] a' p'}
          → (p1' : (π₁' ∘' other') ≡[ p1 ] f')
          → (p2' : (π₂' ∘' other') ≡[ p2 ] g')
          → other' ≡[ unique p1 p2 ] ⟨ f' , g' ⟩'
```
:::

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

~~~{.quiver}
\begin{tikzcd}
  \bullet \\
  \\
  \bullet
  \arrow[from=1-1, lies over, to=3-1]
  \arrow["f"', from=3-1, to=3-1, loop, in=305, out=235, distance=10mm]
\end{tikzcd}
~~~

The total category is equivalent to the [[terminal category]], and thus has
products. However, the base category does not have products, as the uniqueness
condition fails!
:::
