<!--
```agda
open import Cat.Instances.Product
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Diagram.Product where
```

<!--
```agda
module _ {o ℓ} (C : Precategory o ℓ) where
  open Cat.Reasoning C
```
-->

# Products

:::{.definition #product}
The **product** $P$ of two objects $A$ and $B$, if it exists, is the
smallest object equipped with "projection" maps $P \to A$ and $P \to B$.
This situation can be visualised by putting the data of a product into a
commutative diagram, as the one below: To express that $P$ is the
_smallest_ object with projections to $A$ and $B$, we ask that any other
object $Q$ with projections through $A$ and $B$ factors uniquely through
$P$:
:::

~~~{.quiver}
\[\begin{tikzcd}
  & Q \\
  A & P & B
  \arrow[from=2-2, to=2-1]
  \arrow[from=2-2, to=2-3]
  \arrow[from=1-2, to=2-1]
  \arrow["{\exists!}"', dashed, from=1-2, to=2-2]
  \arrow[from=1-2, to=2-3]
\end{tikzcd}\]
~~~

In the sense that [[(univalent) categories|univalent category]]
generalise posets, the product of $A$ and $B$ --- if it exists ---
generalises the binary meet $A \wedge B$. Since products are
[unique](#uniqueness) when they exist, we may safely denote any product
of $A$ and $B$ by $A \times B$.

For a diagram $A \ot A \times B \to B$ to be a product diagram, it must
be able to cough up an arrow $Q \to P$ given the data of another span $A
\ot Q \to B$, which must not only fit into the diagram above but be
unique among the arrows that do so.

This factoring is called the **pairing** of the arrows $f : Q \to A$ and
$g : Q \to B$, since in the special case where $Q$ is the [[terminal
object]] (hence the two arrows are global elements of $A$ resp. $B$),
the pairing $\langle f, g \rangle$ is a global element of the product $A
\times B$.

[terminal object]: Cat.Diagram.Terminal.html

```agda
  record is-product {A B P} (π₁ : Hom P A) (π₂ : Hom P B) : Type (o ⊔ ℓ) where
    field
      ⟨_,_⟩     : ∀ {Q} (p1 : Hom Q A) (p2 : Hom Q B) → Hom Q P
      π₁∘factor : ∀ {Q} {p1 : Hom Q _} {p2} → π₁ ∘ ⟨ p1 , p2 ⟩ ≡ p1
      π₂∘factor : ∀ {Q} {p1 : Hom Q _} {p2} → π₂ ∘ ⟨ p1 , p2 ⟩ ≡ p2

      unique : ∀ {Q} {p1 : Hom Q A} {p2}
             → (other : Hom Q P)
             → π₁ ∘ other ≡ p1
             → π₂ ∘ other ≡ p2
             → other ≡ ⟨ p1 , p2 ⟩

    unique₂ : ∀ {Q} {pr1 : Hom Q A} {pr2}
            → ∀ {o1} (p1 : π₁ ∘ o1 ≡ pr1) (q1 : π₂ ∘ o1 ≡ pr2)
            → ∀ {o2} (p2 : π₁ ∘ o2 ≡ pr1) (q2 : π₂ ∘ o2 ≡ pr2)
            → o1 ≡ o2
    unique₂ p1 q1 p2 q2 = unique _ p1 q1 ∙ sym (unique _ p2 q2)

    ⟨⟩∘ : ∀ {Q R} {p1 : Hom Q A} {p2 : Hom Q B} (f : Hom R Q)
        → ⟨ p1 , p2 ⟩ ∘ f ≡ ⟨ p1 ∘ f , p2 ∘ f ⟩
    ⟨⟩∘ f = unique _ (pulll π₁∘factor) (pulll π₂∘factor)

    ⟨⟩-η : ⟨ π₁ , π₂ ⟩ ≡ id
    ⟨⟩-η = sym $ unique id (idr _) (idr _)
```

A product of $A$ and $B$ is an explicit choice of product diagram:

```agda
  record Product (A B : Ob) : Type (o ⊔ ℓ) where
    no-eta-equality
    field
      apex : Ob
      π₁ : Hom apex A
      π₂ : Hom apex B
      has-is-product : is-product π₁ π₂

    open is-product has-is-product public
```

## Uniqueness {defines="uniqueness-of-products"}

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} where
  open Cat.Reasoning C
  open Product hiding (⟨_,_⟩ ; π₁ ; π₂ ; ⟨⟩∘)
  private variable
    A B a b c d : Ob
```
-->

Products, when they exist, are unique. It's easiest to see this with a
diagrammatic argument: If we have product diagrams $A \ot P \to B$ and
$A \ot P' \to B$, we can fit them into a "commutative diamond" like the
one below:

~~~{.quiver}
\[\begin{tikzcd}
  & P \\
  A && B \\
  & {P'}
  \arrow[from=3-2, to=2-3]
  \arrow[from=1-2, to=2-3]
  \arrow[from=1-2, to=2-1]
  \arrow[from=3-2, to=2-1]
\end{tikzcd}\]
~~~

Since both $P$ and $P'$ are products, we know that the dashed arrows in
the diagram below exist, so the overall diagram commutes: hence we have
an isomorphism $P \cong P'$.

~~~{.quiver}
\[\begin{tikzcd}
  & P \\
  A && B \\
  & {P'}
  \arrow[from=3-2, to=2-3]
  \arrow[from=1-2, to=2-3]
  \arrow[from=1-2, to=2-1]
  \arrow[from=3-2, to=2-1]
  \arrow["{\exists!}"', shift right=1, dashed, from=1-2, to=3-2]
  \arrow["{\exists!}"', shift right=1, dashed, from=3-2, to=1-2]
\end{tikzcd}\]
~~~

We construct the map $P \to P'$ as the pairing of the projections from
$P$, and symmetrically for $P' \to P$.

```agda
  ×-Unique : (p1 p2 : Product C A B) → apex p1 ≅ apex p2
  ×-Unique p1 p2 = make-iso p1→p2 p2→p1 p1→p2→p1 p2→p1→p2
    where
      module p1 = Product p1
      module p2 = Product p2

      p1→p2 : Hom (apex p1) (apex p2)
      p1→p2 = p2.⟨ p1.π₁ , p1.π₂ ⟩

      p2→p1 : Hom (apex p2) (apex p1)
      p2→p1 = p1.⟨ p2.π₁ , p2.π₂ ⟩
```

These are unique because they are maps into products which commute with
the projections.

```agda
      p1→p2→p1 : p1→p2 ∘ p2→p1 ≡ id
      p1→p2→p1 =
        p2.unique₂
          (assoc _ _ _ ·· ap (_∘ _) p2.π₁∘factor ·· p1.π₁∘factor)
          (assoc _ _ _ ·· ap (_∘ _) p2.π₂∘factor ·· p1.π₂∘factor)
          (idr _) (idr _)

      p2→p1→p2 : p2→p1 ∘ p1→p2 ≡ id
      p2→p1→p2 =
        p1.unique₂
          (assoc _ _ _ ·· ap (_∘ _) p1.π₁∘factor ·· p2.π₁∘factor)
          (assoc _ _ _ ·· ap (_∘ _) p1.π₂∘factor ·· p2.π₂∘factor)
          (idr _) (idr _)

  is-product-iso
    : ∀ {A A' B B' P} {π₁ : Hom P A} {π₂ : Hom P B}
        {f : Hom A A'} {g : Hom B B'}
    → is-invertible f
    → is-invertible g
    → is-product C π₁ π₂
    → is-product C (f ∘ π₁) (g ∘ π₂)
  is-product-iso f-iso g-iso prod = prod' where
    module fi = is-invertible f-iso
    module gi = is-invertible g-iso

    open is-product
    prod' : is-product _ _ _
    prod' .⟨_,_⟩ qa qb = prod .⟨_,_⟩ (fi.inv ∘ qa) (gi.inv ∘ qb)
    prod' .π₁∘factor = pullr (prod .π₁∘factor) ∙ cancell fi.invl
    prod' .π₂∘factor = pullr (prod .π₂∘factor) ∙ cancell gi.invl
    prod' .unique other p q = prod .unique other
      (sym (ap (_ ∘_) (sym p) ∙ pulll (cancell fi.invr)))
      (sym (ap (_ ∘_) (sym q) ∙ pulll (cancell gi.invr)))
```

# Categories with all binary products

Categories with all binary products are quite common, so we define
a module for working with them.

```agda
has-products : ∀ {o ℓ} → Precategory o ℓ → Type _
has-products C = ∀ a b → Product C a b

module Binary-products
  {o ℓ}
  (C : Precategory o ℓ)
  (all-products : has-products C)
  where
  open Cat.Reasoning C
  private variable
    A B a b c d : Ob

  module product {a} {b} = Product (all-products a b)

  open product renaming
    (unique to ⟨⟩-unique; π₁∘factor to π₁∘⟨⟩; π₂∘factor to π₂∘⟨⟩) public
  open Functor

  infixr 7 _⊗₀_
  infix 50 _⊗₁_
```

We start by defining a "global" product-assigning operation.

```agda
  _⊗₀_ : Ob → Ob → Ob
  a ⊗₀ b = product.apex {a} {b}
```

This operation extends to a bifunctor $\cC \times \cC \to \cC$.

```agda
  _⊗₁_ : ∀ {a b x y} → Hom a x → Hom b y → Hom (a ⊗₀ b) (x ⊗₀ y)
  f ⊗₁ g = ⟨ f ∘ π₁ , g ∘ π₂ ⟩


  ×-functor : Functor (C ×ᶜ C) C
  ×-functor .F₀ (a , b) = a ⊗₀ b
  ×-functor .F₁ (f , g) = f ⊗₁ g
  ×-functor .F-id = sym $ ⟨⟩-unique id id-comm id-comm
  ×-functor .F-∘ (f , g) (h , i) =
    sym $ ⟨⟩-unique (f ⊗₁ g ∘ h ⊗₁ i)
      (pulll π₁∘⟨⟩ ∙ extendr π₁∘⟨⟩)
      (pulll π₂∘⟨⟩ ∙ extendr π₂∘⟨⟩)
```

We also define a handful of common morphisms.

```agda
  δ : Hom a (a ⊗₀ a)
  δ = ⟨ id , id ⟩

  swap : Hom (a ⊗₀ b) (b ⊗₀ a)
  swap = ⟨ π₂ , π₁ ⟩
```

<!--
```agda
  swap-is-iso : ∀ {a b} → is-invertible (swap {a} {b})
  swap-is-iso = make-invertible swap
    (unique₂ (pulll π₁∘⟨⟩ ∙ π₂∘⟨⟩) ((pulll π₂∘⟨⟩ ∙ π₁∘⟨⟩)) (idr _) (idr _))
    (unique₂ (pulll π₁∘⟨⟩ ∙ π₂∘⟨⟩) ((pulll π₂∘⟨⟩ ∙ π₁∘⟨⟩)) (idr _) (idr _))

  by-π₁ : ∀ {f f' : Hom a b} {g g' : Hom a c} → ⟨ f , g ⟩ ≡ ⟨ f' , g' ⟩ → f ≡ f'
  by-π₁ p = sym π₁∘⟨⟩ ∙ ap (π₁ ∘_) p ∙ π₁∘⟨⟩

  extend-π₁ : ∀ {f : Hom a b} {g : Hom a c} {h} → ⟨ f , g ⟩ ≡ h → f ≡ π₁ ∘ h
  extend-π₁ p = sym π₁∘⟨⟩ ∙ ap (π₁ ∘_) p

  by-π₂ : ∀ {f f' : Hom a b} {g g' : Hom a c} → ⟨ f , g ⟩ ≡ ⟨ f' , g' ⟩ → g ≡ g'
  by-π₂ p = sym π₂∘⟨⟩ ∙ ap (π₂ ∘_) p ∙ π₂∘⟨⟩

  extend-π₂ : ∀ {f : Hom a b} {g : Hom a c} {h} → ⟨ f , g ⟩ ≡ h → g ≡ π₂ ∘ h
  extend-π₂ p = sym π₂∘⟨⟩ ∙ ap (π₂ ∘_) p

  π₁-inv
    : ∀ {f : Hom (a ⊗₀ b) c} {g : Hom (a ⊗₀ b) d}
    → (⟨⟩-inv : is-invertible ⟨ f , g ⟩)
    → f ∘ is-invertible.inv ⟨⟩-inv ≡ π₁
  π₁-inv {f = f} {g = g} ⟨⟩-inv =
    pushl (sym π₁∘⟨⟩) ∙ elimr (is-invertible.invl ⟨⟩-inv)

  π₂-inv
    : ∀ {f : Hom (a ⊗₀ b) c} {g : Hom (a ⊗₀ b) d}
    → (⟨⟩-inv : is-invertible ⟨ f , g ⟩)
    → g ∘ is-invertible.inv ⟨⟩-inv ≡ π₂
  π₂-inv {f = f} {g = g} ⟨⟩-inv =
    pushl (sym π₂∘⟨⟩) ∙ elimr (is-invertible.invl ⟨⟩-inv)
```
-->

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} where
  open Cat.Reasoning C
```
-->

## Representability of products

The collection of maps into a product $a \times b$ is equivalent to
the collection of pairs of maps into $a$ and $b$. The forward direction
of the equivalence is given by postcomposition of the projections, and
the reverse direction by the universal property of products.

```agda
  product-repr
    : ∀ {a b}
    → (prod : Product C a b)
    → (x : Ob)
    → Hom x (Product.apex prod) ≃ (Hom x a × Hom x b)
  product-repr prod x = Iso→Equiv λ where
      .fst f → π₁ ∘ f , π₂ ∘ f
      .snd .is-iso.inv (f , g) → ⟨ f , g ⟩
      .snd .is-iso.rinv (f , g) → π₁∘factor ,ₚ π₂∘factor
      .snd .is-iso.linv f → sym (⟨⟩∘ f) ∙ eliml ⟨⟩-η
    where open Product prod
```
