```agda
open import Cat.Diagram.Limit.Base
open import Cat.Instances.Discrete
open import Cat.Instances.Functor
open import Cat.Instances.Product
open import Cat.Prelude

open import Data.Bool

module Cat.Diagram.Product {o h} (C : Precategory o h) where
```

<!--
```agda
open import Cat.Reasoning C
private variable
  a b c d : Ob
open Functor
```
-->

# Products

The **product** $P$ of two objects $A$ and $B$, if it exists, is the
smallest object equipped with "projection" maps $P \to A$ and $P \to B$.
This situation can be visualised by putting the data of a product into a
commutative diagram, as the one below: To express that $P$ is the
_smallest_ object with projections to $A$ and $B$, we ask that any other
object $Q$ with projections through $A$ and $B$ factors uniquely through
$P$:

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

In the sense that (univalent) categories generalise posets, the product
of $A$ and $B$ --- if it exists --- generalises the binary meet
$A \wedge B$. Since products are [unique](#uniqueness) when they exist,
we may safely denote any product of $A$ and $B$ by $A \times B$.

For a diagram $A \ot A \times B \to B$ to be a product diagram, it must
be able to cough up an arrow $Q \to P$ given the data of another span $A
\ot Q \to B$, which must not only fit into the diagram above but be
unique among the arrows that do so.

This factoring is called the **pairing** of the arrows $f : Q \to A$ and
$g : Q \to B$, since in the special case where $Q$ is the [terminal
object] (hence the two arrows are global elements of $A$ resp. $B$), the
pairing $\langle f, g \rangle$ is a global element of the product $A
\times B$.

[terminal object]: Cat.Diagram.Terminal.html

We can concisely encode all of these properties and pieces of data into
a [limit] of the [two object diagram].

[limit]: Cat.Diagram.Limit.Base.html
[two object diagram]: Cat.Instances.Discrete.html

We begin by defining a diagram that picks out 2 objects from $\cC$.

```agda
Pair : Ob → Ob → Functor (Disc′ (el! Bool)) C
Pair a b = Disc-diagram Discrete-Bool λ where
  true → a
  false → b
```

If we have a pair of morphisms from $x$ into $a$ and $b$ respectively,
then we can form a cone with apex $x$.

```agda
product-cone : ∀ {x a b} → Hom x a → Hom x b → Const x => Pair a b
product-cone π₁ π₂ = Disc-natural λ where
    true → π₁
    false → π₂
```

Finally, we say that $\pi_1 : x \to a$, $\pi_2 : x \to b$ form a product
if the corresponding natural transformation forms a limit.

```agda
is-product : ∀ {x a b} → Hom x a → Hom x b → Type _
is-product {x = x} {a} {b} π₁ π₂ =
  is-limit {C = C} (Pair a b) x (product-cone π₁ π₂)

Product : Ob → Ob → Type _
Product a b = Limit (Pair a b)
```

## Concretely

The compact definition is useful, as it allows us to connect products to
the more general theory of limits. However, it is somewhat clumsy to deal
with when working with a _specific_ product. Therefore, we provide a
record `make-is-product`{.Agda} that unfolds the abstract definition.

```agda
record make-is-product {x a b} (π₁ : Hom x a) (π₂ : Hom x b) : Type (o ⊔ h) where
  no-eta-equality
  field
    ⟨_,_⟩     : ∀ {y} (p1 : Hom y a) (p2 : Hom y b) → Hom y x
    π₁∘factor : ∀ {y} {p1 : Hom y a} {p2 : Hom y b} → π₁ ∘ ⟨ p1 , p2 ⟩ ≡ p1
    π₂∘factor : ∀ {y} {p1 : Hom y a} {p2 : Hom y b} → π₂ ∘ ⟨ p1 , p2 ⟩ ≡ p2

    unique : ∀ {y} {p1 : Hom y a} {p2 : Hom y b}
           → (other : Hom y x)
           → π₁ ∘ other ≡ p1
           → π₂ ∘ other ≡ p2
           → other ≡ ⟨ p1 , p2 ⟩

  unique₂ : ∀ {y} {pr1 : Hom y a} {pr2 : Hom y b}
          → ∀ {o1} (p1 : π₁ ∘ o1 ≡ pr1) (q1 : π₂ ∘ o1 ≡ pr2)
          → ∀ {o2} (p2 : π₁ ∘ o2 ≡ pr1) (q2 : π₂ ∘ o2 ≡ pr2)
          → o1 ≡ o2
  unique₂ p1 q1 p2 q2 = unique _ p1 q1 ∙ sym (unique _ p2 q2)

  ⟨⟩∘ : ∀ {y r} {p1 : Hom y a} {p2 : Hom y b} (f : Hom r y)
      → ⟨ p1 , p2 ⟩ ∘ f ≡ ⟨ p1 ∘ f , p2 ∘ f ⟩
  ⟨⟩∘ f = unique _ (pulll π₁∘factor) (pulll π₂∘factor)

  ⟨⟩-η : ⟨ π₁ , π₂ ⟩ ≡ id
  ⟨⟩-η = sym $ unique id (idr _) (idr _) 
```

If we have an element of `make-is-product`{.Agda}, then we can construct
an element of `is-product`{.Agda}.

```agda
to-is-product
  : ∀ {x a b} {π₁ : Hom x a} {π₂ : Hom x b}
  → make-is-product π₁ π₂
  → is-product π₁ π₂
to-is-product {x = x} {a} {b} {π₁} {π₂} mkprod =
  to-is-limitp ml λ where
    {true} → refl
    {false} → refl
  where
    open make-is-product mkprod renaming (unique to unique-prod)
    open make-is-limit

    ml : make-is-limit (Pair a b) x
    ml .ψ true = π₁
    ml .ψ false = π₂
    ml .commutes {true} {true} f = ap (_∘ π₁) (transport-refl id) ∙ idl _
    ml .commutes {true} {false} f = absurd (true≠false f)
    ml .commutes {false} {true} f = absurd (true≠false $ sym f)
    ml .commutes {false} {false} f = ap (_∘ π₂) (transport-refl id) ∙ idl _
    ml .universal eta _ = ⟨ eta true , eta false ⟩
    ml .factors {j = true} eta _ = π₁∘factor
    ml .factors {j = false} eta _ = π₂∘factor
    ml .unique eta p other q = unique-prod other (q true) (q false)
```

To use the data of `is-product`{.Agda}, we provide a function for
*un*making a product.

```agda
unmake-is-product
  : ∀ {x a b} {π₁ : Hom x a} {π₂ : Hom x b}
  → is-product π₁ π₂
  → make-is-product π₁ π₂
unmake-is-product {x = x} {a} {b} {π₁} {π₂} lim = prod module unmake-prod where
  open make-is-product
  module lim = is-limit lim

  pair : ∀ {y} → Hom y a → Hom y b → ∀ (j : Bool) → Hom y (Pair a b .F₀ j)
  pair p1 p2 true = p1
  pair p1 p2 false = p2

  pair-commutes
    : ∀ {y} {p1 : Hom y a} {p2 : Hom y b}
    → {i j : Bool}
    → (p : i ≡ j)
    → Pair a b .F₁ p ∘ pair p1 p2 i ≡ pair p1 p2 j
  pair-commutes {p1 = p1} {p2 = p2} =
      (J (λ _ p → Pair a b .F₁ p ∘ pair p1 p2 _ ≡ pair p1 p2 _) (eliml (Pair a b .F-id)))

  prod : make-is-product π₁ π₂
  prod .⟨_,_⟩ p1 p2 =
    lim.universal
      (pair p1 p2)
      pair-commutes
  prod .π₁∘factor {p1 = p1} {p2 = p2} = lim.factors (pair p1 p2) pair-commutes
  prod .π₂∘factor {p1 = p1} {p2 = p2} = lim.factors (pair p1 p2) pair-commutes
  prod .unique {p1 = p1} {p2 = p2} other p q =
    lim.unique (pair p1 p2) pair-commutes other λ where
      true → p
      false → q
```

<!--
```agda
module is-product
  {x a b} {π₁ : Hom x a} {π₂ : Hom x b}
  (prod : is-product π₁ π₂)
  where

  open make-is-product (unmake-is-product prod) public
```
-->

We perform a similar construction for the bundled form of products.

```agda
record make-product (a b : Ob) : Type (o ⊔ h) where
  no-eta-equality
  field
    apex : Ob
    π₁ : Hom apex a
    π₂ : Hom apex b
    has-is-product : make-is-product π₁ π₂

  open make-is-product has-is-product public
```

<!--
```agda
to-product : make-product a b → Product a b
to-product mp = to-limit (to-is-product has-is-product)
  where open make-product mp

module Product {a b} (prod : Product a b) where
  open Limit prod renaming (apex to L-apex)
  open Functor
  open _=>_

  apex : Ob
  apex = L-apex

  π₁ : Hom apex a
  π₁ = ψ true

  π₂ : Hom apex b
  π₂ = ψ false

  has-is-product : is-product π₁ π₂
  has-is-product =
    to-is-limitp (unmake-limit has-limit) λ where
      {true} → refl
      {false} → refl

  open is-product has-is-product public
```
-->

## Uniqueness

<!--
```agda
module _ where
  open Product
```
-->


Products, when they exist, are unique. This follows from general results about
[uniqueness of limits], and is a good showcase of why we prefer the more abstract
definition.

[uniqueness of limits]: Cat.Diagram.Limit.Base#uniqueness

```agda
  products-unique : ∀ (p1 p2 : Product a b) → apex p1 ≅ apex p2
  products-unique p1 p2 =
    limits-unique (has-is-product p2) (has-is-product p1)
```

Furthermore, if $p$ is a product of $a$ and $b$, and $f : a \to a'$,
$g : b \to b'$ are both invertible maps, then $p$ is also the product
of $a'$ and $b'$. This also follows from a general theorem about limits;
both $a, b$ and $a', b'$ form diagrams of shape `Pair`{.Agda}, and
the pointwise isomorphisms are enough to induce a natural isomorphism
between the 2 diagrams.

```agda
  is-invertible→is-product
    : ∀ {a a′ b b′ p} {π₁ : Hom p a} {π₂ : Hom p b}
      {f : Hom a a′} {g : Hom b b′}
    → is-invertible f
    → is-invertible g
    → is-product π₁ π₂
    → is-product (f ∘ π₁) (g ∘ π₂)
  is-invertible→is-product {a = a} {a′} {b} {b′} {p} {f = f} {g} f-iso g-iso prod =
    natural-iso→is-limitp prod (to-natural-iso mi) λ where
      {true} → refl
      {false} → refl
    where
      open make-natural-iso
      module f-iso = is-invertible f-iso
      module g-iso = is-invertible g-iso

      mi : make-natural-iso (Pair a b) (Pair a′ b′)
      mi .eta true = f
      mi .eta false = g
      mi .inv true = f-iso.inv
      mi .inv false = g-iso.inv
      mi .eta∘inv true = f-iso.invl
      mi .eta∘inv false = g-iso.invl
      mi .inv∘eta true = f-iso.invr
      mi .inv∘eta false = g-iso.invr
      mi .natural x y f =
        J (λ y f → Pair a′ b′ .F₁ f ∘ mi .eta x ≡ mi .eta y ∘ Pair a b .F₁ f)
          (eliml (Pair a′ b′ .F-id) ∙ intror (Pair a b .F-id))
          f
```

# Categories with all binary products

Categories with all binary products are quite common, so we define
a module for working with them.

```agda
module BinaryProducts (all-products : ∀ a b → Product a b) where

  module product {a} {b} = Product (all-products a b)

  open product renaming (unique to ⟨⟩-unique) public

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
      (pulll π₁∘factor ∙ extendr π₁∘factor)
      (pulll π₂∘factor ∙ extendr π₂∘factor)
```

We also define a handful of common morphisms.

```agda
  δ : Hom a (a ⊗₀ a)
  δ = ⟨ id , id ⟩

  swap : Hom (a ⊗₀ b) (b ⊗₀ a)
  swap = ⟨ π₂ , π₁ ⟩
```
