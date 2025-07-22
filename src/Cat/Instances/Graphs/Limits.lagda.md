<!--
```agda
open import Cat.Diagram.Limit.Finite
open import Cat.Diagram.Pullback
open import Cat.Diagram.Terminal
open import Cat.Instances.Graphs
open import Cat.Diagram.Product
open import Cat.Prelude

open is-pullback
open is-product
open Graph-hom
open Pullback
open Product
open Graph
```
-->

```agda
module Cat.Instances.Graphs.Limits where
```

# Limits of graphs

<!--
```agda
private variable
  o ℓ o' ℓ' : Level
  X Y Z : Graph o ℓ
```
-->

We can compute [[limits]] in the category of [[graphs]] pointwise, i.e.
by letting both the nodes and edges be the limit of same shape in the
category $\Sets$. This follows from $\Graphs$ being a category of
presheaves, but constructing these directly gives us a nicer description
of the resulting adjacency.

::: warning
The *categorical* product of graphs should not be confused with the
[[box product]] of graphs, even though the box product may occasionally
(e.g. on Wikipedia) be called the "Cartesian product" of graphs!
:::

```agda
_×ᴳ_ : Graph o ℓ → Graph o' ℓ' → Graph _ _
(G ×ᴳ H) .Node = ⌞ G ⌟ × ⌞ H ⌟
(G ×ᴳ H) .Edge (a , x) (b , y) = G .Edge a b × H .Edge x y
(G ×ᴳ H) .Node-set = hlevel 2
(G ×ᴳ H) .Edge-set = hlevel 2
```

The terminal graph has a point and a loop on that point.

```agda
⊤ᴳ : Graph o ℓ
⊤ᴳ .Node     = Lift _ ⊤
⊤ᴳ .Edge _ _ = Lift _ ⊤
⊤ᴳ .Node-set = hlevel 2
⊤ᴳ .Edge-set = hlevel 2
```

We note that dependent types introduce a slight complication in defining
pullbacks of graphs: if one has an edge $\alpha : a \to b$ and $\xi : x
\to y$, their images under graph homomorphisms $f$ and $g$ live in
different types, namely $f(a) \to f(b)$ and $g(x) \to g(y)$. However,
since we are defining adjacency in the pullback of $f$ and $g$ we have,
by assumption, identities $f(a) = g(x)$ and $f(b) = g(y)$. We can thus
compare $f(\alpha)$ and $g(\xi)$ over these.

```agda
_⊓ᴳ_ : Graph-hom X Z → Graph-hom Y Z → Graph _ _
_⊓ᴳ_ {X = X} {Z = Z} {Y = Y} f g .Node = Σ[ x ∈ X ] Σ[ y ∈ Y ] f · x ≡ g · y

_⊓ᴳ_ {X = X} {Z = Z} {Y = Y} f g .Edge (a , x , p) (b , y , q) =
  Σ[ α ∈ X .Edge a b ]
  Σ[ ξ ∈ Y .Edge x y ]
  PathP (λ i → Z .Edge (p i) (q i)) (f .edge α) (g .edge ξ)

_⊓ᴳ_ {X = X} {Z = Z} {Y = Y} f g .Node-set = hlevel 2
_⊓ᴳ_ {X = X} {Z = Z} {Y = Y} f g .Edge-set = hlevel 2
```

Showing that these constructions satisfy the appropriate universal
property is simply an exercise in record construction, since, as
mentioned, they are pointwise inherited from $\Sets$, where the relevant
equations mostly hold definitionally.

```agda
fstᴳ : Graph-hom (X ×ᴳ Y) X
fstᴳ .node = fst
fstᴳ .edge = fst

sndᴳ : Graph-hom (X ×ᴳ Y) Y
sndᴳ .node = snd
sndᴳ .edge = snd

Graphs-products : ∀ {o ℓ} → has-products (Graphs o ℓ)
Graphs-products a b .apex = a ×ᴳ b
Graphs-products a b .π₁ = fstᴳ
Graphs-products a b .π₂ = sndᴳ
Graphs-products a b .has-is-product .⟨_,_⟩ f g = record where
  node z = f .node z , g .node z
  edge z = f .edge z , g .edge z

Graphs-products a b .has-is-product .π₁∘⟨⟩ = trivialᴳ!
Graphs-products a b .has-is-product .π₂∘⟨⟩ = trivialᴳ!

Graphs-products a b .has-is-product .unique p q = ext record where
  node x i = p i .node x , q i .node x
  edge e i = p i .edge e , q i .edge e

Graphs-terminal : ∀ {o ℓ} → Terminal (Graphs o ℓ)
Graphs-terminal .Terminal.top = ⊤ᴳ
Graphs-terminal .Terminal.has⊤ x .centre .node = _
Graphs-terminal .Terminal.has⊤ x .centre .edge = _
Graphs-terminal .Terminal.has⊤ x .paths h = trivialᴳ!

Graphs-pullbacks : ∀ {o ℓ} → has-pullbacks (Graphs o ℓ)
Graphs-pullbacks f g .apex = f ⊓ᴳ g

Graphs-pullbacks f g .p₁ .node (x , _ , _) = x
Graphs-pullbacks f g .p₁ .edge (x , _ , _) = x

Graphs-pullbacks f g .p₂ .node (_ , y , _) = y
Graphs-pullbacks f g .p₂ .edge (_ , y , _) = y

Graphs-pullbacks f g .has-is-pb .square = ext record where
  node _ _      p  = p
  edge (_ , _ , p) = p

Graphs-pullbacks f g .has-is-pb .universal {p₁' = p₁'} {p₂'} α = record where
  node x = p₁' .node x , p₂' .node x , λ i → α i .node x
  edge x = p₁' .edge x , p₂' .edge x , λ i → α i .edge x

Graphs-pullbacks f g .has-is-pb .p₁∘universal = trivialᴳ!
Graphs-pullbacks f g .has-is-pb .p₂∘universal = trivialᴳ!
Graphs-pullbacks f g .has-is-pb .unique α β = ext record where
  node x = (λ i → α i .node x) ,ₚ (λ i → β i .node x) ,ₚ prop!
  edge x = (λ i → α i .edge x) ,ₚ (λ i → β i .edge x) ,ₚ prop!

Graphs-finitely-complete : Finitely-complete (Graphs o ℓ)
Graphs-finitely-complete = record
  { Finitely-complete (with-pullbacks (Graphs _ _) Graphs-terminal Graphs-pullbacks) hiding (products)
  ; products = Graphs-products
  }
```
