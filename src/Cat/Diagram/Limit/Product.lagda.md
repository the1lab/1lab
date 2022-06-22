---
description: |
  A correspondence is established between concretely-defined product
  diagrams and general limits of discrete diagrams.
---

```agda
open import Cat.Diagram.Limit.Base
open import Cat.Instances.Discrete
open import Cat.Instances.Shape.Pair
open import Cat.Instances.Functor
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Prelude

open import Data.Bool

module Cat.Diagram.Limit.Product {o h} (Cat : Precategory o h) where
```

<!--
```agda
open import Cat.Reasoning Cat

-- Yikes:
open is-product
open Terminal
open Cone-hom
open Product
open Functor
open Cone
```
-->

# Products are limits

We establishe the correspondence between binary products $A \times B$
and the `Limit`{.Agda} of a diagram of the [two object category].

[two object category]: Cat.Instances.Shape.Pair.html

```agda
Pair→Cone
  : ∀ {X} → (F : Functor ·· Cat)
  → Hom X (F .F₀ false) → Hom X (F .F₀ true)
  → Cone F
Pair→Cone F p1 p2 .apex = _
Pair→Cone F p1 p2 .ψ false = p1
Pair→Cone F p1 p2 .ψ true = p2
Pair→Cone F p1 p2 .commutes {false} {false} tt = eliml (F .F-id)
Pair→Cone F p1 p2 .commutes {true} {true} tt = eliml (F .F-id)
```

The two-way correspondence between products and terminal cones is then
simple enough to establish by appropriately shuffling the data.

```agda
Prod→Lim : {F : Functor ·· Cat} → Product Cat (F .F₀ false) (F .F₀ true) → Limit F
Prod→Lim {F = F} prod = lim where
  module prod = Product prod
  lim : Limit _
  lim .top = Pair→Cone F prod.π₁ prod.π₂
  lim .has⊤ cone .centre .hom = prod.⟨ cone .ψ false , cone .ψ true ⟩
  lim .has⊤ cone .centre .commutes false = prod.π₁∘factor
  lim .has⊤ cone .centre .commutes true = prod.π₂∘factor
  lim .has⊤ cone .paths other = Cone-hom-path F (sym (prod.unique _ p₁ p₂)) where
    p₁ : prod.π₁ ∘ other .hom ≡ cone .ψ false
    p₁ = other .commutes false

    p₂ : prod.π₂ ∘ other .hom ≡ cone .ψ true
    p₂ = other .commutes true

Lim→Prod : {F : Functor ·· Cat} → Limit F → Product Cat (F .F₀ false) (F .F₀ true)
Lim→Prod {F = F} lim = prod where
  module lim = Terminal lim
  prod : Product Cat _ _
  prod .apex = lim.top .apex
  prod .π₁ = lim.top .ψ false
  prod .π₂ = lim.top .ψ true
  prod .has-is-product .⟨_,_⟩ f g =
    lim.has⊤ (Pair→Cone _ f g ) .centre .hom 
  prod .has-is-product .π₁∘factor =
    lim.has⊤ (Pair→Cone F _ _) .centre .commutes false
  prod .has-is-product .π₂∘factor =
    lim.has⊤ (Pair→Cone F _ _) .centre .commutes true
  prod .has-is-product .unique f p q =
    sym (ap hom (lim.has⊤ (Pair→Cone _ _ _) .paths other))
    where
      other : Cone-hom _ _ _
      other .hom = _
      other .commutes false = p
      other .commutes true = q
```
