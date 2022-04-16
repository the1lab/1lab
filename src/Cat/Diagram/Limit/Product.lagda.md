---
description: |
  A correspondence is established between concretely-defined product
  diagrams and general limits of discrete diagrams.
---

```agda
open import Cat.Diagram.Limit.Base
open import Cat.Instances.Discrete
open import Cat.Instances.Functor
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Prelude

open import Data.Bool

module Cat.Diagram.Limit.Product {o h} (C : Precategory o h) where
```

<!--
```agda
open import Cat.Reasoning C
open import Cat.Univalent C

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

We establish the correspondence between binary products $A \times B$ and
limits over the functor out of $\id{Disc}(\{0,1\})$ which maps $0$
to $A$ and $1$ to $B$. We begin by defining the functor (reusing
existing infrastructure):

```agda
2-object-diagram : ∀ {iss} → Ob → Ob → Functor (Disc′ (Bool , iss)) C
2-object-diagram A B = Disc-diagram Discrete-Bool λ where
  false → A
  true  → B
```

With that out of the way, we can establish the claimed equivalence. We
start by showing that any pair of morphisms $A \ot Q \to B$ defines a
cone over the discrete diagram consisting of $A$ and $B$. This is
essentially by _definition_ of what it means to be a cone in this case,
but they're arranged in very different ways:

```agda
Pair→Cone
  : ∀ {iss} {Q A B} → Hom Q A → Hom Q B
  → Cone (2-object-diagram {iss = iss} A B)
Pair→Cone {Q = Q} _ _ .apex  = Q
Pair→Cone p1 p2 .ψ false = p1
Pair→Cone p1 p2 .ψ true  = p2
Pair→Cone _ _ .commutes {false} {false} f = ap (_∘ _) (transport-refl _) ∙ idl _
Pair→Cone _ _ .commutes {false} {true}  f = absurd (true≠false (sym f))
Pair→Cone _ _ .commutes {true}  {false} f = absurd (true≠false f)
Pair→Cone _ _ .commutes {true}  {true}  f = ap (_∘ _) (transport-refl _) ∙ idl _
```

The two-way correspondence between products and terminal cones is then
simple enough to establish by appropriately shuffling the data.

```agda
Prod→Lim : ∀ {iss} {A B} → Product C A B → Limit (2-object-diagram {iss = iss} A B)
Prod→Lim prod .top = Pair→Cone (prod .π₁) (prod .π₂)
Prod→Lim prod .has⊤ x .centre .hom = prod .⟨_,_⟩ (x .ψ false) (x .ψ true)
Prod→Lim prod .has⊤ x .centre .commutes false = prod .π₁∘factor
Prod→Lim prod .has⊤ x .centre .commutes true  = prod .π₂∘factor
Prod→Lim prod .has⊤ x .paths y = Cone-hom-path (2-object-diagram _ _)
  (sym (prod .unique (y .hom) (y .commutes _) (y .commutes _)))

Lim→Prod : ∀ {iss} {A B} → Limit (2-object-diagram {iss = iss} A B) → Product C A B
Lim→Prod x .apex = x .top .apex
Lim→Prod x .π₁   = x .top .ψ false
Lim→Prod x .π₂   = x .top .ψ true
Lim→Prod x .has-is-product .⟨_,_⟩ p1 p2 = x .has⊤ (Pair→Cone p1 p2) .centre .hom
Lim→Prod x .has-is-product .π₁∘factor = x .has⊤ (Pair→Cone _ _) .centre .commutes _
Lim→Prod x .has-is-product .π₂∘factor = x .has⊤ (Pair→Cone _ _) .centre .commutes _
Lim→Prod x .has-is-product .unique f p q =
  sym (ap hom (x .has⊤ (Pair→Cone _ _) .paths other))
  where
    other : Cone-hom (2-object-diagram _ _) _ _
    other .hom = f
    other .commutes false = p
    other .commutes true  = q
```

We note that _any_ functor $F : \id{Disc}(\{0,1\}) \to \ca{C}$ is
canonically _equal_, not just naturally isomorphic, to the one we
defined above.

```agda
canonical-functors
  : ∀ {iss} (F : Functor (Disc′ (Bool , iss)) C)
  → F ≡ 2-object-diagram (F₀ F false) (F₀ F true)
canonical-functors {iss = iss} F = Functor-path p q where
  p : ∀ x → _
  p false = refl
  p true  = refl

  q : ∀ {x y} (f : x ≡ y) → _
  q {false} {false} p =
    F₁ F p            ≡⟨ ap (F₁ F) (iss _ _ _ _) ⟩
    F₁ F refl         ≡⟨ F-id F ⟩
    id                ≡˘⟨ transport-refl _ ⟩
    transport refl id ∎
  q {true} {true} p =
    F₁ F p            ≡⟨ ap (F₁ F) (iss _ _ _ _) ⟩
    F₁ F refl         ≡⟨ F-id F ⟩
    id                ≡˘⟨ transport-refl _ ⟩
    transport refl id ∎
  q {false} {true} p = absurd (true≠false (sym p))
  q {true} {false} p = absurd (true≠false p)
```
