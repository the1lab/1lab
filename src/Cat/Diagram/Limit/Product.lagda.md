---
description: |
  A correspondence is established between concretely-defined product
  diagrams and general limits of discrete diagrams.
---

```agda
open import Cat.Instances.Shape.Terminal
open import Cat.Diagram.Limit.Base
open import Cat.Instances.Discrete
open import Cat.Instances.Functor
open import Cat.Functor.Kan.Base
open import Cat.Diagram.Product
open import Cat.Prelude

open import Data.Bool

module Cat.Diagram.Limit.Product {o h} (C : Precategory o h) where
```

<!--
```agda
open import Cat.Reasoning C

open is-product
open Product
open Functor
open _=>_
```
-->

# Products are limits

We establish the correspondence between binary products $A \times B$ and
limits over the functor out of $\rm{Disc}(\{0,1\})$ which maps $0$
to $A$ and $1$ to $B$. We begin by defining the functor (reusing
existing infrastructure):

```agda
2-object-diagram : ∀ {iss} → Ob → Ob → Functor (Disc′ (el Bool iss)) C
2-object-diagram a b = Disc-diagram Discrete-Bool λ where
  true  → a
  false → b
```

With that out of the way, we can establish the claimed equivalence. We
start by showing that any pair of morphisms $A \ot Q \to B$ defines a
cone over the discrete diagram consisting of $A$ and $B$. This is
essentially by _definition_ of what it means to be a cone in this case,
but they're arranged in very different ways:

```agda
Pair→Cone
  : ∀ {iss} {q a b} → Hom q a → Hom q b
  → Const q => (2-object-diagram {iss} a b)
Pair→Cone f g = Disc-natural λ where
  true → f
  false → g
```

The two-way correspondence between products and terminal cones is then
simple enough to establish by appropriately shuffling the data.

```agda
is-product→is-limit
  : ∀ {iss} {x a b} {p1 : Hom x a} {p2 : Hom x b}
  → is-product C p1 p2
  → is-limit {C = C} (2-object-diagram {iss} a b) x (Pair→Cone p1 p2)
is-product→is-limit {x = x} {a} {b} {p1} {p2} is-prod =
  to-is-limitp ml λ where
    {true} → refl
    {false} → refl
  where
    module is-prod = is-product is-prod
    open make-is-limit

    ml : make-is-limit (2-object-diagram a b) x
    ml .ψ true = p1
    ml .ψ false = p2
    ml .commutes {true} {true} f = ap (_∘ p1) (transport-refl id) ∙ idl _
    ml .commutes {true} {false} f = absurd (true≠false f)
    ml .commutes {false} {true} f = absurd (true≠false $ sym f)
    ml .commutes {false} {false} f = ap (_∘ p2) (transport-refl id) ∙ idl _
    ml .universal eta _ = is-prod.⟨ eta true , eta false ⟩
    ml .factors {true} eta _ = is-prod.π₁∘factor
    ml .factors {false} eta _ = is-prod.π₂∘factor
    ml .unique eta p other q = is-prod.unique other (q true) (q false)

is-limit→is-product
  : ∀ {iss} {a b} {K : Functor ⊤Cat C}
  → {eta : K F∘ !F => 2-object-diagram {iss} a b}
  → is-ran !F (2-object-diagram {iss} a b) K eta
  → is-product C (eta .η true) (eta .η false)
is-limit→is-product {iss = iss} {a} {b} {K} {eta} lim = prod where
  module lim = is-limit lim

  pair
    : ∀ {y} → Hom y a → Hom y b
    → ∀ (j : Bool) → Hom y (2-object-diagram {iss} a b .F₀ j)
  pair p1 p2 true = p1
  pair p1 p2 false = p2

  pair-commutes
    : ∀ {y} {p1 : Hom y a} {p2 : Hom y b}
    → {i j : Bool}
    → (p : i ≡ j)
    → 2-object-diagram {iss} a b .F₁ p ∘ pair p1 p2 i ≡ pair p1 p2 j
  pair-commutes {p1 = p1} {p2 = p2} =
      J (λ _ p → 2-object-diagram {iss} a b .F₁ p ∘ pair p1 p2 _ ≡ pair p1 p2 _)
        (eliml (2-object-diagram {iss} a b .F-id))

  prod : is-product C (eta .η true) (eta .η false)
  prod .⟨_,_⟩ f g = lim.universal (pair f g) pair-commutes
  prod .π₁∘factor {_} {p1'} {p2'} = lim.factors (pair p1' p2') pair-commutes
  prod .π₂∘factor {_} {p1'} {p2'} = lim.factors (pair p1' p2') pair-commutes
  prod .unique other p q = lim.unique _ _ other λ where
    true → p
    false → q

Product→Limit : ∀ {iss} {a b} → Product C a b → Limit (2-object-diagram {iss} a b)
Product→Limit prod = to-limit (is-product→is-limit (has-is-product prod))

Limit→Product : ∀ {iss} {a b} → Limit (2-object-diagram {iss} a b) → Product C a b
Limit→Product lim .apex = Limit.apex lim
Limit→Product lim .π₁ = Limit.cone lim .η true
Limit→Product lim .π₂ = Limit.cone lim .η false
Limit→Product lim .has-is-product =
  is-limit→is-product (Limit.has-limit lim)
```

We note that _any_ functor $F : \rm{Disc}(\{0,1\}) \to \cC$ is
canonically _equal_, not just naturally isomorphic, to the one we
defined above.

```agda
canonical-functors
  : ∀ {iss} (F : Functor (Disc′ (el Bool iss)) C)
  → F ≡ 2-object-diagram (F₀ F true) (F₀ F false)
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
