```agda
open import Cat.Diagram.Product.Solver
open import Cat.Displayed.Cartesian
open import Cat.Diagram.Product renaming (module Cartesian to Products)
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Reasoning

module Cat.Displayed.Instances.Simple
  {o ℓ} (B : Precategory o ℓ)
  (has-prods : ∀ X Y → Product B X Y)
  where

open Precategory B
open Products B has-prods
```

# Simple Fibrations

One reason to be interested in fibrations is that they provide an
excellent setting to study logical and type-theoretical phenomena.
When constructing models of type theories, the general pattern
is to construct a category of contexts and substitutions, and then
to study types and terms as structures over this category.
The language of displayed categories allows us to capture this situation
quite succinctly by considering these extra pieces of equipment as
being fibred over our category of contexts.

Focusing in, the language of *simple fibrations* provides us with enough
structure to study simply-typed languages that have enough structure
to represent contexts internally (i.e.: product types).

To start, we fix some base category $\ca{B}$ with binary products.
Intuitvely, this will be some sort of category of contexts, and
context extension endows this category with products. We interpret a
type in a context to be an object $\Gamma \times X : \ca{B}$.

Maps between types in contexts $(\Gamma \times X) \to (\Delta \times Y)$
are then given by a map $\Gamma \to \Delta$ between contexts, and a
map $\Gamma \times X \to Y$, which is meant to denote a derivation
of $Y$ from $\Gamma \times X$.

To encode this as a displayed category, we define the space of
objects over some $\Gamma$ to be simply an object of $B$.
This may seem odd, but recall that we are modeling a type theory with
enough structure to consider contexts as types: if this is not the
situation (IE: STLC without products), then we need to consider a more
[refined notion].

[refined notion]: Cat.Displayed.Instances.CT-Structure.html

For the maps, we already have the map $\Gamma \to \Delta$ as the
base morphism, so the displayed portion of the map will be the
map $\Gamma \times X \to Y$ between derivations. The identity
morphism $id : \Gamma \times Y \to Y$ ignores the context, and
derives $Y$ by using the $Y$ we already had, and is thus represented
by the second projection $\pi_2$.

Composition of morphisms is somewhat more involved, but can be derived
by playing type-tetris, as it's all a matter of golfing the types
and contexts into the correct place. The category laws are then a matter
of bashing through a bunch of nested pairings and projections, and
can be entirely automated.

```agda
simple : Displayed B o ℓ
simple .Displayed.Ob[_] Γ = Ob
simple .Displayed.Hom[_] {Γ} {Δ} u X Y = Hom (Γ ⊗ X) Y
simple .Displayed.Hom[_]-set _ _ _ = Hom-set (_ ⊗ _) _
simple .Displayed.id′ = π₂
simple .Displayed._∘′_ {f = u} {g = v} f g = f ∘ ⟨ v ∘ π₁ , g ⟩
simple .Displayed.idr′ f =
  f ∘ ⟨ (id ∘ π₁) , π₂ ⟩ ≡⟨ products! B has-prods ⟩
  f                      ∎
simple .Displayed.idl′ {f = u} f =
  π₂ ∘ ⟨ u ∘ π₁ , f ⟩ ≡⟨ products! B has-prods ⟩
  f                   ∎
simple .Displayed.assoc′ {f = u} {g = v} {h = w} f g h =
  f ∘ ⟨ (v ∘ w) ∘ π₁ , g ∘ ⟨ w ∘ π₁ , h ⟩ ⟩ ≡⟨ products! B has-prods ⟩
  (f ∘ ⟨ v ∘ π₁ , g ⟩) ∘ ⟨ w ∘ π₁ , h ⟩     ∎
```

# Fibration Structure

As suggested by it's name, the simple fibration is a fibration.
given a map $\Gamma \to Delta$ in the base, and a $(\Delta , Y)$
upstairs, we can construct a lift by selecting $(\Gamma, Y)$ as the
corner of the lift, and then using the second projection as the lift
itself. Intuitively, this encodes a substitution of contexts: because
we are working with a simple type theory, the substitutions don't need
to touch the types, as there are no possible dependencies!

```agda
open Cartesian-fibration
open Cartesian-lift
open Cartesian

simple-fibration : Cartesian-fibration simple
simple-fibration .has-lift f Y .x′ = Y
simple-fibration .has-lift f Y .lifting = π₂
simple-fibration .has-lift f Y .cartesian .universal _ h = h
simple-fibration .has-lift f Y .cartesian .commutes g h = π₂∘⟨⟩
simple-fibration .has-lift f Y .cartesian .unique {m = g} {h′ = h} h' p =
  h'                   ≡˘⟨ π₂∘⟨⟩ ⟩
  π₂ ∘ ⟨ g ∘ π₁ , h' ⟩ ≡⟨ p ⟩
  h ∎
```
