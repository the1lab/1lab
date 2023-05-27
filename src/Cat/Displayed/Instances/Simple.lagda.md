<!--
```agda
open import Cat.Diagram.Product.Solver
open import Cat.Displayed.Cartesian
open import Cat.Diagram.Product
open import Cat.Diagram.Product
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Displayed.Instances.Simple
  {o ℓ} (B : Precategory o ℓ)
  (has-prods : ∀ X Y → Product B X Y)
  where

open Cat.Reasoning B
open Binary-products B has-prods
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

To start, we fix some base category $\cB$ with binary products.
Intuitvely, this will be some sort of category of contexts, and
context extension endows this category with products. We interpret a
type in a context to be an object $\Gamma \times X : \cB$.

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
Simple : Displayed B o ℓ
Simple .Displayed.Ob[_] Γ = Ob
Simple .Displayed.Hom[_] {Γ} {Δ} u X Y = Hom (Γ ⊗₀ X) Y
Simple .Displayed.Hom[_]-set _ _ _ = Hom-set (_ ⊗₀ _) _
Simple .Displayed.id′ = π₂
Simple .Displayed._∘′_ {f = u} {g = v} f g = f ∘ ⟨ v ∘ π₁ , g ⟩
Simple .Displayed.idr′ f =
  f ∘ ⟨ (id ∘ π₁) , π₂ ⟩ ≡⟨ products! B has-prods ⟩
  f                      ∎
Simple .Displayed.idl′ {f = u} f =
  π₂ ∘ ⟨ u ∘ π₁ , f ⟩ ≡⟨ products! B has-prods ⟩
  f                   ∎
Simple .Displayed.assoc′ {f = u} {g = v} {h = w} f g h =
  f ∘ ⟨ (v ∘ w) ∘ π₁ , g ∘ ⟨ w ∘ π₁ , h ⟩ ⟩ ≡⟨ products! B has-prods ⟩
  (f ∘ ⟨ v ∘ π₁ , g ⟩) ∘ ⟨ w ∘ π₁ , h ⟩     ∎
```

# Cartesian Morphisms

A morphism $f' : \Gamma \times X \to Y$ in the simple fibration is
cartesian if and only if the morphism
$\langle \pi_1 , f' \rangle : \Gamma \times X \to \Gamma \times Y$ is
invertible. This means that the cartesian morphisms are the isomorphisms
of types, as we are interpreting morphisms in the simple fibration as
derivations.

We begin with the reverse direction, as it is slightly simpler to show.

```agda
⟨⟩-invertible→cartesian
  : ∀ {Γ Δ x y} {f : Hom Γ Δ} {f′ : Hom (Γ ⊗₀ x) y}
  → is-invertible ⟨ π₁ , f′ ⟩ 
  → is-cartesian Simple f f′
⟨⟩-invertible→cartesian {Γ} {Δ} {x} {y} {f} {f′} ⟨⟩-inv = cart where
  module ⟨⟩-inv = is-invertible ⟨⟩-inv
  open is-cartesian
```

We begin by proving some small lemmas, which show that postcomposing
a projection with the inverse to $\langle \pi_1 , f' \rangle$ yields
a projection.

```agda
  π₁∘inv : π₁ ∘ ⟨⟩-inv.inv ≡ π₁
  π₁∘inv =
    π₁ ∘ ⟨⟩-inv.inv               ≡⟨ pushl (sym π₁∘⟨⟩) ⟩
    π₁ ∘ ⟨ π₁ , f′ ⟩ ∘ ⟨⟩-inv.inv ≡⟨ elimr ⟨⟩-inv.invl ⟩
    π₁ ∎

  f′∘inv : f′ ∘ ⟨⟩-inv.inv ≡ π₂
  f′∘inv =
    f′ ∘ ⟨⟩-inv.inv               ≡⟨ pushl (sym π₂∘⟨⟩) ⟩
    π₂ ∘ ⟨ π₁ , f′ ⟩ ∘ ⟨⟩-inv.inv ≡⟨ elimr ⟨⟩-inv.invl ⟩
    π₂                            ∎
```

With those lemmas out of the way, we proceed by constructing the
universal map of $f'$. Let $m : \Psi \to \Gamma$, and
$h' : \Psi \times Z \to Y$ be a pair of morphisms; we need to construct
some $m' : \Psi \times Z \to X$ that factorizes $h'$ through $f'$.
We by constructing the map
$\langle m \circ \pi_1 , h' \rangle : \Psi \times Z \to \Gamma \times Y$,
which we can then pre-compose with the inverse to $\langle \pi_1 , f' \rangle$
to obtain a map $\Psi \times Z \to \Gamma \times X$. Finally, we can
compose these two maps with the second projection, yielding the required
map.

```agda
  cart : is-cartesian Simple f f′
  cart .universal m h′ = π₂ ∘ ⟨⟩-inv.inv ∘ ⟨ m ∘ π₁ , h′ ⟩
```

Showing that this map uniquely factorises $f'$ boils down to pushing
around products and using that fact that the inverse to
$\langle \pi_1 , f' \rangle$ is, in fact, an inverse.

```agda
  cart .commutes m h′ =
    f′ ∘ ⟨ m ∘ π₁ , π₂ ∘ ⟨⟩-inv.inv ∘ ⟨ m ∘ π₁ , h′ ⟩ ⟩ ≡˘⟨ ap₂ _∘_ refl (⟨⟩-unique _ (pulll π₁∘inv ∙ π₁∘⟨⟩) refl) ⟩
    f′ ∘ ⟨⟩-inv.inv ∘ ⟨ m ∘ π₁ , h′ ⟩                   ≡⟨ pulll f′∘inv ⟩
    π₂ ∘ ⟨ m ∘ π₁ , h′ ⟩                                ≡⟨ π₂∘⟨⟩ ⟩
    h′                                                  ∎
  cart .unique {m = m} {h′ = h′} m′ p =
    m′                                                      ≡˘⟨ π₂∘⟨⟩ ⟩
    π₂ ∘ ⟨ m ∘ π₁ , m′ ⟩                                    ≡⟨ ap₂ _∘_ refl (introl ⟨⟩-inv.invr) ⟩
    π₂ ∘ (⟨⟩-inv.inv ∘ ⟨ π₁ , f′ ⟩) ∘ ⟨ m ∘ π₁ , m′ ⟩       ≡⟨ products! B has-prods ⟩
    π₂ ∘ ⟨⟩-inv.inv ∘ ⟨ m ∘ π₁ , ⌜ f′ ∘ ⟨ m ∘ π₁ , m′ ⟩ ⌝ ⟩ ≡⟨ ap! p ⟩
    π₂ ∘ ⟨⟩-inv.inv ∘ ⟨ m ∘ π₁ , h′ ⟩ ∎
```

On to the forward direction! Let $f : \Gamma \to \Delta$ and
$f' : \Gamma \times X \to Y$ form a cartesian map in the simple fibration.
We can construct an inverse to $\langle \pi_1 , f' \rangle$ by factorizing
the map $\pi_2 : \Gamma \times Y \to Y$, as in the following diagram:

~~~{.quiver}
\begin{tikzcd}
  Y \\
  & X && Y \\
  \Gamma \\
  & \Gamma && \Delta \\
  & \bullet
  \arrow["{\exist! i}", dashed, from=1-1, to=2-2]
  \arrow["{f'}", from=2-2, to=2-4]
  \arrow[lies over, from=2-2, to=4-2]
  \arrow[lies over, from=2-4, to=4-4]
  \arrow[lies over, from=1-1, to=3-1]
  \arrow["f"', curve={height=-12pt}, from=3-1, to=4-4]
  \arrow["id"', from=3-1, to=4-2]
  \arrow["f"', from=4-2, to=4-4]
  \arrow["{\pi_2}"{description}, curve={height=-12pt}, from=1-1, to=2-4]
\end{tikzcd}
~~~

```agda
cartesian→⟨⟩-invertible
  : ∀ {Γ Δ x y} {f : Hom Γ Δ} {f′ : Hom (Γ ⊗₀ x) y}
  → is-cartesian Simple f f′
  → is-invertible ⟨ π₁ , f′ ⟩
cartesian→⟨⟩-invertible {Γ} {Δ} {x} {y} {f} {f′} cart =
  make-invertible ⟨ π₁ , universal id π₂ ⟩
    left-inv
    right-inv
    where
      open is-cartesian cart
```

Showing that this map is a left inverse can be seen by a short computation.

```agda
      left-inv : ⟨ π₁ , f′ ⟩ ∘ ⟨ π₁ , universal id π₂ ⟩ ≡ id
      left-inv =
        ⟨ π₁ , f′ ⟩ ∘ ⟨ π₁ , universal id π₂ ⟩           ≡⟨ products! B has-prods ⟩
        ⟨ π₁ , ⌜ f′ ∘ ⟨ id ∘ π₁ ,  universal id π₂ ⟩ ⌝ ⟩ ≡⟨ ap! (commutes id π₂) ⟩
        ⟨ π₁ , π₂ ⟩                                      ≡⟨ ⟨⟩-η ⟩
        id                                               ∎
```

Showing that the constructed map is a right inverse is somewhat more
involved. The key lemma is that
$i \circ \langle \pi_1 , f' \rangle : \Gamma \times X \to X$ is equal
to $\pi_2$. To see this, consider the following diagram

~~~{.quiver}
\begin{tikzcd}
  X \\
  & Y \\
  \Gamma && X && Y \\
  & \Gamma \\
  && \Gamma && \Delta \\
  && \bullet
  \arrow["{\exist! i}", dashed, from=2-2, to=3-3]
  \arrow["{f'}", from=3-3, to=3-5]
  \arrow[lies over, from=3-3, to=5-3]
  \arrow[lies over, from=3-5, to=5-5]
  \arrow[lies over, from=2-2, to=4-2]
  \arrow["f"', curve={height=-12pt}, from=4-2, to=5-5]
  \arrow["id"', from=4-2, to=5-3]
  \arrow["f"', from=5-3, to=5-5]
  \arrow["{\pi_2}"{description}, curve={height=-12pt}, from=2-2, to=3-5]
  \arrow["{f'}", curve={height=-18pt}, from=1-1, to=3-5]
  \arrow["id"', from=3-1, to=4-2]
  \arrow[lies over, from=1-1, to=3-1]
  \arrow["{\langle \pi_1, f' \rangle}", from=1-1, to=2-2]
\end{tikzcd}
~~~

Note that $\pi_2$ factorizes $f'$, so it must be equal to the universal
factorization of $f'$, as $f'$ is cartesian. Furthermore,
$i \circ \langle \pi_1 , f' \rangle$ also factorizes $f'$, which lets us
see that $i \circ \langle \pi_1 , f' \rangle = \pi_2$.

```agda
      universal-π₂-unique : f′ ∘ ⟨ id ∘ π₁ , universal id π₂ ∘ ⟨ π₁ , f′ ⟩ ⟩ ≡ f′
      universal-π₂-unique =
        f′ ∘ ⟨ id ∘ π₁ , universal id π₂ ∘ ⟨ π₁ , f′ ⟩ ⟩ ≡⟨ products! B has-prods ⟩
        f′ ∘ ⟨ id ∘ π₁ , universal id π₂ ⟩ ∘ ⟨ π₁ , f′ ⟩ ≡⟨ pulll (commutes id π₂) ⟩
        π₂ ∘ ⟨ π₁ , f′ ⟩                                 ≡⟨ π₂∘⟨⟩ ⟩
        f′                                               ∎

      universal-π₂∘f′ : universal id π₂ ∘ ⟨ π₁ , f′ ⟩ ≡ π₂
      universal-π₂∘f′ =
        universal id π₂ ∘ ⟨ π₁ , f′ ⟩ ≡⟨ unique _ universal-π₂-unique ⟩
        universal id f′               ≡˘⟨ unique _ (elimr (ap₂ ⟨_,_⟩ (idl _) refl ∙ ⟨⟩-η)) ⟩
        π₂                            ∎
```

We can then apply this lemma to see that $\langle \pi_1, i \rangle$ forms
a right inverse.

```agda
      right-inv : ⟨ π₁ ,  universal id π₂ ⟩ ∘ ⟨ π₁ , f′ ⟩ ≡ id
      right-inv =
        ⟨ π₁ , universal id π₂ ⟩ ∘ ⟨ π₁ , f′ ⟩ ≡⟨ products! B has-prods ⟩
        ⟨ π₁ , universal id π₂ ∘ ⟨ π₁ , f′ ⟩ ⟩ ≡⟨ ap₂ ⟨_,_⟩ refl universal-π₂∘f′ ⟩
        ⟨ π₁ , π₂ ⟩                            ≡⟨ ⟨⟩-η ⟩
        id                                     ∎
```


# Fibration Structure

As suggested by it's name, the simple fibration is a fibration.
given a map $\Gamma \to Delta$ in the base, and a $(\Delta , Y)$
upstairs, we can construct a lift by selecting $(\Gamma, Y)$ as the
corner of the lift, and then using the second projection as the lift
itself. Intuitively, this encodes a substitution of contexts: because
we are working with a simple type theory, the substitutions don't need
to touch the types, as there are no possible dependencies!

<!--
```agda
open Cartesian-fibration
open Cartesian-lift
open is-cartesian
```
-->

```agda
Simple-fibration : Cartesian-fibration Simple
Simple-fibration .has-lift f Y .x′ = Y
Simple-fibration .has-lift f Y .lifting = π₂
Simple-fibration .has-lift f Y .cartesian .universal _ h = h
Simple-fibration .has-lift f Y .cartesian .commutes g h = π₂∘⟨⟩
Simple-fibration .has-lift f Y .cartesian .unique {m = g} {h′ = h} h' p =
  h'                   ≡˘⟨ π₂∘⟨⟩ ⟩
  π₂ ∘ ⟨ g ∘ π₁ , h' ⟩ ≡⟨ p ⟩
  h ∎
```
