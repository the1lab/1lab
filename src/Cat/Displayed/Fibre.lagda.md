```agda
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Reasoning as Dr
import Cat.Displayed.Solver as Ds
import Cat.Reasoning as Cr
import Cat.Displayed.Morphism as Dm

module Cat.Displayed.Fibre
  {o ℓ o′ ℓ′} {B : Precategory o ℓ}
  (E : Displayed B o′ ℓ′)
  where

open Displayed E
open Ds
open Dr E
open Cr B
open Dm E
```

## Fibre categories

A displayed category can be thought of as representing data of a "family
of categories"^[Though note that unless the displayed category is a
[Cartesian fibration], this "family" might not be functorially-indexed].
Given an object $x : \cB$ of the base category, the morphisms in the
fibre over x, or **vertical morphisms**, are those in the set
$\hom_{\id[x]}(x, y)$ of morphisms over the identity map (on $x$).

[Cartesian fibration]: Cat.Displayed.Cartesian.html

The intuition from the term _vertical_ comes from _literally_ thinking
of a category $E$ displayed over $\cB$ as being a like a grab-bag of
categories, admitting a map into $\cB$ (the [total space]
perspective), a situation examplified by the diagram below. Here, $\int
E$ is the total space of a category $E$ displayed over $\cB$, and
$\pi$ is the corresponding projection functor.

~~~{.quiver .tall-2}
\begin{tikzpicture}
\node (basex) at (-1.5, -2) {$x$};
\node (basey) at (0, -2)  {$y$};
\node (basez) at (1, -2)  {$z$};
\draw[->] (basex) -- (basey) node[midway, preaction={fill, diagrambg}, inner sep=0.3mm] {$f$};
\node[draw,dashed,inner sep=2mm,fit=(basex) (basex) (basex) (basez)] (basecat) {};
\node[xshift=-0.4cm] (baselabel) at (basecat.west) {$\mathcal{B}$};

\node[] (aoverx) at (-1.5, 1.75) {$a$};
\node[] (boverx) at (-1.5, 0.5) {$b$};
\node[] (covery) at (0, 0.5) {$c$};
\node[] (doverz) at (1, 0.5) {$d$};
\draw[->] (aoverx) -- (boverx) node[midway, left, inner sep=0.3mm] (g) {$g$};
\draw[->] (aoverx) -- (covery) node[midway, preaction={fill, diagrambg}, inner sep=0.3mm] {$h$};
\node[draw,inner sep=2mm,fit=(aoverx) (g) (boverx) (doverz)] (dispcat) {};
\node[xshift=-0.4cm] (displabel) at (dispcat.west) {$\int\!\! E$};

\draw[->] (displabel) -- (baselabel) node[pos=0.6, preaction={fill, diagrambg}] {$\pi$};

\node[] () [] at (basecat.south) {};
\node[] () [] at (basecat.east) {};
\node[] () [] at (dispcat.north) {};
\end{tikzpicture}
~~~

In this diagram, the map $g$, which is displayed over the identity on
$a$, is literally... vertical! A map such as $h$, between objects in two
different fibres (hence displayed over a non-identity map $f$), is not
drawn vertically. Additionally, the unwritten (displayed) identity
morphisms on $a$, $b$, $c$, and $d$ are all vertical.

This last observation, coupled with the equation
$\id\circ\id=\id$ from the base category, implies that the
set of vertical arrows over an object $x$ contain identities and are
closed under composition, the **fibre (pre)category over $x$**.

[total space]: Cat.Displayed.Total.html

This definition does work, but requires a transport every time we compose!
To avoid this, we allow the morphisms of fibre categories to be displayed
over any morphism $u : \cC(X, X)$, so long as $u$ is propositionally
equal to the identity morphism. This allows us to fuse all of the
transports, which drastically improves the situation.

```agda
module _ (X : Ob) where
  record Fibre-hom (a b : Ob[ X ]) : Type (ℓ ⊔ ℓ′) where
    no-eta-equality
    field
      base  : Hom X X
      is-id : base ≡ id
      vert  : Hom[ base ] a b

  open Fibre-hom public

```

As an aside, this fusion technique is a sneaky application of the
[coyoneda lemma].

[coyoneda lemma]: Cat.Functor.Hom.Coyoneda.html

<!--
```agda
  Fibre-hom-pathp
    : ∀ (a b : I → Ob[ X ])
      {f : Fibre-hom (a i0) (b i0)}
      {g : Fibre-hom (a i1) (b i1)}
    → (p : f .base ≡ g .base)
    → (α : PathP (λ i → Hom[ p i ] (a i) (b i)) (f .vert) (g .vert))
    → PathP (λ i → Fibre-hom (a i) (b i)) f g
  Fibre-hom-pathp a b {f} {g} p α = done where
    done : PathP (λ i → Fibre-hom (a i) (b i)) f g
    done i .base  = p i
    done i .is-id = is-prop→pathp (λ i → Hom-set _ _ (p i) _) (f .is-id) (g .is-id) i
    done i .vert  = α i

  Fibre-hom-path
    : ∀ {a b} {f g : Fibre-hom a b}
    → (p : f .base ≡ g .base) → PathP (λ i → Hom[ p i ] a b) (f .vert) (g .vert) → f ≡ g
  Fibre-hom-path {a} {b} {f} {g} =
    Fibre-hom-pathp (λ _ → a) (λ _ → b) {f = f} {g = g}

  private unquoteDecl eqv = declare-record-iso eqv (quote Fibre-hom)

  abstract
    Fibre-hom-is-set
      : ∀ {a b} → is-set (Fibre-hom a b)
    Fibre-hom-is-set = Iso→is-hlevel 2 eqv (hlevel 2)
      where open Hom[]-hlevel-instance
```
-->

With that technicality out of the way, we can proceed to define the
actual category.

```agda
  Fibre : Precategory o′ (ℓ ⊔ ℓ′)
  Fibre .Precategory.Ob = Ob[ X ]
  Fibre .Precategory.Hom = Fibre-hom
  Fibre .Precategory.Hom-set _ _ = Fibre-hom-is-set
  Fibre .Precategory.id .base = id
  Fibre .Precategory.id .is-id = refl
  Fibre .Precategory.id .vert = id′
  Fibre .Precategory._∘_ f g .base  = f .base ∘ g .base
  Fibre .Precategory._∘_ f g .is-id = eliml (f .is-id) ∙ g .is-id
  Fibre .Precategory._∘_ f g .vert  = f .vert ∘′ g .vert
```

<!--
```agda
  Fibre .Precategory.idr f = Fibre-hom-path (idr _) (idr′ _)
  Fibre .Precategory.idl f = Fibre-hom-path (idl _) (idl′ _)
  Fibre .Precategory.assoc f g h = Fibre-hom-path (assoc _ _ _) (assoc′ _ _ _)
```
-->

# Morphisms in Fibre Categories

Our trick for postponing transports does make morphisms of fibre
categories more pleasant to work with, but does make the relation
between vertical morphisms and morphisms in the fibre more involved.

<!--
```agda
module _ {x : Ob} where
  private
    module Fibre = Cr (Fibre x)
```
-->

To start, we note that there is an equivalence between vertical morphism
and morphisms in fibre categories.

```agda
  to-vert : ∀ {a b} → Fibre-hom x a b → Hom[ id ] a b
  to-vert f = hom[ f .is-id ] (f .vert)

  from-vert : ∀ {a b} → Hom[ id ] a b → Fibre-hom x a b
  from-vert x .base  = id
  from-vert x .is-id = refl
  from-vert x .vert  = x

  to-vert-is-equiv : ∀ {a b} → is-equiv (to-vert {a} {b})
  to-vert-is-equiv =
    is-iso→is-equiv $ iso
      from-vert
      transport-refl
      (λ f → Fibre-hom-path x
        (sym (f .is-id))
        (symP (transport-filler (λ i → Hom[ f .is-id i ] _ _) (f .vert))))

  vert-equiv : ∀ {a b} → Fibre-hom x a b ≃ Hom[ id ] a b
  vert-equiv = to-vert , to-vert-is-equiv

  -- to-vertl : ∀ {a b} {f : Fibre-hom x a b} {v : Hom[ id ] a b} → to-vert f ≡ ? ∘′ ?
```

Furthermore, isomorphism in fibre categories correspond to vertical
isomorphisms.

```agda
  fibre-iso→vert-iso : ∀ {a b} → a Fibre.≅ b → a ≅↓ b 
  fibre-iso→vert-iso i = make-iso[ id-iso ]
    (to-vert (Fibre.to i))
    (to-vert (Fibre.from i))
    (collapse (ap vert (Fibre.invl i)))
    (collapse (ap vert (Fibre.invr i)))

  vert-iso→fibre-iso : ∀ {a b} → a ≅↓ b → a Fibre.≅ b
  vert-iso→fibre-iso i = Fibre.make-iso
    (from-vert (i .to′))
    (from-vert (i .from′))
    (Fibre-hom-path x _ (i .invl′))
    (Fibre-hom-path x _ (i .invr′))
```
