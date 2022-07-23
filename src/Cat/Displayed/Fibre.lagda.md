```agda
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Reasoning as DR
import Cat.Displayed.Solver as SR
import Cat.Reasoning as CR

module Cat.Displayed.Fibre
  {o ℓ o′ ℓ′} {B : Precategory o ℓ}
  (E : Displayed B o′ ℓ′)
  where

open Displayed E
open SR E
open DR E
open CR B
```

## Fibre categories

A displayed category can be thought of as representing data of a "family
of categories"^[Though note that unless the displayed category is a
[Cartesian fibration], this "family" might not be functorially-indexed].
Given an object $x : \ca{B}$ of the base category, the morphisms in the
fibre over x, or **vertical morphisms**, are those in the set
$\hom_{\id{id}_x}(x, y)$ of morphisms over the identity map (on $x$).

[Cartesian fibration]: Cat.Displayed.Cartesian.html

The intuition from the term _vertical_ comes from _literally_ thinking
of a category $E$ displayed over $\ca{B}$ as being a like a grab-bag of
categories, admitting a map into $\ca{B}$ (the [total space]
perspective), a situation examplified by the diagram below. Here, $\int
E$ is the total space of a category $E$ displayed over $\ca{B}$, and
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
$\id{id}\circ\id{id}=\id{id}$ from the base category, implies that the
set of vertical arrows over an object $x$ contain identities and are
closed under composition, the **fibre (pre)category over $x$**.

[total space]: Cat.Displayed.Total.html

```agda
Fibre : Ob → Precategory _ _
Fibre x .Precategory.Ob = Ob[ x ]
Fibre x .Precategory.Hom a b = Hom[ id ] a b
Fibre x .Precategory.Hom-set = Hom[ id ]-set
Fibre x .Precategory.id = id′
Fibre x .Precategory._∘_ f g = hom[ idl id ] (f ∘′ g)
Fibre x .Precategory.idr f =
  hom[ idl id ] (f ∘′ id′) ≡⟨ reindex _ _ ⟩
  hom[ idr id ] (f ∘′ id′) ≡⟨ from-pathp (idr′ f) ⟩
  f                        ∎
Fibre x .Precategory.idl f = from-pathp (idl′ f)
Fibre x .Precategory.assoc f g h = r ∙ reindex _ _ ∙ sym s where
  r : PathP _ (hom[ B.idl B.id ] (f ∘′ hom[ B.idl B.id ] (g ∘′ h))) _
  r = symP $ eval′-sound `id (`hom[_]_ {f = `id `∘ `id} (B.idl B.id) (f ↑ `∘ `hom[_]_ {f = `id `∘ `id} (B.idl B.id) (g ↑ `∘ h ↑)))

  s : PathP _ (hom[ B.idl B.id ] (hom[ B.idl B.id ] (f ∘′ g) ∘′ h)) _
  s = symP $ eval′-sound `id (`hom[_]_ {f = `id `∘ `id} (B.idl B.id) (`hom[_]_ {f = `id `∘ `id} (B.idl B.id) (f ↑ `∘ g ↑) `∘ h ↑))
```
