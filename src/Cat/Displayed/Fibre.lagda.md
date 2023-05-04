<!--
```agda
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Reasoning as Dr
import Cat.Displayed.Solver as Ds
import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Displayed.Fibre
  {o ℓ o′ ℓ′} {B : Precategory o ℓ}
  (E : Displayed B o′ ℓ′)
  where

open Ds
open Dr E
open Cr B
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

```agda
Fibre′
  : (X : Ob)
  → (fix : {x y : Ob[ X ]} → Hom[ id ∘ id ] x y → Hom[ id ] x y)
  → (coh : ∀ {x y} (f : Hom[ id ∘ id ] x y) → fix f ≡ hom[ idl id ] f)
  → Precategory _ _
Fibre′ X fix coh .Precategory.Ob = Ob[ X ]
Fibre′ X fix coh .Precategory.Hom = Hom[ id ]
Fibre′ X fix coh .Precategory.Hom-set = Hom[ id ]-set
Fibre′ X fix coh .Precategory.id = id′
Fibre′ X fix coh .Precategory._∘_ f g = fix (f ∘′ g)
```

The definition of `Fibre′`{.Agda} has an extra degree of freedom: it is
parametrised over how to reindex a morphism from lying over $\id
\circ \id$ to lying over $\id$. You don't get _that_ much
freedom, however: there is a canonical way of doing this reindexing,
which is to transport the composite morphism (since $\id \circ
\id$ is equal to $\id$), and the provided method _must_ be
homotopic to this canonical one --- to guarantee that the resulting
construction is a precategory.

It may seem that this extra freedom serves no purpose, then, but there
are cases where it's possible to transport without actually
transporting: For example, if $\cE$ is displayed over $\Sets$, then
composition of morphisms is definitionally unital, so transporting is
redundant; but without regularity, the transports along reflexivity
would still pile up.

<!--
```agda
Fibre′ X fix coh .Precategory.idr f =
  fix (f ∘′ id′)           ≡⟨ coh (f ∘′ id′) ⟩
  hom[ idl id ] (f ∘′ id′) ≡⟨ Ds.disp! E ⟩
  f                        ∎
Fibre′ X fix coh .Precategory.idl f =
  fix (id′ ∘′ f)           ≡⟨ coh (id′ ∘′ f) ⟩
  hom[ idl id ] (id′ ∘′ f) ≡⟨ from-pathp (idl′ f) ⟩
  f                        ∎
Fibre′ X fix coh .Precategory.assoc f g h =
  fix (f ∘′ fix (g ∘′ h))                     ≡⟨ ap (λ e → fix (f ∘′ e)) (coh _) ∙ coh _ ⟩
  hom[ idl id ] (f ∘′ hom[ idl id ] (g ∘′ h)) ≡⟨ Ds.disp! E ⟩
  hom[ idl id ] (hom[ idl id ] (f ∘′ g) ∘′ h) ≡⟨ sym (coh _) ∙ ap (λ e → fix (e ∘′ h)) (sym (coh _)) ⟩
  fix (fix (f ∘′ g) ∘′ h)                     ∎
```
-->

```agda
Fibre : Ob → Precategory _ _
Fibre X = Fibre′ X _ (λ f → refl)
```
