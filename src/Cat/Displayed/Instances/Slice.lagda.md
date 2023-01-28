```agda
open import Cat.Displayed.Cartesian
open import Cat.Functor.Equivalence
open import Cat.Diagram.Pullback
open import Cat.Displayed.Fibre
open import Cat.Instances.Slice
open import Cat.Displayed.Base
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Reasoning as CR

module Cat.Displayed.Instances.Slice {o ℓ} (B : Precategory o ℓ) where
```

<!--
```agda
open Cartesian-fibration
open Cartesian-lift
open Displayed
open is-cartesian
open Functor
open CR B
open /-Obj
```
-->

# The canonical self-indexing

There is a canonical way of viewing any category $\cB$ as displayed
over _itself_, given [fibrewise] by taking [slice categories]. Following
[@relativect], we refer to this construction as the **canonical-self
indexing** of $\cB$ and denote it $\underline{\cB}$. Recall that
the objects in the slice over $y$ are pairs consisting of an object $x$
and a map $f : x \to y$. The core idea is that _any morphism_ lets us
view an object $x$ as being "structure over" an object $y$; the
collection of all possible such structures, then, is the set of
morphisms $x \to y$, with domain allowed to vary.

[fibrewise]: Cat.Displayed.Fibre.html
[slice categories]: Cat.Instances.Slice.html

Contrary to the maps in the slice category, the maps in the canonical
self-indexing have an extra "adjustment" by a morphism $f : x \to y$ of
the base category. Where maps in the ordinary slice are given by
commuting triangles, maps in the canonical self-indexing are given by
commuting _squares_, of the form

~~~{.quiver}
\[\begin{tikzcd}
  x' && y' \\
  \\
  x && {y\text{,}}
  \arrow["{p_x}"', dashed, from=1-1, to=3-1]
  \arrow["{p_y}"', dashed, from=1-3, to=3-3]
  \arrow["f'", dashed, from=1-1, to=1-3]
  \arrow["f"', from=3-1, to=3-3]
\end{tikzcd}\]
~~~

where the primed objects and dotted arrows are displayed.

```agda
record
  Slice-hom
    {x y} (f : Hom x y)
    (px : /-Obj {C = B} x) (py : /-Obj {C = B} y)
    : Type (o ⊔ ℓ)
  where
  constructor slice-hom
  field
    to      : Hom (px .domain) (py .domain)
    commute : f ∘ px .map ≡ py .map ∘ to

open Slice-hom
```

<!--
```agda
private unquoteDecl eqv = declare-record-iso eqv (quote Slice-hom)
```
-->

The intuitive idea for the canonical self-indexing is possibly best
obtained by considering the canonical self-indexing of $\Sets_\kappa$.
First, recall that an object $f : \Sets/X$ is equivalently a $X$-indexed
family of sets, with the value of the family at each point $x : X$ being
the fibre $f^*(x)$. A function $X \to Y$ of sets then corresponds to a
_reindexing_, which takes an $X$-family of sets to a $Y$-family of sets
([in a functorial way]). A morphism $X' \to Y'$ in the canonical
self-indexing of $\Sets$ lying over a map $f : X \to Y$ is then a
function between the families $X' \to Y'$ which commutes with the
reindexing given by $f$.

[in a functorial way]: Cat.Instances.Slice.html#slices-of-sets

<!--
```agda
module _ {x y} {f g : Hom x y} {px : /-Obj x} {py : /-Obj y}
         {f′ : Slice-hom f px py} {g′ : Slice-hom g px py} where

  Slice-pathp : (p : f ≡ g) → (f′ .to ≡ g′ .to) → PathP (λ i → Slice-hom (p i) px py) f′ g′
  Slice-pathp p p′ i .to = p′ i
  Slice-pathp p p′ i .commute =
    is-prop→pathp
      (λ i → Hom-set _ _ (p i ∘ px .map) (py .map ∘ (p′ i)))
      (f′ .commute)
      (g′ .commute)
      i

module _ {x y} (f : Hom x y) (px : /-Obj x) (py : /-Obj y) where
  Slice-is-set : is-set (Slice-hom f px py)
  Slice-is-set = Iso→is-hlevel 2 eqv (hlevel 2)
    where open HLevel-instance
```
-->

It's straightforward to piece together the objects of the (ordinary)
slice category and our displayed maps `Slice-hom`{.Agda} into a category
displayed over $\cB$.

```agda
Slices : Displayed B (o ⊔ ℓ) (o ⊔ ℓ)
Slices .Ob[_] = /-Obj {C = B}
Slices .Hom[_] = Slice-hom
Slices .Hom[_]-set = Slice-is-set
Slices .id′ = slice-hom id id-comm-sym
Slices ._∘′_ {x = x} {y = y} {z = z} {f = f} {g = g} px py =
  slice-hom (px .to ∘ py .to) $
    (f ∘ g) ∘ x .map           ≡⟨ pullr (py .commute) ⟩
    f ∘ (y .map ∘ py .to)      ≡⟨ extendl (px .commute) ⟩
    z .map ∘ (px .to ∘ py .to) ∎
Slices .idr′ {f = f} f′ = Slice-pathp (idr f) (idr (f′ .to))
Slices .idl′ {f = f} f′ = Slice-pathp (idl f) (idl (f′ .to))
Slices .assoc′ {f = f} {g = g} {h = h} f′ g′ h′ =
  Slice-pathp (assoc f g h) (assoc (f′ .to) (g′ .to) (h′ .to))
```

It's only slightly more annoying to show that a vertical map in the
canonical self-indexing is a map in the ordinary slice category which,
since the objects displayed over $x$ are _defined_ to be those of the
slice category $\cB/x$, gives an equivalence of categories between
the fibre $\underline{\cB}^*(x)$ and the slice $\cB/x$.

```agda
Fibre→slice : ∀ {x} → Functor (Fibre Slices x) (Slice B x)
Fibre→slice .F₀ x = x
Fibre→slice .F₁ f ./-Hom.map = f .to
Fibre→slice .F₁ f ./-Hom.commutes = sym (f .commute) ∙ eliml refl
Fibre→slice .F-id = /-Hom-path refl
Fibre→slice .F-∘ f g = /-Hom-path (transport-refl _)

Fibre→slice-is-ff : ∀ {x} → is-fully-faithful (Fibre→slice {x = x})
Fibre→slice-is-ff {_} {x} {y} = is-iso→is-equiv isom where
  isom : is-iso (Fibre→slice .F₁)
  isom .is-iso.inv hom =
    slice-hom (hom ./-Hom.map) (eliml refl ∙ sym (hom ./-Hom.commutes))
  isom .is-iso.rinv x = /-Hom-path refl
  isom .is-iso.linv x = Slice-pathp refl refl

Fibre→slice-is-equiv : ∀ {x} → is-equivalence (Fibre→slice {x})
Fibre→slice-is-equiv = is-precat-iso→is-equivalence $
  record { has-is-ff = Fibre→slice-is-ff
         ; has-is-iso = id-equiv
         }
```

## As a fibration

If (and only if) $\cB$ has all [pullbacks], then the self-indexing
$\cB$ is a [Cartesian fibration]. This is almost by definition, and
is in fact where the "Cartesian" in "Cartesian fibration" (recall that
another term for "pullback square" is "cartesian square"). Since the
total space $\int \underline{\cB}$ is equivalently the arrow category
of $\cB$, with the projection functor $\pi : \int \underline{\cB}
\to \cB$ corresponding under this equivalence to the codomain
functor, we refer to $\underline{ca{B}}$ regarded as a Cartesian
fibration as the **codomain fibration**.

```agda
Codomain-fibration
  : (∀ {x y z} (f : Hom x y) (g : Hom z y) → Pullback B f g)
  → Cartesian-fibration Slices
Codomain-fibration pullbacks .has-lift f y′ = lift-f where
  open Pullback (pullbacks f (y′ .map))

  lift-f : Cartesian-lift Slices f y′
  lift-f .x′ = cut p₁
  lift-f .lifting .to = p₂
  lift-f .lifting .commute = square
  lift-f .cartesian .universal m h′ .to = limiting (assoc _ _ _ ∙ h′ .commute)
  lift-f .cartesian .universal m h′ .commute = sym p₁∘limiting
  lift-f .cartesian .commutes m h′ = Slice-pathp refl p₂∘limiting
  lift-f .cartesian .unique m′ x = Slice-pathp refl $
    Pullback.unique (pullbacks f (y′ .map)) (sym (m′ .commute)) (ap to x)
```

[pullbacks]: Cat.Diagram.Pullback.html
[Cartesian fibration]: Cat.Displayed.Cartesian.html

Since the proof that `Slices`{.Agda} is a cartesian fibration is given
by essentially rearranging the data of pullbacks in $\cB$, we also
have the converse implication: If $\underline{\cB}$ is a Cartesian
fibration, then $\cB$ has all pullbacks.

```agda
Codomain-fibration→pullbacks
  : ∀ {x y z} (f : Hom x y) (g : Hom z y)
  → Cartesian-fibration Slices
  → Pullback B f g
Codomain-fibration→pullbacks f g lifts = pb where
  open Pullback
  open is-pullback
  the-lift = lifts .has-lift f (cut g)

  pb : Pullback B f g
  pb .apex = the-lift .x′ .domain
  pb .p₁ = the-lift .x′ .map
  pb .p₂ = the-lift .lifting .to
  pb .has-is-pb .square = the-lift .lifting .commute
  pb .has-is-pb .limiting {p₁' = p₁'} {p₂'} p =
    the-lift .cartesian .universal {u′ = cut id}
      p₁' (slice-hom p₂' (pullr (idr _) ∙ p)) .to
  pb .has-is-pb .p₁∘limiting =
    sym (the-lift .cartesian .universal _ _ .commute) ∙ idr _
  pb .has-is-pb .p₂∘limiting = ap to (the-lift .cartesian .commutes _ _)
  pb .has-is-pb .unique p q = ap to $ the-lift .cartesian .unique
    (slice-hom _ (idr _ ∙ sym p)) (Slice-pathp refl q)
```

Since the fibres of the codomain fibration are given by slice
categories, then the interpretation of Cartesian fibrations as
"displayed categories whose fibres vary functorially" leads us to
reinterpret the above results as, essentially, giving the [pullback
functors] between slice categories.

[pullback functors]: Cat.Functor.Pullback.html
