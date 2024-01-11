<!--
```agda
open import Cat.Displayed.Cartesian.Weak
open import Cat.Displayed.Cocartesian
open import Cat.Displayed.Cartesian
open import Cat.Functor.Equivalence
open import Cat.Functor.Properties
open import Cat.Diagram.Pullback
open import Cat.Displayed.Fibre
open import Cat.Instances.Slice
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Reasoning as CR
```
-->

```agda
module Cat.Displayed.Instances.Slice {o ℓ} (B : Precategory o ℓ) where
```

<!--
```agda
open Cartesian-fibration
open Cartesian-lift
open Displayed
open is-cartesian
open is-weak-cartesian
open Functor
open CR B
open /-Obj
```
-->

# The canonical self-indexing {defines="canonical-self-indexing fundamental-fibration codomain-fibration"}

There is a canonical way of viewing any category $\cB$ as displayed over
_itself_, given [[fibrewise|fibre categories]] by taking [slice
categories]. Following [@relativect], we refer to this construction as
the **canonical self-indexing** of $\cB$ and denote it
$\underline{\cB}$. Recall that the objects in the slice over $y$ are
pairs consisting of an object $x$ and a map $f : x \to y$. The core idea
is that _any morphism_ lets us view an object $x$ as being "structure
over" an object $y$; the collection of all possible such structures,
then, is the set of morphisms $x \to y$, with domain allowed to vary.

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
    : Type ℓ
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
_reindexing_, which takes an $Y$-family of sets to a $X$-family of sets
([in a functorial way]). A morphism $X' \to Y'$ in the canonical
self-indexing of $\Sets$ lying over a map $f : X \to Y$ is then a
function between the families $X' \to Y'$ which commutes with the
reindexing given by $f$.

[in a functorial way]: Cat.Instances.Slice.html#slices-of-sets

<!--
```agda
module _ {x y} {f g : Hom x y} {px : /-Obj x} {py : /-Obj y}
         {f' : Slice-hom f px py} {g' : Slice-hom g px py} where

  Slice-pathp : (p : f ≡ g) → (f' .to ≡ g' .to) → PathP (λ i → Slice-hom (p i) px py) f' g'
  Slice-pathp p p' i .to = p' i
  Slice-pathp p p' i .commute =
    is-prop→pathp
      (λ i → Hom-set _ _ (p i ∘ px .map) (py .map ∘ (p' i)))
      (f' .commute)
      (g' .commute)
      i

Slice-path
  : ∀ {x y} {f : Hom x y} {px : /-Obj x} {py : /-Obj y}
  → {f' g' : Slice-hom f px py}
  → (f' .to ≡ g' .to)
  → f' ≡ g'
Slice-path = Slice-pathp refl

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
Slices : Displayed B (o ⊔ ℓ) ℓ
Slices .Ob[_] = /-Obj {C = B}
Slices .Hom[_] = Slice-hom
Slices .Hom[_]-set = Slice-is-set
Slices .id' = slice-hom id id-comm-sym
Slices ._∘'_ {x = x} {y = y} {z = z} {f = f} {g = g} px py =
  slice-hom (px .to ∘ py .to) $
    (f ∘ g) ∘ x .map           ≡⟨ pullr (py .commute) ⟩
    f ∘ (y .map ∘ py .to)      ≡⟨ extendl (px .commute) ⟩
    z .map ∘ (px .to ∘ py .to) ∎
Slices .idr' {f = f} f' = Slice-pathp (idr f) (idr (f' .to))
Slices .idl' {f = f} f' = Slice-pathp (idl f) (idl (f' .to))
Slices .assoc' {f = f} {g = g} {h = h} f' g' h' =
  Slice-pathp (assoc f g h) (assoc (f' .to) (g' .to) (h' .to))
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
Fibre→slice .F-id = trivial!
Fibre→slice .F-∘ f g = ext (transport-refl _)

Fibre→slice-is-ff : ∀ {x} → is-fully-faithful (Fibre→slice {x = x})
Fibre→slice-is-ff {_} {x} {y} = is-iso→is-equiv isom where
  isom : is-iso (Fibre→slice .F₁)
  isom .is-iso.inv hom =
    slice-hom (hom ./-Hom.map) (eliml refl ∙ sym (hom ./-Hom.commutes))
  isom .is-iso.rinv x = ext refl
  isom .is-iso.linv x = Slice-pathp refl refl

Fibre→slice-is-equiv : ∀ {x} → is-equivalence (Fibre→slice {x})
Fibre→slice-is-equiv = is-precat-iso→is-equivalence $
  record { has-is-ff = Fibre→slice-is-ff
         ; has-is-iso = id-equiv
         }
```

## Cartesian maps

A map $f' : x' \to y'$ over $f : x \to y$ in the codomain fibration is
[[cartesian|cartesian map]] if and only if it forms a pullback square as below:

~~~{.quiver}
\begin{tikzcd}
  {x'} && {y'} \\
  \\
  x && y
  \arrow["f"', from=3-1, to=3-3]
  \arrow["g"', from=1-1, to=3-1]
  \arrow["{f'}", from=1-1, to=1-3]
  \arrow["h", from=1-3, to=3-3]
\end{tikzcd}
~~~

This follows by a series of relatively straightforward computations, so
we do not comment too heavily on the proof.

```agda
cartesian→pullback
  : ∀ {x y x' y'} {f : Hom x y} {f' : Slice-hom f x' y'}
  → is-cartesian Slices f f'
  → is-pullback B (x' .map) f (f' .to) (y' .map)
cartesian→pullback {x} {y} {x'} {y'} {f} {f'} cart = pb where
  pb : is-pullback B (x' .map) f (f' .to) (y' .map)
  pb .is-pullback.square = f' .commute
  pb .is-pullback.universal p =
    cart .universal _ (slice-hom _ (idr _ ∙ p)) .to
  pb .is-pullback.p₁∘universal =
    sym (cart .universal _ _ .commute) ∙ idr _
  pb .is-pullback.p₂∘universal =
    ap Slice-hom.to (cart .commutes _ _)
  pb .is-pullback.unique p q =
    ap Slice-hom.to (cart .unique (slice-hom _ (idr _ ∙ sym p)) (Slice-pathp refl q))

pullback→cartesian
  : ∀ {x y x' y'} {f : Hom x y} {f' : Slice-hom f x' y'}
  → is-pullback B (x' .map) f (f' .to) (y' .map)
  → is-cartesian Slices f f'
pullback→cartesian {x} {y} {x'} {y'} {f} {f'} pb = cart where
  module pb = is-pullback pb

  cart : is-cartesian Slices f f'
  cart .universal m h' .to = pb.universal (assoc _ _ _ ∙ h' .commute)
  cart .universal m h' .commute = sym pb.p₁∘universal
  cart .commutes m h' = Slice-pathp refl pb.p₂∘universal
  cart .unique m' x = Slice-pathp refl $
    pb.unique (sym (m' .commute)) (ap to x)
```

<!--
```agda
_ = weak-cartesian→cartesian
```
-->

We can actually weaken the hypothesis of `cartesian→pullback`{.Agda}
so that pullback squares also exactly characterise [[weakly cartesian morphisms]].
While this is automatic if $\cB$ has all pullbacks (since then cartesian and
weakly cartesian morphisms `coincide`{.Agda ident="weak-cartesian→cartesian"}),
it is sometimes useful to have both characterisations if we do not want to
make such an assumption.

```agda
weak-cartesian→pullback
  : ∀ {x y x' y'} {f : Hom x y} {f' : Slice-hom f x' y'}
  → is-weak-cartesian Slices f f'
  → is-pullback B (x' .map) f (f' .to) (y' .map)

pullback→weak-cartesian
  : ∀ {x y x' y'} {f : Hom x y} {f' : Slice-hom f x' y'}
  → is-pullback B (x' .map) f (f' .to) (y' .map)
  → is-weak-cartesian Slices f f'
```

<details>
<summary>The computation is essentially the same.</summary>

```agda
weak-cartesian→pullback {x} {y} {x'} {y'} {f} {f'} cart = pb where
  pb : is-pullback B (x' .map) f (f' .to) (y' .map)
  pb .is-pullback.square = f' .commute
  pb .is-pullback.universal p =
    cart .universal (slice-hom _ p) .to
  pb .is-pullback.p₁∘universal =
    sym (cart .universal _ .commute) ∙ idl _
  pb .is-pullback.p₂∘universal =
    apd (λ _ → Slice-hom.to) (cart .commutes _)
  pb .is-pullback.unique p q =
    ap Slice-hom.to (cart .unique (slice-hom _ (idl _ ∙ sym p)) (Slice-pathp (idr _) q))

pullback→weak-cartesian pb = cartesian→weak-cartesian _ (pullback→cartesian pb)
```
</details>

## As a fibration

If (and only if) $\cB$ has all [[pullbacks]], then its self-indexing is
a [[Cartesian fibration]]. This is almost by definition, and is in fact
where the "Cartesian" in "Cartesian fibration" comes from (recall that another term
for "pullback square" is "cartesian square"). Since the total space
$\int \underline{\cB}$ is equivalently the arrow category of $\cB$, with
the projection functor $\pi : \int \underline{\cB} \to \cB$
corresponding under this equivalence to the codomain functor, we refer
to $\underline{\cB}$ regarded as a Cartesian fibration as the
**codomain fibration**.

```agda
Codomain-fibration
  : (∀ {x y z} (f : Hom x y) (g : Hom z y) → Pullback B f g)
  → Cartesian-fibration Slices
Codomain-fibration pullbacks .has-lift f y' = lift-f where
  module pb = Pullback (pullbacks f (y' .map))

  lift-f : Cartesian-lift Slices f y'
  lift-f .x' = cut pb.p₁
  lift-f .lifting .to = pb.p₂
  lift-f .lifting .commute = pb.square
  lift-f .cartesian = pullback→cartesian pb.has-is-pb
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
  module the-lift = Cartesian-lift (lifts .has-lift f (cut g))

  pb : Pullback B f g
  pb .apex = the-lift.x' .domain
  pb .p₁ = the-lift.x' .map
  pb .p₂ = the-lift.lifting .to
  pb .has-is-pb .square = the-lift.lifting .commute
  pb .has-is-pb .universal {p₁' = p₁'} {p₂'} p =
    the-lift.cartesian .universal {u' = cut id}
      p₁' (slice-hom p₂' (pullr (idr _) ∙ p)) .to
  pb .has-is-pb .p₁∘universal =
    sym (the-lift.universal _ _ .commute) ∙ idr _
  pb .has-is-pb .p₂∘universal = ap to (the-lift.cartesian .commutes _ _)
  pb .has-is-pb .unique p q = ap to $ the-lift.cartesian .unique
    (slice-hom _ (idr _ ∙ sym p)) (Slice-pathp refl q)
```

Since the fibres of the codomain fibration are given by slice
categories, then the interpretation of Cartesian fibrations as
"[[displayed categories]] whose fibres vary functorially" leads us to
reinterpret the above results as, essentially, giving the [[pullback
functors]] between slice categories.

## As an opfibration

The canonical self-indexing is *always* an opfibration, where
opreindexing is given by postcomposition. If we think about slices as
families, then opreindexing along $X \to Y$ extends a family over $X$
to a family over $Y$ by adding in empty fibres for all elements of $Y$
that do not lie in the image of $f$.

```agda
Codomain-opfibration : Cocartesian-fibration Slices
Codomain-opfibration .Cocartesian-fibration.has-lift f x' = lift-f where

  lift-f : Cocartesian-lift Slices f x'
  lift-f .Cocartesian-lift.y' = cut (f ∘ x' .map)
  lift-f .Cocartesian-lift.lifting = slice-hom id (sym (idr _))
  lift-f .Cocartesian-lift.cocartesian .is-cocartesian.universal m h' =
    slice-hom (h' .to) (assoc _ _ _ ∙ h' .commute)
  lift-f .Cocartesian-lift.cocartesian .is-cocartesian.commutes m h' =
    Slice-pathp refl (idr _)
  lift-f .Cocartesian-lift.cocartesian .is-cocartesian.unique m' p =
    Slice-pathp refl (sym (idr _) ∙ ap to p)
```
