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

open is-weak-cartesian
open Cocartesian-lift
open Cartesian-lift
open is-cocartesian
open is-cartesian
open is-pullback
open Displayed
open Pullback
open Functor
open /-Obj
```
-->

```agda
module Cat.Displayed.Instances.Slice where
```

<!--
```agda
module _ {o ℓ} (B : Precategory o ℓ) where
  open CR B
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
  private
    Ob[] : ⌞ B ⌟ → Type _
    Ob[] x = /-Obj {C = B} x

  record Slice-hom {x y} (f : Hom x y) (px : Ob[] x) (py : Ob[] y) : Type ℓ where
    no-eta-equality
    field
      map : Hom (px .dom) (py .dom)
      com : py ./-Obj.map ∘ map ≡ f ∘ px ./-Obj.map

  open Slice-hom public
```

<!--
```agda
{-# INLINE Slice-hom.constructor #-}
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
module
  _ {o ℓ} {B : Precategory o ℓ} (open Precategory B)
    {x y} {f g : Hom x y} {px : /-Obj x} {py : /-Obj y}
    {f' : Slice-hom B f px py} {g' : Slice-hom B g px py}
  where

  Slice-pathp : ∀ {p : f ≡ g} → f' .map ≡ g' .map → PathP (λ i → Slice-hom B (p i) px py) f' g'
  Slice-pathp {p = p} p' i .map = p' i
  Slice-pathp {p = p} p' i .com = is-prop→pathp
    (λ i → Hom-set _ _ (py .map ∘ p' i) (p i ∘ px .map))
    (f' .com) (g' .com) i

Slice-path
  : ∀ {o ℓ} {B : Precategory o ℓ} (open Precategory B)
  → ∀ {x y} {f : Hom x y} {px : /-Obj x} {py : /-Obj y}
  → {f' g' : Slice-hom B f px py}
  → (f' .map ≡ g' .map)
  → f' ≡ g'
Slice-path = Slice-pathp

unquoteDecl H-Level-Slice-hom = declare-record-hlevel 2 H-Level-Slice-hom (quote Slice-hom)

module _ {o ℓ} (B : Precategory o ℓ) where
  open CR B
```
-->

It's straightforward to piece together the objects of the (ordinary)
slice category and our displayed maps `Slice-hom`{.Agda} into a category
displayed over $\cB$.

```agda
  Slices : Displayed B (o ⊔ ℓ) ℓ
  Slices .Ob[_]            = /-Obj {C = B}
  Slices .Hom[_]           = Slice-hom B
  Slices .Hom[_]-set _ _ _ = hlevel 2
  Slices .id' = record where
    map = id
    com = id-comm

  Slices ._∘'_ {x = x} {y = y} {z = z} {f = f} {g = g} px py = record where
    com =
      z .map ∘ px .map ∘ py .map ≡⟨ extendl (px .com) ⟩
      f ∘ y .map ∘ py .map       ≡⟨ pushr (py .com) ⟩
      (f ∘ g) ∘ x .map           ∎
    map = px .map ∘ py .map

  Slices .idr' {f = f} f' = Slice-pathp (idr (f' .map))
  Slices .idl' {f = f} f' = Slice-pathp (idl (f' .map))
  Slices .assoc' {f = f} {g = g} {h = h} f' g' h' = Slice-pathp $
    assoc (f' .map) (g' .map) (h' .map)
  Slices .hom[_] p f' = record
    { map = f' .map
    ; com = f' .com ∙ ap₂ _∘_ p refl
    }
  Slices .coh[_] p f' = Slice-pathp refl
```

It's only slightly more annoying to show that a vertical map in the
canonical self-indexing is a map in the ordinary slice category which,
since the objects displayed over $x$ are _defined_ to be those of the
slice category $\cB/x$, gives an equivalence of categories between
the fibre $\underline{\cB}^*(x)$ and the slice $\cB/x$.

```agda
  Fibre→slice : ∀ {x} → Functor (Fibre Slices x) (Slice B x)
  Fibre→slice .F₀ x = x
  Fibre→slice .F₁ f ./-Hom.map = f .map
  Fibre→slice .F₁ f ./-Hom.com = f .com ∙ eliml refl
  Fibre→slice .F-id    = ext refl
  Fibre→slice .F-∘ f g = ext refl

  Fibre→slice-is-ff : ∀ {x} → is-fully-faithful (Fibre→slice {x = x})
  Fibre→slice-is-ff = is-iso→is-equiv λ where
    .is-iso.from hom → record where
      map = hom ./-Hom.map
      com = hom ./-Hom.com ∙ introl refl
    .is-iso.rinv x → ext refl
    .is-iso.linv x → Slice-pathp refl

  Fibre→slice-is-equiv : ∀ {x} → is-equivalence (Fibre→slice {x})
  Fibre→slice-is-equiv = is-precat-iso→is-equivalence $ record
    { has-is-ff  = Fibre→slice-is-ff
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
    : ∀ {x y x' y'} {f : Hom x y} {f' : Slice-hom B f x' y'}
    → is-cartesian Slices f f'
    → is-pullback B (x' .map) f (f' .map) (y' .map)
  cartesian→pullback {x} {y} {x'} {y'} {f} {f'} cart = pb where
    pb : is-pullback B (x' .map) f (f' .map) (y' .map)
    pb .square       = sym (f' .com)
    pb .universal p  = cart .universal _ record { com = sym p ∙ ap₂ _∘_ (intror refl) refl } .map
    pb .p₁∘universal = cart .universal _ _ .com ∙ eliml refl
    pb .p₂∘universal = ap map (cart .commutes _ _)
    pb .unique p q   = ap map $ cart .unique
      record { com = p ∙ introl refl }
      (Slice-pathp q)

  pullback→cartesian
    : ∀ {x y x' y'} {f : Hom x y} {f' : Slice-hom B f x' y'}
    → is-pullback B (x' .map) f (f' .map) (y' .map)
    → is-cartesian Slices f f'
  pullback→cartesian {x} {y} {x'} {y'} {f} {f'} pb = cart where
    module pb = is-pullback pb

    cart : is-cartesian Slices f f'
    cart .universal m h' .map = pb.universal (assoc _ _ _ ∙ sym (h' .com))
    cart .universal m h' .com  = pb.p₁∘universal
    cart .commutes m h' = Slice-pathp pb.p₂∘universal
    cart .unique m' x = Slice-pathp $ pb.unique (m' .com) (ap map x)
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
    : ∀ {x y x' y'} {f : Hom x y} {f' : Slice-hom B f x' y'}
    → is-weak-cartesian Slices f f'
    → is-pullback B (x' .map) f (f' .map) (y' .map)

  pullback→weak-cartesian
    : ∀ {x y x' y'} {f : Hom x y} {f' : Slice-hom B f x' y'}
    → is-pullback B (x' .map) f (f' .map) (y' .map)
    → is-weak-cartesian Slices f f'
```

<details>
<summary>The computation is essentially the same.</summary>

```agda
  weak-cartesian→pullback {x} {y} {x'} {y'} {f} {f'} cart = pb where
    pb : is-pullback B (x' .map) f (f' .map) (y' .map)
    pb .square       = sym (f' .com)
    pb .universal p  = cart .universal record{ com = sym p } .map
    pb .p₁∘universal = cart .universal _ .com ∙ eliml refl
    pb .p₂∘universal = apd (λ _ → Slice-hom.map) (cart .commutes _)
    pb .is-pullback.unique p q = ap Slice-hom.map $ cart .unique
      record{ com = p ∙ introl refl }
      (Slice-pathp q)

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
  Codomain-fibration pullbacks f y' = lift-f where
    module pb = Pullback (pullbacks f (y' .map))

    lift-f : Cartesian-lift Slices f y'
    lift-f .x' = cut pb.p₁
    lift-f .lifting .map = pb.p₂
    lift-f .lifting .com = sym pb.square
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
  Codomain-fibration→pullbacks f g slices-fib = pb where
    open Cartesian-fibration Slices slices-fib

    pb : Pullback B f g
    pb .apex = (f ^* cut g) .dom
    pb .p₁ = (f ^* cut g) .map
    pb .p₂ = π* f (cut g) .map
    pb .has-is-pb .square = sym (π* f (cut g) .com)
    pb .has-is-pb .universal {p₁' = p₁'} {p₂'} p =
      π*.universal {u' = cut id}
        p₁' record{ com = sym p ∙ intror refl } .map
    pb .has-is-pb .p₁∘universal =
      π*.universal _ _ .com ∙ elimr refl
    pb .has-is-pb .p₂∘universal = ap map (π*.commutes _ _)
    pb .has-is-pb .unique p q = ap map $ π*.unique
      record{ com = p ∙ intror refl } (Slice-path q)
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
  Codomain-opfibration f x' = lift-f where
    lift-f : Cocartesian-lift Slices f x'
    lift-f .y'      = cut (f ∘ x' .map)
    lift-f .lifting = record{ com = idr _ }
    lift-f .cocartesian .universal m h' = record where
      map = h' .map
      com = h' .com ∙ pullr refl
    lift-f .cocartesian .commutes m h' = Slice-pathp (idr _)
    lift-f .cocartesian .unique m' p   = Slice-pathp (sym (idr _) ∙ ap map p)
```
