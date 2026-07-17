<!--
```agda
open import Cat.Bi.Instances.Discrete
open import Cat.Displayed.Cartesian
open import Cat.Functor.Equivalence
open import Cat.Functor.Naturality
open import Cat.Instances.Discrete
open import Cat.Functor.Coherence
open import Cat.Bi.Functor.Base
open import Cat.Displayed.Fibre
open import Cat.Functor.Adjoint
open import Cat.Displayed.Base
open import Cat.Functor.Base
open import Cat.Bi.Duality renaming (_^op to _^opᵇ)
open import Cat.Groupoid
open import Cat.Bi.Base
open import Cat.Prelude

import Cat.Displayed.Cartesian.Indexing as Idx
import Cat.Displayed.Reasoning as Dr
import Cat.Functor.Reasoning as Fr
import Cat.Displayed.Total as Total
import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Bi.Functor.IndexedCategory where
```

# Indexed categories {defines="indexed-category"}

If $\ca{I}$ is any precategory, a [[pseudofunctor]] $F : \ca{I}\op \to
\Cat$ can be regarded as a family of categories $\{F(i)\}_{i : \ca{I}}$,
which varies "nicely" (i.e., functorially) in the index $i$.
Accordingly, such pseudofunctors go by the name of **indexed
categories**.

Of course, we can also consider covariant pseudofunctors $F : \ca{I} \to
\Cat$.  However, just like how [[contravariant functors into
$\Sets$|presheaf]] play a special role in category theory, so do
contravariant pseudofunctors into $\Cat$ in bicategory theory.  In other
words, we can think of an indexed category as a bicategorical presheaf.

```agda
module Indexed-category
  {o h o' h'}
  {I : Precategory o h}
  (F : Pseudofunctor (Locally-discrete (I ^op)) (Cat o' h'))
  where
```

## The Grothendieck construction {defines="grothendieck-construction"}

Indexed categories are typically studied under a different guise: as
[[cartesian fibrations]].  Each cartesian fibration over a base category
$\ca{I}$ [induces an indexed category] $F : \ca{I}\op \to \Cat$.  The
converse also holds, as we will now show.

[induces an indexed category]: Cat.Displayed.Cartesian.Indexing.html

<!--
```agda
  open Cartesian-lift
  open is-cartesian
  open Cr.Inverses
  open Functor
  open Cr._≅_
  open _=>_

  private
    module F          = Pf-reasoning F
    module I          = Precategory I
    module pg {x} {y} = is-pregroupoid (Disc! (I.Hom x y)) Disc-is-groupoid

    open module F₀ {x} = Cr (F.₀ x)

    p→i = Id≃path.from

  open F public hiding (left-unit ; right-unit ; hexagon)

  υ≅' : ∀ {A : I.Ob} {x : Ob {A}} → x ≅ F.₁ I.id .F₀ x
  υ≅' = isoⁿ→iso υ≅ _

  γ≅'
    : ∀ {A B C : I.Ob} {f : I.Hom B C} {g : I.Hom A B} {x : Ob {C}}
    → F.₁ g .F₀ (F.₁ f .F₀ x) ≅ F.₁ (f I.∘ g) .F₀ x
  γ≅' = isoⁿ→iso γ≅ _
```
-->

<details>
<summary>
First, we need a technical result related to a detail we glossed over so
far.  To regard $\ca{I}$ as a bicategory, we form the [[locally
discrete bicategory]] on $\ca{I}$.  This means our pseudofunctor $F$
acts not only on objects and morphisms in $\ca{I}$, but also on *paths
between the morphisms* in $\ca{I}$.  It turns out we can characterise
this action as follows using `path→iso`{.Agda}.
</summary>

```agda
  abstract
    P₁-path
      : ∀ {A B} {f g : I.Hom A B} {x} (p : f ≡ᵢ g)
      → F.₂ p .η x ≡ path→iso {C = F.₀ A} (ap (λ h → F.₁ h .F₀ x) (Id≃path.to p)) .to
    P₁-path {A} {x = x} p =
        sym (ap Cr._≅_.to (P₁.ap-F₀-iso Disc-is-category (pg.hom→iso p)) ηₚ x)
      ∙ Regularity.reduce!
```

</details>

<!--
```agda
    P₁-hom-pathp
      : ∀ {A B} {f g : I.Hom A B} {x y} {Ff Fg} (p : f ≡ g)
      → F.₂ (p→i p) .η y ∘ Ff ≡ Fg
      → PathP (λ i → Hom x (F₀ (F.₁ (p i)) y)) Ff Fg
    P₁-hom-pathp {A} {y = y} {Ff} p q = Hom-pathp-reflr (F.₀ A) (car p' ∙ q) where
      p' : path→iso {C = F.₀ A} (ap (λ h → F.₁ h .F₀ y) p) .to ≡ F.₂ (p→i p) .η y
      p' = sym
        $ P₁-path (p→i p)
        ∙ ap (λ p → path→iso {C = F.₀ A} (ap (λ h → F.₁ h .F₀ _) p) .to) (Id≃path.ε p)

    left-unit
      : ∀ {A B} (f : I.Hom A B) Fy
      → F.₂ (p→i (I.idr f)) .η Fy ∘ γ→ (I.id , f) .η Fy ∘ υ→ .η (F.₁ f .F₀ Fy) ≡ id
    left-unit f Fy = F.left-unit f ηₚ Fy

    right-unit
      : ∀ {A B} (f : I.Hom A B) Fy
      → F.₂ (p→i (I.idl f)) .η Fy ∘ γ→ (f , I.id) .η Fy ∘ F.₁ f .F₁ (υ→ .η Fy) ≡ id
    right-unit f Fy = F.right-unit f ηₚ Fy

    hexagon
      : ∀ {A B C D} (f : I.Hom C D) (g : I.Hom B C) (h : I.Hom A B) Fz
      → F.₂ (p→i (I.assoc f g h)) .η Fz ∘ γ→ ((g I.∘ h) , f) .η Fz ∘ γ→ (h , g) .η (F.₁ f .F₀ Fz)
      ≡ γ→ (h , (f I.∘ g)) .η Fz ∘ F.₁ h .F₁ (γ→ (g , f) .η Fz)
    hexagon f g h Fz = F.hexagon h g f ηₚ Fz ∙ cdr (idr _)

    right-unit-υr
      : ∀ {A B} (f : I.Hom A B) Fy
      → F.₂ (p→i (I.idl f)) .η Fy ∘ γ→ (f , I.id) .η Fy ≡ F.₁ f .F₁ (υ← .η Fy)
    right-unit-υr f Fy =
      cdr (intror (F-iso.F-map-iso (F.₁ f) υ≅' .invl)) ∙ cancell3 (right-unit f Fy)

    left-unit-υr-inv
      : ∀ {A B} (f : I.Hom A B) Fy
      → γ← (I.id , f) .η _ ∘ F.₂ (p→i (sym (I.idr _))) .η _ ≡ υ→ .η (F.₁ f .F₀ Fy)
    left-unit-υr-inv f Fy =
         intror (left-unit f Fy)
      ∙∙ cancel-inner (
           car (ap (λ p → F.₂ p .η Fy) prop!)
         ∙ P₁.F-map-iso (pg.hom→iso (p→i (I.idr f))) .invr ηₚ Fy
         )
      ∙∙ cancell (γ≅' .invr)
```
-->

We begin by building a displayed category over $\ca{I}$ using the data
of our indexed category.  This is known as the (contravariant)
**Grothendieck construction**.

<!--
TODO: Relax the premise to a lax functor for this part: we can construct
the displayed category even if we don't have an invertible unitor and
compositor.
-->

The idea will be to let the objects over $x : \ca{I}$ be given by the
objects of $F(x)$.

```agda
  displayed : Displayed I _ _
  displayed .Displayed.Ob[_] x = F₀.Ob {x}
```

A morphism over $f : x \to y$ should somehow connect an object
$a : F(x)$ to an object $b : F(y)$.  Since $F$ is contravariant, we have
a functor $F(f) : F(y) \to F(x)$, so we can consider morphisms $a \to
F(f)(b)$ in $F(x)$.

```agda
  displayed .Displayed.Hom[_] f a b     = F₀.Hom a (F.₁ f .F₀ b)
  displayed .Displayed.Hom[_]-set _ _ _ = hlevel 2
```

For $a : F(x)$, the identity morphism $\id : a \to a$ in our displayed
category should be a morphism $a \to F(\id)(a)$.  As it happens, this is
given by the components of $F$'s unitor, which has the form $\Id \to
F(\id)$.

```agda
  displayed .Displayed.id' = υ→ .η _
```

To compose morphisms $\phi : b \to F(f)(c)$ and $\psi : a \to F(g)(b)$
into $\phi \circ \psi : a \to F(f \circ g)(c)$ we follow a pattern
similar to monadic composition, as illustrated in the diagram below.
Note how the compositor $\gamma$ must be used in the final step.

~~~{.quiver}
\[\begin{tikzcd}[column sep=2.25em]
	a & {F(g)(b)} & {F(g)(F(f)(c))} \\
	&& {F(f\circ g)(c)}
	\arrow["\psi", from=1-1, to=1-2]
	\arrow["{\psi \circ \phi}"', color={rgb,255:red,92;green,92;blue,214}, curve={height=12pt}, from=1-1, to=2-3]
	\arrow["{F(g)(\phi)}", from=1-2, to=1-3]
	\arrow["{\gamma_{f,g,c}}", from=1-3, to=2-3]
\end{tikzcd}\]
~~~

```agda
  displayed .Displayed._∘'_ {g = g} ϕ ψ = γ→ _ .η _ ∘ F.₁ g .F₁ ϕ ∘ ψ
```

<details>
<summary>
Showing that the identity and composition satisfy the axioms of a
displayed category is a bit fiddly, and we leave the details here.  The
basic idea is that the identity axioms correspond to the unit identities
of $F$, and the associativity axiom corresponds to the hexagon identity
of $F$.  The lemma `P₁-hom-pathp`{.Agda} is derived from
`P₁-path`{.Agda} and lets us build dependent paths of the correct type
using $F$'s functorial action.
</summary>

```agda
  displayed .Displayed.idr' {y = b} {f} ϕ = P₁-hom-pathp (I.idr f) $
    F.₂ (p→i (I.idr f)) .η b ∘ γ→ _ .η b ∘ F.₁ I.id .F₁ ϕ ∘ υ→ .η _ ≡⟨ refl⟩∘⟨ refl⟩∘⟨ sym (υ→ .is-natural _ _ _) ⟩
    F.₂ (p→i (I.idr f)) .η b ∘ γ→ _ .η b ∘ υ→ .η _ ∘ ϕ              ≡⟨ cancell3 (left-unit f b) ⟩
    ϕ                                                               ∎
  displayed .Displayed.idl' {y = b} {f} ϕ = P₁-hom-pathp (I.idl f)
    $ cancell3 (right-unit f b)
  displayed .Displayed.assoc' {z = c} {f} {g} {h} ϕ₁ ϕ₂ ϕ₃ =
    P₁-hom-pathp (I.assoc f g h) $
      F.₂ (p→i (I.assoc f g h)) .η c ∘ γ→ _ .η c
    ∘ F.₁ (g I.∘ h) .F₁ ϕ₁ ∘ γ→ _ .η _ ∘ F.₁ h .F₁ ϕ₂ ∘ ϕ₃
      ≡⟨ refl⟩∘⟨ refl⟩∘⟨ extendl (sym $ γ→ _ .is-natural _ _ _) ⟩
      F.₂ (p→i (I.assoc f g h)) .η c ∘ γ→ _ .η c
    ∘ γ→ _ .η (F.₁ f .F₀ c) ∘ F.₁ h .F₁ (F.₁ g .F₁ ϕ₁) ∘ F.₁ h .F₁ ϕ₂ ∘ ϕ₃
      ≡⟨ pulll3 (hexagon f g h c) ∙ sym (assoc _ _ _) ⟩
    γ→ _ .η c ∘ F.₁ h .F₁ (γ→ _ .η c) ∘ F.₁ h .F₁ (F.₁ g .F₁ ϕ₁) ∘ F.₁ h .F₁ ϕ₂ ∘ ϕ₃
      ≡⟨ refl⟩∘⟨ Fr.pulll3 (F.₁ h) refl ⟩
    γ→ _ .η c ∘ F.₁ h .F₁ (γ→ _ .η c ∘ F.₁ g .F₁ ϕ₁ ∘ ϕ₂) ∘ ϕ₃
      ∎
  displayed .Displayed.hom[_] p ϕ = F.₂ (p→i p) .η _ ∘ ϕ
  displayed .Displayed.coh[_] p ϕ = P₁-hom-pathp p refl
```

</details>

<!--
```agda
  open Dr displayed

  cancel-id'
    : ∀ {x y} {g : I.Hom x y} {a b c}
    → {ϕ : Hom[ g ] b c} {ψ : F₀.Hom a b}
    → ϕ ∘' id' ∘ ψ ≡[ I.idr g ] ϕ ∘ ψ
  cancel-id' =
    cdr (extendl (sym $ υ→ .is-natural _ _ _) ∙ υ→ .is-natural _ _ _) ◁ idr' _
```
-->

With that out of the way, showing that our displayed category is a
fibration is a walk in the park.  Given a morphism $f : x \to y$ in
$\ca{I}$ and an object $b : F(y)$, we must construct a cartesian lift
$\phi : a \to b$, for some $a : F(x)$.  But since a morphism $a \to b$
in our displayed category is just a morphism $a \to F(f)(b)$ in $F(x)$,
we can choose $a$ to be $F(f)(b)$ and our lift to be the identity on
$a$.

```agda
  fibration : Cartesian-fibration displayed
  fibration f b .x'      = F₀ (F.₁ f) b
  fibration f b .lifting = id
```

Because we could choose our lift to be the identity, the lifting diagram
trivialises:

~~~{.quiver}
\[\begin{tikzcd}
	\textcolor{rgb,255:red,124;green,50;blue,189}{{a}} &&& \\
	& {F(f)(b)} && b \\
	\textcolor{rgb,255:red,124;green,50;blue,189}{u} \\
	& x && y
	\arrow["{{\exists!}}"', color={rgb,255:red,36;green,202;blue,28}, dashed, from=1-1, to=2-2]
	\arrow["{{h}}", color={rgb,255:red,204;green,51;blue,51}, curve={height=-12pt}, from=1-1, to=2-4]
	\arrow[lies over, color={rgb,255:red,124;green,50;blue,189}, from=1-1, to=3-1]
	\arrow["{{\id}}"', from=2-2, to=2-4]
	\arrow[lies over, from=2-2, to=4-2]
	\arrow[lies over, from=2-4, to=4-4]
	\arrow["m"', color={rgb,255:red,124;green,50;blue,189}, from=3-1, to=4-2]
	\arrow["f", from=4-2, to=4-4]
\end{tikzcd}\]
~~~

Here, we are given $ϕ : a \to b$ lying over $f \circ m$, which by the
definition above is a morphism $ϕ : a \to F(f \circ m)(b)$ in $F(u)$,
and must produce a unique morphism $a \to F(m)(F(f)(b))$.  But we can
just use $ϕ$ itself, using the compositor $\gamma$ to go from
$F(f \circ m)$ to $F(m)F(f)$.[^pseudo]

[^pseudo]: Here we use that $F$ is actually a pseudofunctor and not just
a lax functor, since we require the inverse of the compositor.

```agda
  fibration f b .cartesian .universal m ϕ = γ← (m , f) .η b ∘ ϕ
  fibration f b .cartesian .commutes m ϕ  =
    cdr (eliml (F.₁ m .F-id)) ∙ cancell (γ≅' .invl)
  fibration f b .cartesian .unique {m = m} m' p =
    sym (cdr p) ∙ cancell3 (cancell (γ≅' .invr) ∙ F.₁ m .F-id)
```

## Fibre categories of the Grothendieck construction

The fibre categories of the `displayed`{.Agda} category we just built
admit a particularly clean description: the fibre at $x : \ca{I}$ is
$F(x)$.  This is more or less definitional, but to construct functors
both ways we do need to utilise $F$'s pseudofunctoriality.

```agda
  fibre-equiv-to : ∀ {x} → Functor (F.₀ x) (Fibre displayed x)
  fibre-equiv-to .F₀ a    = a
  fibre-equiv-to .F₁ ϕ    = υ→ .η _ ∘ ϕ
  fibre-equiv-to .F-id    = idr _
  fibre-equiv-to .F-∘ ϕ ψ = from-pathp[]⁻ $ assoc _ _ _ ◁ cast[] (symP cancel-id')

  fibre-equiv-from : ∀ {x} → Functor (Fibre displayed x) (F.₀ x)
  fibre-equiv-from .F₀ a            = a
  fibre-equiv-from .F₁ ϕ            = υ← .η _ ∘ ϕ
  fibre-equiv-from .F-id            = isoⁿ→iso υ≅ _ .invr
  fibre-equiv-from .F-∘ {z = c} ϕ ψ =
    υ← .η c ∘ F.₂ (p→i (I.idl I.id)) .η c ∘ ϕ ∘' ψ        ≡⟨ refl⟩∘⟨ pulll (right-unit-υr I.id _) ⟩
    υ← .η c ∘ F.₁ I.id .F₁ (υ← .η _) ∘ F.₁ I.id .F₁ ϕ ∘ ψ ≡⟨ cdr (Fr.pulll (F.₁ I.id) refl) ∙ extendl (υ← .is-natural _ _ _) ⟩
    (υ← .η c ∘ ϕ) ∘ υ← .η _ ∘ ψ                           ∎
```

<details>
<summary>
Showing that `fibre-equiv-to`{.Agda} and `fibre-equiv-from`{.Agda} form an
[[equivalence of categories]] is straightforward, and we elide the
details.
</summary>

```agda
  fibre-equiv⊣ : ∀ {x} → fibre-equiv-to {x} ⊣ fibre-equiv-from
  fibre-equiv⊣ ._⊣_.unit .η _                = id
  fibre-equiv⊣ ._⊣_.unit .is-natural _ _ _   =
    idl _ ∙∙ insertl (υ≅' .invr) ∙∙ sym (idr _)
  fibre-equiv⊣ ._⊣_.counit .η _              = id'
  fibre-equiv⊣ ._⊣_.counit .is-natural _ _ f = cdr
    $ cast[] (cancel-id' ∙[] cancell (υ≅' .invl) ∙[] symP (idr' _))
  fibre-equiv⊣ ._⊣_.zig = from-pathp[] (idl' _) ∙ idr _
  fibre-equiv⊣ ._⊣_.zag = eliml (υ≅' .invr)

  fibre-equiv : ∀ {x} → Equivalence (F.₀ x) (Fibre displayed x)
  fibre-equiv .Equivalence.To                             = fibre-equiv-to
  fibre-equiv .Equivalence.To-equiv .is-equivalence.F⁻¹   = fibre-equiv-from
  fibre-equiv .Equivalence.To-equiv .is-equivalence.F⊣F⁻¹ = fibre-equiv⊣
  fibre-equiv .Equivalence.To-equiv .is-equivalence.has-is-equivalence =
    record where
      unit-iso   _ = id-invertible
      counit-iso _ = Cr.id-invertible (Fibre displayed _)
```

</details>

<!--
```agda
  open Idx displayed fibration
```
-->

Furthermore, under this equivalence, the `base-change`{.Agda} functors
coincide with $F$'s functorial action.  Formally, we have a commutative
square of functors holding up to natural isomorphism.

```agda
  fibration-base-change
    : ∀ {x y} (f : I.Hom x y)
    → fibre-equiv-to F∘ F.₁ f ≅ⁿ base-change f F∘ fibre-equiv-to
```

Recalling that `fibre-equiv-to`{.Agda} is the identity on objects, and
that `base-change`{.Agda} acts by taking cartesian lifts, which in our
case is just given by the action of $F$, we can choose the components of
this natural isomorphism to be identities.

```agda
  fibration-base-change f = to-natural-iso ni where
    ni : make-natural-iso _ _
    ni .make-natural-iso.eta a = id'
    ni .make-natural-iso.inv a = id'
```

<details>
<summary>
What remains is verifying that both sides act identically on morphisms.
The proof comes down to fiddly displayed reasoning and is not very
enlightening.
</summary>

```agda
    ni .make-natural-iso.eta∘inv a     = from-pathp[] $ idl' id'
    ni .make-natural-iso.inv∘eta a     = from-pathp[] $ idl' id'
    ni .make-natural-iso.natural _ b ϕ = cdr $ cast[] (idr' _ ∙[] p ∙[] symP (idl' _))
      where
        p : (base-change f F∘ fibre-equiv-to) .F₁ ϕ ≡ (fibre-equiv-to F∘ F.₁ f) .F₁ ϕ
        p =
          γ← (I.id , f) .η b ∘ hom[ sym (Cr.id-comm I) ] (γ→ (f , I.id) .η b ∘ _)  ≡⟨ refl⟩∘⟨ pushl (ap (λ p → F.₂ p .η b) prop! ∙ P₁.F-∘ _ _ ηₚ b) ⟩
          γ← (I.id , f) .η b ∘ F.₂ (p→i (sym (I.idr _))) .η _ ∘ hom[ I.idl _ ] _   ≡⟨ pulll (left-unit-υr-inv f b) ⟩
          υ→ .η _ ∘ hom[ I.idl _ ] (γ→ (f , I.id) .η _ ∘ F.₁ f .F₁ (id' ∘ ϕ) ∘ id) ≡⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ idr _ ∙ F.₁ f .F-∘ _ _ ⟩
          _ ∘ hom[ I.idl _ ] (id' ∘' F.₁ f .F₁ ϕ)                                  ≡⟨ refl⟩∘⟨ from-pathp[] (idl' _) ⟩
          υ→ .η _ ∘ F.₁ f .F₁ ϕ                                                    ∎
```

</details>

## Total category of the Grothendieck construction

<!--
```agda
  private
    ιᶠ'                  = Total.ιᶠ displayed
    ιᶠ-base-change-comp' = Total.ιᶠ-base-change-comp displayed fibration
```
-->

As with any `displayed`{.Agda} category, we can pass to the total
category, which bundles objects $x : \ca{I}$ with objects $a : F(x)$
lying over $x$, and morphisms $f : x \to y$ with morphisms $\phi : a \to
F(f)(b)$ lying over $f$.  Typically, we denote this total category
directly as $\int F$.  Recalling that an indexed category is a
bicategorical presheaf, the similarity to the notation for the
[[category of elements]] of a presheaf is not a coincidence.

```agda
  ∫ : Precategory _ _
  ∫ = Total.∫ displayed
```

We also get canonical inclusions from each fibre category $F(x)$ into
the total category $\int F$.

```agda
  ιᶠ : (x : I.Ob) → Functor (F.₀ x) ∫
  ιᶠ x = ιᶠ' x F∘ fibre-equiv-to
```

<!--
```agda
  -- We specialize the construction from Cat.Displayed.Total to avoid unnecessary
  -- identity morphisms.
  ιᶠ-base-change : ∀ {a b} (f : I.Hom a b) → ιᶠ a F∘ F.₁ f => ιᶠ b
  ιᶠ-base-change f .η x              = Total.∫hom f id
  ιᶠ-base-change f .is-natural x y g =
    Total.∫Hom-path displayed (Cr.id-comm I) $ begin[]
      id ∘' id' ∘ F.₁ f .F₁ g                           ≡[]⟨ cancel-id' ∙[] idl _ ∙[] symP (idl' _) ⟩
      id' ∘' F.₁ f .F₁ g                                ≡[]˘⟨ cdr (idr _ ∙ F.₁ f .F-∘ _ _) ⟩
      γ→ (f , I.id) .η y ∘ F.₁ f .F₁ (υ→ .η y ∘ g) ∘ id ∎[]

  ιᶠ-base-change-comp
    : ∀ {a b c} (f : I.Hom b c) (g : I.Hom a b)
    → ιᶠ-base-change (f I.∘ g)
    ≡ ιᶠ-base-change f
    ∘nt nat-unassoc-from (ιᶠ-base-change g ◂ F.₁ f)
    ∘nt (ιᶠ a ▸ γ← (g , f))
  ιᶠ-base-change-comp f g = ext λ i →
      ιᶠ-base-change-comp' f g ηₚ i
    ∙ (
      Cr.cddr ∫ $ Total.∫Hom-path _ refl $ pulll (left-unit-υr-inv g _) ∙ cdr (idr _)
    )

open Pseudofunctor

module IndexedOplax
  {o h o' h'}
  {I : Precategory o h}
  {F G : Pseudofunctor (Locally-discrete (I ^op) ^opᵇ) (Cat o' h' ^opᵇ)}
  (α : G .lax =>ₗ F .lax)
  where

  open Functor
  open _=>_

  private
    module I = Precategory I
    module F = Pseudofunctor F
    module G = Pseudofunctor G
    module α = _=>ₗ_ α
    open module G₀ {x} = Cr (G.₀ x)

  open α hiding (ν-compositor ; ν-unitor) public

  ν-compositor
    : ∀ {a b c : I.Ob} (f : I.Hom b c) (g : I.Hom a b) Fx
    → η (α.ν→ (f I.∘ g)) Fx ∘ F₁ (α.σ a) (F.γ→ (f , g) .η Fx)
    ≡ G.γ→ (f , g) .η (σ c .F₀ Fx) ∘ G.₁ g .F₁ (ν→ f .η Fx) ∘ ν→ g .η _
  ν-compositor f g Fx = α.ν-compositor f g ηₚ Fx ∙ cdr (idl _ ∙ cdr (idl _ ∙ idr _))

  ν-unitor : ∀ {a : I.Ob} Fx → ν→ I.id .η _ ∘ σ a .F₁ (F.υ→ .η Fx) ≡ G.υ→ .η _
  ν-unitor Fx = α.ν-unitor ηₚ Fx ∙ elimr (idl _)
```
-->
