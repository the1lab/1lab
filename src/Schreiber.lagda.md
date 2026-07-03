---
description: |
  A reading guide to Urs Schreiber's "Higher Topos Theory in Physics",
  mapping its diagrams to their constructive formalisations, with a
  worked example of compiling a physical system to any topos.
---
<!--
```agda
open import Cat.CartesianClosed.Functor
open import Cat.Instances.Sets.Closed
open import Cat.Instances.SimplicialSets.Nerve
open import Cat.Instances.Presheaf.Exponentials
open import Cat.Instances.Sheaf.Limits.Finite
open import Cat.Instances.Sets.Complete
open import Cat.Instances.SimplicialSets
open import Cat.Instances.Localisation
open import Cat.Instances.Sheaves
open import Cat.Instances.Simplex
open import Cat.Diagram.Exponential
open import Cat.Functor.Hom.Yoneda
open import Cat.Functor.Hom
open import Cat.Functor.Base
open import Cat.Site.Base
open import Cat.Cartesian
open import Cat.Prelude

open import Cat.CartesianClosed.Free.Signature

open import Data.Set.Projective
open import Data.Set.Surjection
open import Data.Int.Base using (Int ; _+ℤ_)
open import Data.Bool

open import Homotopy.Space.Delooping

open import Topoi.Base

import Cat.CartesianClosed.Free.Model
import Cat.Morphism

open λ-Signature
open Functor
```
-->

```agda
module Schreiber where
```

# Higher topos theory in physics

This page maps the numbered diagrams and constructions of Urs
Schreiber's encyclopedia survey *Higher Topos Theory in Physics*
[@Schreiber:HTTPhysics] to their formalisations in the 1Lab. Two
warnings are in order. First, the 1Lab is resolutely *constructive*:
where the paper works over the site of smooth Cartesian spaces
$\bR^n$ — whose classical theory of smooth functions is not available
to us — we work over an *arbitrary* site, which is exactly the level
of generality at which the paper's topos-theoretic arguments live.
Second, the higher part of the story ($\infty$-topoi proper) remains
largely future work; the final section collects what is missing.

## Probes, plots and gluing

The starting point of the paper (its diagram (1)) is that physical
spaces are known by how we may *probe* them: maps compose, and
composition is associative and unital. This is the definition of a
[[precategory]]. A space $X$ probe-able by the objects of a category
$\cC$ of "shapes" assigns to each shape $U$ a set
$\rm{Plt}(U, X)$ of plots, contravariantly functorially — the paper's
boxed condition (1.), *precomposition of plots*, says exactly that
$\rm{Plt}(-, X)$ is a presheaf. Boxed condition (3.),
*postcomposition*, says that maps of such spaces are [[natural
transformations]].

```agda
_ = Precategory
_ = Functor
_ = _=>_
```

Boxed condition (2.), *gluing of plots*, is the sheaf condition for a
[[coverage]] on the category of shapes: a family of plots on the
patches of a cover, compatible on overlaps, glues to a unique global
plot. In the 1Lab this is the theory of [[sites|site]]: a
`Coverage`{.Agda} equips $\cC$ with covering sieves, a
`Patch`{.Agda} is a compatible family, a `Section`{.Agda} is a
gluing, and `is-sheaf`{.Agda} says every patch over every covering
sieve has a contractible space of sections.

```agda
_ = Coverage
_ = Patch
_ = Cat.Site.Base.Section
_ = is-sheaf
```

## The gros topos of generalized spaces

The paper's (2) defines the category of smooth sets as sheaves inside
presheaves, $\rm{SmthSet} := \rm{Sh}(\rm{CrtSp}) \mono
\rm{PSh}(\rm{CrtSp})$, and (8) recalls that such categories of
sheaves on a site are exactly the **Grothendieck topoi**. Both layers
exist here, over any site: the category `Sh[ C , J ]`{.Agda
ident=Sh[_,_]} of sheaves, the fully faithful inclusion into
presheaves, and its left exact left adjoint, [[sheafification]]. The
notion of [[topos]] as a lex-reflective subcategory of presheaves,
together with geometric morphisms `Geom[_,_]`{.Agda}, is in
`Topoi.Base`{.Agda}.

```agda
_ = Sh[_,_]
_ = forget-sheaf
_ = Sheafification⊣ι
_ = Topos
_ = Geom[_,_]
```

The embedding (3) of the site itself into its topos of spaces, and
the resulting tautology (4) — maps out of a representable are plots,
$\hom(\bR^n, X) \simeq \rm{Plt}(\bR^n, X)$ — are the [[Yoneda
embedding]] and the [[Yoneda lemma]].

```agda
_ = よ
_ = よ-is-fully-faithful
_ = yo
_ = yo-is-equiv
```

The paper's (7) presents the sheaf topos as a *localisation* of the
presheaf topos at the local isomorphisms. The 1Lab has the general
localisation of a category at a class of maps, as a higher inductive
type with the full universal property; the identification of
$\rm{Sh}(\cC)$ with $L^{\rm{liso}}\rm{PSh}(\cC)$ is future work, as
is the theory of *germs* of plots ((5), (6)).

```agda
_ = Localisation
```

## Fields and mapping spaces

Diagram (9) reads a field configuration as a map $\Phi : X \to F$
from spacetime to a space of field values — simply a morphism in the
topos. Diagram (10) is the heart of variational physics: the space
of *all* field configurations exists as a smooth set, the
**mapping space** $\rm{Maps}(X, F)$, characterised by the
[[exponential|exponential object]] adjunction: plots $U \to
\rm{Maps}(X, F)$ are maps $U \times X \to F$. Constructively and in
full generality: [[Sets is cartesian closed|sets-is-cartesian-closed]],
presheaf categories are [[cartesian closed]], and sheaf topoi are an
exponential ideal inside them.

```agda
_ = Sets-closed
_ = PSh-closed
_ = Sh[]-closed
_ = product⊣exponential
```

## Choice, constructively

The section-of-an-epimorphism diagram in the paper illustrates how
topos-internal logic differs from classical logic: the axiom of
choice — every epi $E \epi B$ has a section $\sigma$ — fails for
smooth sets ($\bR \epi \bR/\bZ$ has no continuous section). In the
1Lab even the base topos of sets is choice-free, so the phenomenon
is visible one level earlier: epimorphisms of sets are precisely the
[[surjections]], and the sets all of whose surjections split are the
[[projective|set-projective]] ones — assuming *every* set is
projective is exactly assuming the axiom of choice, which we neither
assume nor refute.

```agda
_ = Cat.Morphism.is-epic
_ = Cat.Morphism.has-section
_ = epi→surjective
_ = surjective→regular-epi
_ = is-set-projective
_ = set-surjections-split
```

## The constructive simulator: compiling physics to categories

The deepest structural point of the paper is that all these
"variable" contexts — sets, smooth sets, formal smooth sets, super
smooth sets — share the same *internal language*. A physical system
specified once, by operations on abstract types, makes sense in every
one of them. The 1Lab expresses this as [[compiling to
categories|compiling-to-categories]]: a [[λ-signature]] of base types
and operations freely generates a [[cartesian closed category]] of
programs, and any [[model|model-of-a-lambda-signature]] of the
signature in a cartesian closed category $\cC$ extends to a functor
$\Syn \to \cC$ preserving all the structure.

As a demonstration, here is a complete (if small) physical system: a
**heliostat** — a mirror that tracks the sun so that the reflected
ray hits a fixed target. The signature has two base types, `angle`
and `time`, and two operations: the sun's azimuth as a function of
time, and the aiming law. (Measuring time so that the sun moves at
unit speed, and angles in half-units, both operations are exactly
*addition*: the mirror normal must bisect the sun and target
directions.)

```agda
data Heliostat-type : Type where
  angle time : Heliostat-type

data Heliostat-op
  : types.Ty Heliostat-type → Heliostat-type → Type where
  sun-at : Heliostat-op (` time) angle
  aim    : Heliostat-op (` angle `× ` angle) angle
```

<!--
```agda
private
  Heliostat-type-is-set : is-set Heliostat-type
  Heliostat-type-is-set = retract→is-hlevel 2 dec enc ret (hlevel 2) where
    enc : Heliostat-type → Bool
    enc angle = true
    enc time = false

    dec : Bool → Heliostat-type
    dec true = angle
    dec false = time

    ret : ∀ x → dec (enc x) ≡ x
    ret angle = refl
    ret time = refl

  Heliostat-op-is-prop : ∀ {τ b} → is-prop (Heliostat-op τ b)
  Heliostat-op-is-prop sun-at sun-at = refl
  Heliostat-op-is-prop aim aim = refl
```
-->

```agda
Heliostat : λ-Signature lzero
Heliostat .Ob = Heliostat-type
Heliostat .Ob-is-set = Heliostat-type-is-set
Heliostat .Hom = Heliostat-op
Heliostat .Hom-is-set = is-prop→is-set Heliostat-op-is-prop
```

<!--
```agda
open import Cat.CartesianClosed.Free Heliostat
open import Cat.CartesianClosed.Free.Lambda Heliostat
```
-->

The controller is a *program* in the [[simply-typed lambda
calculus|STLC]] over this signature: given the time and the target
direction, point the mirror at the bisector of the current sun
position and the target.

```agda
mirror-program : Expr (∅ , ` time `× ` angle) (` angle)
mirror-program =
  `hom aim `⟨ `hom sun-at (`π₁ (`var stop)) , `π₂ (`var stop) ⟩
```

To *run* it, interpret the signature in the topos of sets: both base
types become the integers, and both operations become what they
always were, addition.

```agda
private
  module SetsModel = Cat.CartesianClosed.Free.Model Heliostat
    (Sets-cartesian {ℓ = lzero}) Sets-closed

heliostat-interp
  : elim.base-method
      SetsModel.chaotic-cartesian SetsModel.chaotic-closed
      (λ _ → el! Int)
heliostat-interp sun-at = λ t → t
heliostat-interp aim = λ (s , t) → s +ℤ t

private
  module Run = SetsModel.model (λ _ → el! Int) heliostat-interp

run-heliostat : Lift lzero ⊤ × Int × Int → Int
run-heliostat = Run.compile .F₁ ⟦ mirror-program ⟧ᵉ
```

The compiled controller is an honest function, and it *computes*: at
time $2$, aiming at target direction $3$, the mirror should sit at
$5$ — and this is so definitionally, by `refl`{.Agda}.

```agda
_ : run-heliostat (lift tt , 2 , 3) ≡ 5
_ = refl
```

The same program, unchanged, runs in every cartesian closed category:
in particular in the topos of sheaves on *any* site — any gros topos
of generalized smooth spaces — where the base types may now be
interpreted as, say, a sheaf of smoothly-varying angles, and where
mapping spaces (10) provide the configuration spaces of *fields* of
heliostats. This is the sense in which the formalisation is a
constructive simulator: one syntax, all semantics.

```agda
module heliostat-fields
    {ℓ} {C : Precategory ℓ ℓ} (J : Coverage C ℓ)
  where

  private
    module ShModel = Cat.CartesianClosed.Free.Model Heliostat
      (Sh[]-cartesian J) (Sh[]-closed {J = J})

  heliostat-in-sheaves
    : (V : Heliostat-type → ⌞ Sh[ C , J ] ⌟)
    → elim.base-method ShModel.chaotic-cartesian ShModel.chaotic-closed V
    → Functor Free-ccc Sh[ C , J ]
  heliostat-in-sheaves V ops = ShModel.model.compile V ops
```

Moreover the compilation functors are not bare functors: they
preserve products and exponentials — the [[cartesian closed
functor|cartesian-closed-functor]] structure that makes "the space of
fields" mean the same thing before and after compilation.

```agda
_ = SetsModel.model.compile-cartesian
_ = SetsModel.model.compile-closed
_ = Cartesian-closed-functor
```

## Gauge transformations and simplicial shapes

Where the paper turns to gauge theory ((22)–(25)), plots stop forming
sets and start forming *groupoids*: two field configurations may be
identified by a gauge transformation, gauge transformations compose
(23), and higher gauge transformations identify identifications. The
shapes probing this structure are the simplices $\Delta^n$ of (25),
which form the [[simplex category]] with its [[coface]] and
[[codegeneracy]] generators satisfying the simplicial identities; the
resulting probe-topos is that of [[simplicial sets|simplicial-set]].

```agda
_ = Δ
_ = δ
_ = σ
_ = δ-comm
_ = σ-comm
_ = δ-σ-comm
_ = sSet
_ = Δ[_]
```

The paper's boxed *Kan condition* — every [[horn]] $\Lambda^n_k \mono
\Delta^n$ of gauge transformations admits a filler — is
`is-kan`{.Agda}, and the higher groupoids of (32),
$\rm{Sh}(\Delta)_{\rm{Kan}} \mono \rm{Sh}(\Delta)$, are the full
subcategory of [[Kan complexes|kan-complex]].

```agda
_ = Λ[_,_]
_ = horn-inclusion
_ = is-kan
_ = Kan-complexes
```

The delooping groupoid $\mathbf{B}G$ of (26) is the [[nerve]] of the
one-object [[delooping category]], and the computation (27) of its
plots — a single vertex, a 1-simplex for every group element, and a
2-simplex for every *pair*, witnessing the composite — holds here
for any monoid:

```agda
_ = nerve
_ = nerve-B
_ = nerve-B₀-is-contr
_ = nerve-B₁≃M
_ = nerve-B₂≃M×M
```

On the homotopy-theoretic side of the dictionary, the delooping of a
group exists as a higher inductive type with $G \simeq \Omega
\mathbf{B} G$ — the paper's (34) in the case $n = 1$ — and first
nonabelian cohomology appears as $H^1(X; G) = \| X \to \mathbf{B}G
\|_0$, computed in the 1Lab for abelian coefficients.

```agda
_ = Deloop
_ = G≃ΩB
```

## What is missing

For honesty, the items of the paper with no 1Lab counterpart yet:
germs of plots ((5), (6)); the identification of sheaves with the
localisation of presheaves at local isomorphisms (7); the proof that
the higher-inductive sheafification is left exact (connecting
`Sh[_,_]`{.Agda} to `Topos`{.Agda}); infinitesimally thickened and
super sites ((13)–(21)) — though nothing obstructs instantiating our
general sites at them once formal duals of algebras are set up; the
Dold–Kan correspondence ((29)–(31)); Eilenberg–MacLane spaces
$\mathbf{B}^n A$ for $n \ge 2$ and stable homotopy/spectra ((33),
(34), (40), (41)); Čech nerves and the cofibrant-resolution
presentation of nonabelian cohomology ((38), (39)); and orbifold
singularities. Each is a well-posed project over the infrastructure
assembled above.
