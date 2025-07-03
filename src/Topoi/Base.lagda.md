<!--
```agda
open import Cat.Functor.Equivalence.Properties
open import Cat.Functor.Adjoint.Continuous
open import Cat.Functor.Adjoint.Reflective
open import Cat.Instances.Algebras.Limits
open import Cat.Instances.Sets.Cocomplete
open import Cat.Instances.Functor.Limits
open import Cat.Instances.Shape.Terminal
open import Cat.Instances.Slice.Presheaf
open import Cat.Functor.Adjoint.Compose
open import Cat.Functor.Adjoint.Monadic
open import Cat.Instances.Sets.Complete
open import Cat.Functor.Adjoint.Monad
open import Cat.Diagram.Colimit.Base
open import Cat.Diagram.Limit.Finite
open import Cat.Functor.Hom.Coyoneda
open import Cat.Functor.Equivalence
open import Cat.Diagram.Limit.Base
open import Cat.Functor.Properties
open import Cat.Instances.Elements
open import Cat.Instances.Functor
open import Cat.Diagram.Pullback
open import Cat.Functor.Pullback
open import Cat.Functor.Adjoint
open import Cat.Instances.Slice
open import Cat.Instances.Lift
open import Cat.Diagram.Monad
open import Cat.Functor.Slice
open import Cat.Functor.Hom
open import Cat.Prelude

import Cat.Functor.Bifunctor as Bifunctor
import Cat.Reasoning
```
-->

```agda
module Topoi.Base where
```

<!--
```agda
open _=>_
```
-->

# Grothendieck topoi {defines="topos topoi"}

Topoi are an abstraction introduced by Alexander Grothendieck in the
1960s as a generalisation of [topological spaces], suitable for his work
in algebraic geometry. Later (in the work of William Lawvere, and even
later Myles Tierney), topoi found a new life as "categories with a nice
internal logic", which mirrors that of the category $\Sets$. Perhaps
surprisingly, every Grothendieck topos is also a topos in their logical
conception (called **elementary**); Since elementary topoi are very hard
to come by predicatively, we formalise a particular incarnation of
Grothendieck's notion here.

[topological spaces]: https://ncatlab.org/nlab/show/topological+space

Grothendieck described his topoi by first defining a notion of _site_,
which generalises the (poset of) open subsets of a topological space,
and then describing what "sheaves on a site" should be, the
corresponding generalisation of sheaves on a space. Instead of directly
defining the notion of site, we will leave it implicitly, and define a
**topos** as follows:

A **topos** $\cT$ is a [full subcategory] of a [presheaf category]
$[\cC\op,\Sets]$ (the category $\cC$ is part of the definition) such
that the inclusion functor $\iota : \cT \mono [\cC\op,\Sets]$ admits a
[[left adjoint]], and this left adjoint preserves [[finite limits]]. We
summarise this situation in the diagram below, where "lex" (standing for
"**l**eft **ex**act") is old-timey speak for "finite limit preserving".

~~~{.quiver}
\[\begin{tikzcd}
  {\mathcal{T}} & {[\mathcal{C}^{\mathrm{op}},\mathbf{Sets}]}
  \arrow[shift right=2, hook, from=1-1, to=1-2]
  \arrow["{\mathrm{lex}}"', shift right=2, from=1-2, to=1-1]
\end{tikzcd}\]
~~~

[full subcategory]: Cat.Functor.FullSubcategory.html
[presheaf category]: Cat.Functor.Hom.html#the-yoneda-embedding

In type theory, we must take care about the specific [universes] in
which everything lives. Now, much of Grothendieck topos theory
generalises to arbitrary "base" topoi, via the use of bounded geometric
morphisms, but the "main" definition talks about $\Sets$-topoi. In
particular, every universe $\kappa$ generates a theory of
$\Sets_\kappa$-topoi, the categories of [$\kappa$-small] sheaves on
$\kappa$-small sites.

[$\kappa$-small]: 1Lab.intro.html#universes-and-size-issues

Fix a universe level $\kappa$, and consider the category $\Sets_\kappa$:
A topos $\cT$ might be a large category (i.e. it might have a space
of objects $o$ with $o > \kappa$), but it is _essentially locally
small_, since it admits a fully-faithful functor into
$[\cC\op,\Sets_\kappa]$, which have homs at level $\kappa$. Hence,
even if we allowed the category $\cT$ to have $\hom$s at a level
$\ell$, we would have no more information there than fits in $\kappa$.

For this reason, a topos $\cC$ only has two levels: The level $o$ of
its objects, and the level $\kappa$ of the category of Sets relative to
which $\cC$ is a topos.

[universes]: 1Lab.Type.html

```agda
record Topos {o} κ (𝓣 : Precategory o κ) : Type (lsuc (o ⊔ κ)) where
  field
    site : Precategory κ κ

    ι : Functor 𝓣 (PSh κ site)
    has-ff : is-fully-faithful ι

    L : Functor (PSh κ site) 𝓣
    L-lex : is-lex L

    L⊣ι : L ⊣ ι

  module ι = Functor ι
  module L = Functor L
  module L⊣ι = _⊣_ L⊣ι
```

## As generalised spaces

I'll echo here the standard definition of topological space, but due to
personal failings I can't motivate it. A **topological space** $(X,
\tau)$ consists of a set of _points_ $X$, and a _topology_ $\tau$, a
subset of its [powerset] which is closed under arbitrary unions and
finite intersections.

Let's reword that using category-theoretic language: Recall that the
powerset of $X$ is the poset $[X,\Props]$. It is --- being a functor
category into a complete and cocomplete (thin) category --- _also_
complete and cocomplete, so all joins and finite meets (unions and
intersections) exist; Furthermore, the distributive law

$$
S \cap \left(\bigcup_i F_i\right) = \bigcup_i (S \cap F_i)
$$

holds for any subset $S$ and family of subsets $F$. A [lattice]
satisfying these properties (finite meets, arbitrary joins, the
distributive law) is called a **frame**. A map of frames $f : A \to B$
is defined to be a map of their underlying sets preserving finite meets
and arbitrary joins --- by abstract nonsense, this is the same as a
function $f^* : A \to B$ which preserves finite meets and has a right
adjoint $f_* : B \to A$[^aft].

[^aft]: By the adjoint functor theorem, any map between posets which
preserves arbitrary joins has a right adjoint; Conversely, every map
which has a right adjoint preserves arbitrary joins.

[powerset]: Data.Power.html
[lattice]: Order.Lattice.html

We can prove that a topology $\tau$ on $X$ is the same thing as a
subframe of its powerset $[X,\Props]$ --- a collection of subsets of
$X$, closed under finite meets and arbitrary joins.

Now, the notion of "topos" as a generalisation of that of "topological
space" is essentially self-evident: A topos $\cT$ is a sub-topos of a
presheaf category $[\cC\op,\Sets]$. We have essentially categorified
"subframe" into "subtopos", and $\Props$ into $\Sets$. Note that, while
this seems circular ("a topos is a sub-topos of..."), the notion of
subtopos --- or rather, of **geometric embedding** --- makes no mention
of actual topoi, and makes sense for any pair of categories.

## As categories of spaces

Another perspective on topoi is that they are _categories of_ spaces,
rather than spaces themselves. We start by looking at presheaf topoi,
$[\cC\op,\Sets]$. The [coyoneda lemma] tells us that every presheaf
is a colimit of representables, which can be restated in less abstract
terms by saying that _presheaves are instructions for gluing together
objects of $\cC$._ The objects of $\cC$ are then interpreted as
"primitive shapes", and the maps in $\cC$ are interpreted as "maps to
glue against".

[coyoneda lemma]: Cat.Functor.Hom.Coyoneda.html

Let's make this more concrete by considering an example: Take $\cC =
\bull \tto \bull$, the category with two points --- let's
call them $V$ and $E$ --- and two arrows $s, t : V \to E$. A presheaf
$F$ on this category is given by a set $F_0(V)$, a set $F_0(E)$, and two
functions $F_1(s), F_1(t) : F_0(E) \to F_0(V)$. We call $F_0(V)$ the
node set, and $F_0(E)$ the edge set. Indeed, a presheaf on this
category is a _directed multigraph_, and maps between presheaves
_preserve adjacency_.

Our statement about "gluing primitive shapes" now becomes the rather
pedestrian statement "graphs are made up of vertices and edges". For
instance, the graph $\bull \to \bull \to \bull$ can be considered as a
disjoint union of two edges, which is then glued together in a way such
that the target of the first is the source of the second. The maps $s, t
: V \to E$ exhibit the two ways that a node can be considered "part
of" an edge.

## As "logically nice" categories

The definition of topos implies that any topos $\cT$ enjoys many of the
same categorical properties of the category $\Sets$ (see
[below](#properties-of-topoi)). Topoi are [complete] and [cocomplete],
[[cartesian closed]] (even [[locally so|locally cartesian closed]]) ---
colimits are stable under pullback, coproducts are [disjoint], and
[equivalence relations are effective].

[complete]: Cat.Diagram.Limit.Base.html#completeness
[cocomplete]: Cat.Diagram.Colimit.Base.html#cocompleteness
[disjoint]: Cat.Diagram.Coproduct.Indexed.html#disjoint-coproducts
[equivalence relations are effective]: Cat.Diagram.Congruence.html#effective-congruences

These properties, but _especially_ local cartesian closure, imply that
the internal logic of a topos is an incredibly nice form of type theory.
Dependent sums and products exist, there is an object of natural
numbers, the poset of subobjects of any object is a complete [lattice]
(even a Heyting algebra), including existential and universal
quantification.  Effectivity of congruences means that two points in a
quotient are identified if, and only if, they are related by the
congruence.

[lattice]: Order.Lattice.html

In fact, this is essentially the _definition of_ a topos. The actual
definition, as a lex [reflective subcategory] of a presheaf category,
essentially ensures that the category $\cT$ inherits the nice logical
properties of $\Sets$ (through the presheaf category, which is _also_
very nice logically).

[reflective subcategory]: Cat.Functor.Adjoint.Reflective.html

::: terminology
As was implicitly mentioned above, for a topos $L :
\cT \xadj{}{} \psh(\cC)$, we call the category $\cC$ the **site
of definition**. Objects in $\cT$ are called **sheaves**, and the
functor $L$ is called **sheafification**. Maps between topoi are called
**geometric morphisms**, and will be defined below. We denote the
2-category of topoi, geometric morphisms and natural transformations by
$\Topos$, following Johnstone. When $\psh(\cC)$ is regarded as a topos
unto itself, rather than an indirection in the definition of a sheaf
topos, we call it the **topos of $\cC$-sets**.
:::

# Examples

The "trivial" example of topoi is the category $\Sets$, which is
equivalently the category $[*\op,\Sets]$ of presheaves on the [[terminal
category]]. This is, in fact, the [[terminal object]] in the 2-category
$\Topos$ of topoi (morphisms are described
[below](#geometric-morphisms)), so we denote it by `𝟙`.

```agda
𝟙 : ∀ {κ} → Topos κ (Sets κ)
𝟙 {κ} = sets where
  open Topos
  open Functor
  open _⊣_
  open is-lex
```

The inclusion functor $\Sets \mono \psh(*)$ is given by the "constant
presheaf" functor, which sends each set $X$ to the constant functor with
value $X$.

```agda
  incl : Functor (Sets κ) (PSh κ (Lift-cat κ κ ⊤Cat))
  incl .F₀ x .F₀ _    = x
  incl .F₀ x .F₁ _ f  = f
  incl .F₀ x .F-id    = refl
  incl .F₀ x .F-∘ f g = refl

  incl .F₁ f = NT (λ _ → f) (λ _ _ _ → refl)

  incl .F-id    = trivial!
  incl .F-∘ f g = trivial!

  sets : Topos κ (Sets κ)
  sets .site = Lift-cat κ κ ⊤Cat

  sets .ι = incl
```

This functor is fully faithful since a natural transformation between
presheaves on the point is entirely determined by its component at..
well, the point. Hence, the map $\eta \mapsto \eta_*$ exhibits an
inverse to the inclusion functor's action on morphisms, which is
sufficient (and necessary) to conclude fully-faithfulness.

```agda
  sets .has-ff {x} {y} = is-iso→is-equiv isic where
    open is-iso
    isic : is-iso (incl .F₁ {x} {y})
    isic .from nt = nt .η _
    isic .rinv nt = trivial!
    isic .linv f  = refl
```

The "sheafification" left adjoint is given by evaluating a presheaf $F$
at its sole section $F(*)$, and similarly by evaluating a natural
transformation $\eta : F \To G$ at its one component $\eta_* : F(*) \to
G(*)$.

```agda
  sets .L .F₀ F    = F · _
  sets .L .F₁ nt   = nt · _
  sets .L .F-id    = refl
  sets .L .F-∘ f g = refl
```

<details>

<summary> These functors actually define an [adjoint equivalence] of
categories, $L$ is continuous and, in particular, lex. Rather than
appealing to that theorem, though, we define the preservation of finite
limits directly for efficiency concerns. </summary>

[adjoint equivalence]: Cat.Functor.Equivalence.html

```agda
  sets .L-lex .pres-⊤ {T} psh-terminal set = contr (cent .η _) uniq where
    func = incl .F₀ set
    cent = psh-terminal func .centre
    uniq : ∀ f → cent .η _ ≡ f
    uniq f = psh-terminal func .paths f' ηₚ _ where
      f' : _ => _
      f' .η _ = f
      f' .is-natural _ _ _ = funext λ x → happly (sym (T .F-id)) _

  sets .L-lex .pres-pullback {P} {X} {Y} {Z} pb = pb' where
    open is-pullback
    pb' : is-pullback (Sets κ) _ _ _ _
    pb' .square = pb .square ηₚ _
    pb' .universal {P'} {p₁' = p₁'} {p₂' = p₂'} p =
      pb .universal {P' = incl · P'}
        {p₁' = NT (λ _ → p₁') (λ _ _ _ → funext λ _ → sym (X .F-id · _))}
        {p₂' = NT (λ _ → p₂') (λ _ _ _ → funext λ _ → sym (Y .F-id · _))}
        (Nat-pathp _ _ (λ x → p)) · lift tt

    pb' .p₁∘universal = pb .p₁∘universal ηₚ _
    pb' .p₂∘universal = pb .p₂∘universal ηₚ _
    pb' .unique {P'} {lim' = lim'} p1 p2 =
      pb .unique {lim' = l'} (Nat-pathp _ _ λ _ → p1) (Nat-pathp _ _ λ _ → p2) ηₚ _
      where
        l' : incl .F₀ P' => P
        l' .η _ = lim'
        l' .is-natural x y f i o = P .F-id (~ i) (lim' o)
```
</details>

Similarly, we can construct the adjunction unit and counit by looking at
components and constructing identity natural transformations.

```agda
  sets .L⊣ι .unit .η _ .η _ f            = f
  sets .L⊣ι .unit .η F .is-natural _ _ _ = F .F-id
  sets .L⊣ι .unit .is-natural _ _ _      = trivial!

  sets .L⊣ι .counit .η _ x            = x
  sets .L⊣ι .counit .is-natural _ _ _ = refl

  sets .L⊣ι .zig = refl
  sets .L⊣ι .zag = trivial!
```

More canonical examples are given by any presheaf category, where both
the inclusion and sheafification functors are the identity.  Examples of
presheaf topoi are abundant in abstract homotopy theory (the categories
of cubical and simplicial sets) --- which also play an important role in
modelling homotopy _type_ theory; Another example of a presheaf topos is
the category of _quivers_ (directed multigraphs).

```agda
Presheaf : ∀ {κ} (C : Precategory κ κ) → Topos κ (PSh κ C)
Presheaf {κ} C = psh where
  open Functor
  open Topos
  psh : Topos _ _
  psh .site = C
  psh .ι = Id
  psh .has-ff = id-equiv
  psh .L = Id
  psh .L-lex .is-lex.pres-⊤ c = c
  psh .L-lex .is-lex.pres-pullback pb = pb
  psh .L⊣ι = Id⊣Id
```

# Properties of topoi

The defining property of a topos $\cT$ is that it admits a
geometric embedding into a presheaf category, meaning the adjunction
$L : \cT \xadj{}{} \psh(\cC) : \iota$ is very special indeed: Since
the right adjoint is fully faithful, the adjunction is [monadic],
meaning that it exhibits $\cT$ as the category of [algebras] for
a (lex, idempotent) monad: the "sheafification monad". This gives us
completeness in $\cT$ for "free" (really, it's because presheaf
categories are complete, and those are complete because $\Sets$ is.)

```agda
module _ {o κ} {𝓣 : Precategory o κ} (T : Topos κ 𝓣) where
  open Topos T

  Sheafify : Monad-on _
  Sheafify = Adjunction→Monad L⊣ι

  Sheafify-monadic : is-monadic L⊣ι
  Sheafify-monadic = is-reflective→is-monadic L⊣ι has-ff

  Topos-is-complete : is-complete κ κ 𝓣
  Topos-is-complete = equivalence→complete
    (is-equivalence.inverse-equivalence Sheafify-monadic)
    (Eilenberg-Moore-is-complete _
      (Functor-cat-is-complete (Sets-is-complete {ι = κ} {κ} {κ})))
```

[monadic]: Cat.Functor.Adjoint.Monadic.html
[algebras]: Cat.Diagram.Monad.html#algebras-over-a-monad

Furthermore, since $L$ preserves colimits (it is a left adjoint), then
we can compute the colimit of some diagram $F : J \to \cT$ as the
colimit (in $\psh(\cC)$) of $\iota F$ --- which exists because
$\Sets$ is cocomplete --- then apply $L$ to get a colimiting cocone for
$L \iota F$. But the counit of the adjunction $\eps : L \iota \To
\Id$ is a natural isomorphism, so we have a colimiting cocone for
$F$.

```agda
  Topos-is-cocomplete : is-cocomplete κ κ 𝓣
  Topos-is-cocomplete F =
    natural-iso→colimit
      (F∘-iso-id-l (is-reflective→counit-iso L⊣ι has-ff))
      sheafified
      where
      psh-colim : Colimit (ι F∘ F)
      psh-colim = Functor-cat-is-cocomplete (Sets-is-cocomplete {ι = κ} {κ} {κ}) _

      sheafified : Colimit ((L F∘ ι) F∘ F)
      sheafified = subst Colimit F∘-assoc $
        left-adjoint-colimit L⊣ι psh-colim
```

Since the reflector is [[left exact|lex functor]], and thus in
particular preserves finite products, a theorem of Johnstone (Elephant
A4.3.1) implies the topos $\cT$ is an _exponential ideal_ in
$\psh(\cC)$: If $Y$ is a sheaf, and $X$ is any presheaf, then the
internal hom $[X,Y]$ is a sheaf: topoi are [[cartesian closed]].

<!-- [TODO: Amy 2022-04-02]
prove all of the above lmao
-->

Since topoi are defined as embedding faithfully into a category of
presheaves, it follows that they have a small **generating set**, in the
same sense that representables generate presheaves: In fact, the
generating set of a Grothendieck topos is exactly the set of
representables of its site!

Elaborating, letting $\cT$ be a topos, two maps $f, g : X \to Y \in
\cT$ are equal if and only if they are equal under $\iota$, i.e. as
maps of presheaves. But it follows from the [coyoneda lemma] that maps
of presheaves are equal if and only if they are equal on all
representables. Consequently, two maps in a $\cT$ are equal if and
only if they agree on all generalised elements with domain the
sheafification of a representable:

[coyoneda lemma]: Cat.Functor.Hom.Coyoneda.html

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} (ct : Topos ℓ C) where
  private
    module C = Cat.Reasoning C
    module ct = Topos ct
    module Site = Cat.Reasoning (ct.site)
    module PSh = Cat.Reasoning (PSh ℓ ct.site)
    module ι = Functor (ct.ι)
    module L = Functor (ct.L)
    open _⊣_ (ct.L⊣ι)

  open Functor
  open _=>_
```
-->

```agda
  Representables-generate
    : ∀ {X Y} {f g : C.Hom X Y}
    → ( ∀ {A} (h : C.Hom (L.₀ (よ₀ ct.site A)) X)
      → f C.∘ h ≡ g C.∘ h )
    → f ≡ g
  Representables-generate {f = f} {g} sep =
    ff→faithful {F = ct.ι} ct.has-ff $
      Representables-generate-presheaf ct.site λ h →
        ι.₁ f PSh.∘ h                                     ≡⟨ mangle ⟩
        ι.₁ ⌜ f C.∘ counit.ε _ C.∘ L.₁ h ⌝ PSh.∘ unit.η _ ≡⟨ ap! (sep _) ⟩
        ι.₁ (g C.∘ counit.ε _ C.∘ L.₁ h) PSh.∘ unit.η _   ≡˘⟨ mangle ⟩
        ι.₁ g PSh.∘ h                                     ∎
```

<!--
```agda
    where
      mangle
        : ∀ {X Y} {f : C.Hom X Y} {Z} {h : PSh.Hom Z _}
        → ι.₁ f PSh.∘ h ≡ ι.₁ (f C.∘ counit.ε _ C.∘ L.₁ h) PSh.∘ unit.η _
      mangle {f = f} {h = h} =
        ι.₁ f PSh.∘ h                                                                  ≡⟨ PSh.insertl zag ⟩
        ι.₁ (counit.ε _) PSh.∘ ⌜ unit.η _ PSh.∘ ι.₁ f PSh.∘ h ⌝                        ≡⟨ ap! (PSh.extendl (unit.is-natural _ _ _)) ⟩
        ι.₁ (counit.ε _) PSh.∘ ι.₁ (L.₁ (ι.₁ f)) PSh.∘ ⌜ unit.η _ PSh.∘ h ⌝            ≡⟨ ap! (unit.is-natural _ _ _) ⟩
        ι.₁ (counit.ε _) PSh.∘ ⌜ ι.₁ (L.₁ (ι.₁ f)) PSh.∘ ι.₁ (L.₁ h) PSh.∘ unit.η _ ⌝  ≡⟨ ap! (PSh.pulll (sym (ι.F-∘ _ _))) ⟩
        ι.₁ (counit.ε _) PSh.∘ ι.₁ (L.₁ (ι.₁ f) C.∘ L.₁ h) PSh.∘ unit.η _              ≡⟨ PSh.pulll (sym (ι.F-∘ _ _)) ⟩
        ι.₁ ⌜ counit.ε _ C.∘ L.₁ (ι.₁ f) C.∘ L.₁ h ⌝ PSh.∘ unit.η _                    ≡⟨ ap! (C.extendl (counit.is-natural _ _ _)) ⟩
        ι.₁ (f C.∘ counit.ε _ C.∘ L.₁ h) PSh.∘ unit.η _                                ∎
```
-->

Finally, the property of "being a topos" is invariant under slicing.
More specifically, since a given topos can be presented by different
sites, a presentation $\cT \xadj{}{} \psh(\cC)$ can be sliced
under an object $X \in \cT$ to present $\cT/X$ as a sheaf topos,
with site of definition $\psh(\int \iota(X))$. This follows from a
wealth of pre-existing theorems:

- A pair $L \dashv R$ of adjoint functors can be [sliced] under an
object $X$, giving an adjunction $\Sigma \epsilon L/R(X) \dashv R/X$; Slicing a
functor preserves full-faithfulness and left exactness, hence slicing a
geometric embedding gives a geometric embedding.

[sliced]: Cat.Functor.Slice.html

- The category $\psh(\cC)/\iota(X)$ [is equivalent to] the category
$\psh(\int \iota(X))$, hence "being a presheaf topos is stable under
slicing". Furthermore, this equivalence is part of an ambidextrous
adjunction, hence both functors preserve limits.

[is equivalent to]: Cat.Instances.Slice.Presheaf.html

- Dependent sum $\Sigma f$ along an isomorphism is an equivalence of
categories; But since a topos is presented by a _reflective_ subcategory
inclusion, the counit is an isomorphism.

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} (T : Topos ℓ C) (X : ⌞ C ⌟) where
  private
    module C = Cat.Reasoning C
    module Co = Cat.Reasoning (Slice C X)
    module T = Topos T

  open Topos
  open Functor
```
-->

We build the geometric embedding presenting $\cT/X$ as a topos by
composing the adjunctions $\epsilon_!(L/\iota(X)) \dashv \iota/X$
and $F \dashv F\inv$ --- where $F$ is the equivalence $\psh(\cC)/X
\to \psh(\int X)$. The right adjoint is [[fully faithful]] because it
composes two fully faithful functors (a slice of $\iota$ and an
equivalence), the left adjoint preserves finite limits because it is a
composite of two equivalences (hence two right adjoints) and a lex
functor.

```agda
  Slice-topos : Topos ℓ (Slice C X)
  Slice-topos .site = ∫ T.site (T.ι.F₀ X)
  Slice-topos .ι = slice→total F∘ Sliced (T.ι) X
  Slice-topos .has-ff = ∘-is-equiv (Sliced-ff {F = T.ι} (T.has-ff)) slice→total-is-ff
  Slice-topos .L = (Σf (T .L⊣ι.counit.ε _) F∘ Sliced (T.L) (T.ι.F₀ X)) F∘ total→slice

  Slice-topos .L-lex =
    F∘-is-lex
      (F∘-is-lex
        (right-adjoint→lex
          (is-equivalence.F⁻¹⊣F
            (Σ-iso-equiv (C.iso→invertible
              (is-reflective→counit-is-iso T.L⊣ι T.has-ff)))))
        (Sliced-lex T.L-lex))
      (right-adjoint→lex (slice→total-is-equiv .is-equivalence.F⊣F⁻¹))

  Slice-topos .L⊣ι = LF⊣GR (is-equivalence.F⁻¹⊣F slice→total-is-equiv)
                           (Sliced-adjoints T.L⊣ι)
```

# Geometric morphisms

The definition of a topos as a generalisation of topological space leads
us to look for a categorification of "continuous map" to functors
between topoi. In the same way that a continuous function $f : X \to Y$
may be seen as a homomorphism of frames $f^* : O(Y) \to O(X)$, with
defining feature the preservation of finite meets and arbitrary joins,
we shall define a **geometric morphism** $\Topos(X,Y)$ to be a functor
$f^* : Y \to X$ which is left exact and admits a right adjoint.

Why the right adjoint? Well, [right adjoints preserve limits], but by
duality, _left adjoints preserve colimits_. This embodies the "arbitrary
joins" part of a map of frames, whereas the "finite meets" come from
left exactness.

[right adjoints preserve limits]: Cat.Functor.Adjoint.Continuous.html

<!--
```agda
private
  variable
    o ℓ o' ℓ' κ κ' κ'' s s' : Level
    E F G : Precategory o ℓ
  lvl : ∀ {o ℓ o' ℓ'} → Precategory o ℓ → Precategory o' ℓ' → Level
  lvl {o} {ℓ} {o'} {ℓ'} _ _ = o ⊔ ℓ ⊔ ℓ' ⊔ o'
```
-->

```agda
record Geom[_,_] (E : Precategory o ℓ) (F : Precategory o' ℓ') : Type (lvl E F) where
  no-eta-equality
  field
    Inv[_]  : Functor F E
    Dir[_]  : Functor E F
    Inv-lex : is-lex Inv[_]
    Inv⊣Dir : Inv[_] ⊣ Dir[_]

open Geom[_,_] public
```

Computation establishes that the identity functor is left exact, and
self adjoint, so it is in particular both the direct and inverse image
parts of a geometric morphism $\cT \to \cT$.

```agda
Idg : Geom[ E , E ]
Idg {E = E} = record { Inv[_] = Id ; Dir[_] = Id
                     ; Inv-lex = lex ; Inv⊣Dir = adj }
```

<!--
```agda
  where
    module E = Cat.Reasoning E

    lex : is-lex Id
    lex .is-lex.pres-⊤ f = f
    lex .is-lex.pres-pullback p = p

    adj : Id ⊣ Id
    adj ._⊣_.unit .η _ = E.id
    adj ._⊣_.unit .is-natural x y f = sym E.id-comm
    adj ._⊣_.counit .η _ = E.id
    adj ._⊣_.counit .is-natural x y f = sym E.id-comm
    adj ._⊣_.zig = E.idl _
    adj ._⊣_.zag = E.idl _
```
-->

Since [[adjunctions compose]], geometric morphisms do, too. Observe that
the composite of inverse images and the composite of direct images go in
different directions! Fortunately, this matches the convention for
composing adjunctions, where the functors "swap sides": $LF \dashv GR$.

```agda
_G∘_ : Geom[ F , G ] → Geom[ E , F ] → Geom[ E , G ]
f G∘ g = mk where
  module f = Geom[_,_] f
  module g = Geom[_,_] g
  open is-lex

  mk : Geom[ _ , _ ]
  Inv[ mk ] = Inv[ g ] F∘ Inv[ f ]
  Dir[ mk ] = Dir[ f ] F∘ Dir[ g ]
  mk .Inv⊣Dir = LF⊣GR f.Inv⊣Dir g.Inv⊣Dir
```

The composition of two left-exact functors is again left-exact, so
there's no impediment to composition there, either.

```agda
  mk .Inv-lex .pres-⊤ term ob = g.Inv-lex .pres-⊤ (f.Inv-lex .pres-⊤ term) _
  mk .Inv-lex .pres-pullback pb = g.Inv-lex .pres-pullback (f.Inv-lex .pres-pullback pb)
```

An important class of geometric morphism is the **geometric embedding**,
which we've already met as the very definition of `Topos`{.Agda}. These
are the geometric morphisms with fully faithful direct image. These are
_again_ closed under composition, so if we want to exhibit that a
certain category $\cC$ is a topos, it suffices to give a geometric
embedding $\cC \to \cT$, where $\cT$ is some topos which is
convenient for this application.

```agda
record Geom[_↪_] (E : Precategory o ℓ) (F : Precategory o' ℓ') : Type (lvl E F) where
  field
    morphism : Geom[ E , F ]
    has-ff : is-fully-faithful Dir[ morphism ]

Geometric-embeddings-compose : Geom[ F ↪ G ] → Geom[ E ↪ F ] → Geom[ E ↪ G ]
Geometric-embeddings-compose f g =
  record { morphism = f .morphism G∘ g .morphism
         ; has-ff = ∘-is-equiv (g .has-ff) (f .has-ff) }
  where open Geom[_↪_]

Topos→geometric-embedding : (T : Topos κ E) → Geom[ E ↪ PSh κ (T .Topos.site) ]
Topos→geometric-embedding T = emb where
  emb : Geom[ _ ↪ _ ]
  Inv[ emb .Geom[_↪_].morphism ] = T .Topos.L
  Dir[ emb .Geom[_↪_].morphism ] = T .Topos.ι
  emb .Geom[_↪_].morphism .Inv-lex = T .Topos.L-lex
  emb .Geom[_↪_].morphism .Inv⊣Dir = T .Topos.L⊣ι
  emb .Geom[_↪_].has-ff = T .Topos.has-ff
```

<!-- [TODO: Amy, 2022-04-02]
talk about geometric logic?
-->
