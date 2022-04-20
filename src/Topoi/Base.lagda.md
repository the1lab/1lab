```agda
open import Algebra.Prelude

open import Cat.Instances.Sets.Cocomplete
open import Cat.Instances.Functor.Limits
open import Cat.Instances.Sets.Complete
open import Cat.Diagram.Everything
open import Cat.Functor.Everything

import Cat.Functor.Bifunctor as Bifunctor
import Cat.Reasoning

module Topoi.Base where
```

<!--
```agda
open _=>_
```
-->

# Grothendieck topoi

Topoi are an abstraction introduced by Alexander Grothendieck in the
1960s as a generalisation of [topological spaces], suitable for his work
in algebraic geometry. Later (in the work of William Lawvere, and even
later Myles Tierney), topoi found a new life as "categories with a nice
internal logic", which mirrors that of the category $\sets$. Perhaps
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

A **topos** $\ca{T}$ is a [full subcategory] of a [presheaf category]
$[\ca{C}\op,\sets]$ (the category $\ca{C}$ is part of the definition)
such that the inclusion functor $\iota : \ca{T} \mono [\ca{C}\op,\sets]$
admits a [right adjoint], and this right adjoint preserves [finite
limits]. We summarise this situation in the diagram below, where "lex"
(standing for "**l**eft **ex**act") is old-timey speak for "finite limit
preserving".

~~~{.quiver .short-15}
\[\begin{tikzcd}
  {\mathcal{T}} & {[\mathcal{C}^{\mathrm{op}},\mathbf{Sets}]}
  \arrow[shift right=2, hook, from=1-1, to=1-2]
  \arrow["{\mathrm{lex}}"', shift right=2, from=1-2, to=1-1]
\end{tikzcd}\]
~~~

[full subcategory]: Cat.Functor.FullSubcategory.html
[presheaf category]: Cat.Functor.Hom.html#the-yoneda-embedding
[right adjoint]: Cat.Functor.Adjoint.html
[finite limits]: Cat.Diagram.Limit.Finite.html

In type theory, we must take care about the specific [universes] in
which everything lives. Let us make them explicit: An $(o,\ell)$-topos
$\ca{T}$ has a **site of definition**, which is an
$(o',\ell')$-precategory $\ca{C}$, and it arises as a reflective
subcategory of $[\ca{C}\op,\sets_\kappa]$ for some level $\kappa$.  That
is **five levels**.

[universes]: 1Lab.Type.html

```agda
record Topos {o ℓ} (𝓣 : Precategory o ℓ) s κ
  : Type (lsuc (o ⊔ ℓ ⊔ s ⊔ κ)) where
  field
    site : Precategory s s

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
powerset of $X$ is the poset $[X,\props]$. It is --- being a functor
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
function $f^* : B \to A$ which preserves finite meets and has a right
adjoint $f_* : A \to B$[^aft].

[^aft]: By the adjoint functor theorem, any map between posets which
preserves arbitrary joins has a right adjoint; Conversely, every map
which has a left adjoint preserves arbitrary joins.

[powerset]: Data.Power.html
[lattice]: Algebra.Lattice.html

We can prove that a topology $\tau$ on $X$ is the same thing as a
subframe of its powerset $[X,\props]$ --- a collection of subsets of
$X$, closed under finite meets and arbitrary joins.

Now, the notion of "topos" as a generalisation of that of "topological
space" is essentially self-evident: A topos $\ca{T}$ is a sub-topos of a
presheaf category $[\ca{C}\op,\sets]$. We have essentially categorified
"subframe" into "subtopos", and $\props$ into $\sets$. Note that, while
this seems circular ("a topos is a sub-topos of..."), the notion of
subtopos --- or rather, of **geometric embedding** --- makes no mention
of actual topoi, and makes sense for any pair of categories.

## As categories of spaces

Another perspective on topoi is that they are _categories of_ spaces,
rather than spaces themselves. We start by looking at presheaf topoi,
$[\ca{C}^op,\sets]$. The [coyoneda lemma] tells us that every presheaf
is a colimit of representables, which can be restated in less abstract
terms by saying that _presheaves are instructions for gluing together
objects of $\ca{C}$._ The objects of $\ca{C}$ are then interpreted as
"primitive shapes", and the maps in $\ca{C}$ are interpreted as "maps to
glue against".

[coyoneda lemma]: Cat.Functor.Hom.html#the-coyoneda-lemma

Let's make this more concrete by considering an example: Take $\ca{C} =
\bull \rightrightarrows \bull$, the category with two points --- let's
call them $V$ and $E$ --- and two arrows $s, t : V \to E$. A presheaf
$F$ on this category is given by a set $F_0(V)$, a set $F_0(E)$, and two
functions $F_1(s), F_1(t) : F_0(E) \to F_0(V)$. We call $F_0(V)$ the
vertex set, and $F_0(E)$ the edge set. Indeed, a presheaf on this
category is a _directed multigraph_, and maps between presheaves
_preserve adjacency_.

Our statement about "gluing primitive shapes" now becomes the rather
pedestrian statement "graphs are made up of vertices and edges". For
instance, the graph $\bull \to \bull \to \bull$ can be considered as a
disjoint union of two edges, which is then glued together in a way such
that the target of the first is the source of the first. The maps $s, t
: V \to E$ exhibit the two ways that a vertex can be considered "part
of" an edge.

## As "logically nice" categories

The definition of topos implies that any topos $\ca{T}$ enjoys many of
the same categorical properties of the category $\sets$ (see
[below](#properties)). Topoi are [complete] and [cocomplete], [cartesian
closed] (even [locally so]) --- colimits are stable under pullback,
coproducts are [disjoint], and [equivalence relations are effective].

[complete]: Cat.Diagram.Limit.Base.html#completeness
[cocomplete]: Cat.Diagram.Colimit.Base.html#cocompleteness
[cartesian closed]: Cat.CartesianClosed.Base.html
[locally so]: Cat.CartesianClosed.Locally.html
[disjoint]: Cat.Diagram.Coproduct.Indexed.html#disjoint-coproducts
[equivalence relations are effective]: Cat.Diagram.Congruence.html#effective-congruences

These properties, but _especially_ local cartesian closure, imply that
the internal logic of a topos is an incredibly nice form of type theory.
Dependent sums and products exist, there is an object of natural
numbers, the [poset of subobjects] is a complete [lattice] (even a
Heyting algebra), including existential and universal quantification.
Effectivity of congruences means that two points in a quotient are
identified if, and only if, they are related by the congruence.

[lattice]: Algebra.Lattice.html
[poset of subobjects]: Cat.Thin.Instances.Sub.html

In fact, this is essentially the _definition of_ a topos. The actual
definition, as a lex [reflective subcategory] of a presheaf category,
essentially ensures that the category $\ca{T}$ inherits the nice logical
properties of $\sets$ (through the presheaf category, which is _also_
very nice logically).

[reflective subcategory]: Cat.Functor.Adjoint.Reflective.html

**Terminology**: As was implicitly mentioned above, for a topos $L :
\ca{T} \xadj{}{} \psh(\ca{C})$, we call the category $\ca{C}$ the **site
of definition**. Objects in $\ca{T}$ are called **sheaves**, and the
functor $L$ is called **sheafification**. Maps between topoi are called
**geometric morphisms**, and will be defined below. We denote the
2-category of topoi, geometric morphisms and natural transformations by
$\topos$, following Johnstone. When $\psh(\ca{C})$ is regarded as a topos
unto itself, rather than an indirection in the definition of a sheaf
topos, we call it the **topos of $\ca{C}$-sets**.

# Examples

The "trivial" example of topoi is the category $\sets$, which is
equivalently the category $[*\op,\sets]$ of presheaves on the [terminal
category]. This is, in fact, the [terminal object] in the 2-category
$\topos$ of topoi (morphisms are described
[below](#geometric-morphisms)), so we denote it by `𝟙`.

[terminal category]: Cat.Instances.Shape.Terminal.html
[terminal object]: Cat.Diagram.Terminal.html

```agda
𝟙 : ∀ {κ} → Topos (Sets κ) lzero κ
𝟙 {κ} = sets where
  open Topos
  open Functor
  open _⊣_
  open is-lex
```

The inclusion functor $\sets \mono \psh(*)$ is given by the "constant
presheaf" functor, which sends each set $X$ to the constant functor with
value $X$.

```agda
  incl : Functor (Sets κ) (PSh κ ⊤Cat)
  incl .F₀ x .F₀ _    = x
  incl .F₀ x .F₁ _ f  = f
  incl .F₀ x .F-id    = refl
  incl .F₀ x .F-∘ f g = refl

  incl .F₁ f = NT (λ _ → f) (λ _ _ _ → refl)

  incl .F-id    = Nat-path λ _ → refl
  incl .F-∘ f g = Nat-path λ _ → refl

  sets : Topos _ _ _
  sets .site = ⊤Cat

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
    isic .inv nt         = η nt tt

    isic .rinv nt i .η _ = η nt tt
    isic .rinv nt i .is-natural _ _ f j x =
      y .is-tr _ _ (λ j → nt .η tt x) (λ j → nt .is-natural tt tt f j x) i j

    isic .linv x i = x
```

The "sheafification" left adjoint is given by evaluating a presheaf $F$
at its sole section $F(*)$, and similarly by evaluating a natural
transformation $\eta : F \To G$ at its one component $\eta_* : F(*) \to
G(*)$.

```agda
  sets .L .F₀ F    = F₀ F tt
  sets .L .F₁ nt   = η nt tt
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
  sets .L-lex .pres-⊤ {T} psh-terminal set = contr (cent .η tt) uniq where
    func = incl .F₀ set
    cent = psh-terminal func .centre
    uniq : ∀ f → cent .η tt ≡ f
    uniq f = ap (λ e → e .η tt) (psh-terminal func .paths f′) where
      f′ : _ => _
      f′ .η _ = f
      f′ .is-natural _ _ _ = funext λ x → happly (sym (F-id T)) _

  sets .L-lex .pres-pullback {P} {X} {Y} {Z} pb = pb′ where
    open is-pullback
    pb′ : is-pullback (Sets κ) _ _ _ _
    pb′ .square = ap (λ e → η e tt) (pb .square)
    pb′ .limiting {P'} {p₁' = p₁'} {p₂' = p₂'} p =
      η (pb .limiting {P′ = incl .F₀ P'} {p₁' = p1'} {p₂' = p2'}
          (Nat-path λ _ → p)) tt
      where
        p1' : _ => _
        p1' .η _ = p₁'
        p1' .is-natural x y f i o = F-id X (~ i) (p₁' o)
        p2' : _ => _
        p2' .η _ = p₂'
        p2' .is-natural x y f i o = F-id Y (~ i) (p₂' o)
    pb′ .p₁∘limiting = ap (λ e → η e tt) (pb .p₁∘limiting)
    pb′ .p₂∘limiting = ap (λ e → η e tt) (pb .p₂∘limiting)
    pb′ .unique {P′} {lim' = lim'} p1 p2 =
      ap (λ e → η e tt) (pb .unique {lim' = l′}
        (Nat-path λ _ → p1) (Nat-path λ _ → p2))
      where
        l′ : incl .F₀ P′ => P
        l′ .η _ = lim'
        l′ .is-natural x y f i o = F-id P (~ i) (lim' o)
```
</details>

Similarly, we can construct the adjunction unit and counit by looking at
components and constructing identity natural transformations.

```agda
  sets .L⊣ι .unit .η _ .η _ f            = f
  sets .L⊣ι .unit .η F .is-natural _ _ _ = F-id F
  sets .L⊣ι .unit .is-natural _ _ _      = Nat-path λ _ → refl

  sets .L⊣ι .counit .η _ x            = x
  sets .L⊣ι .counit .is-natural _ _ _ = refl

  sets .L⊣ι .zig = refl
  sets .L⊣ι .zag = Nat-path λ _ → refl
```

More canonical examples are given by any presheaf category, where both
the inclusion and sheafification functors are the identity.  Examples of
presheaf topoi are abundant in abstract homotopy theory (the categories
of cubical and simplicial sets) --- which also play an important role in
modelling homotopy _type_ theory; Another example of a presheaf topos is
the category of _quivers_ (directed multigraphs).

```agda
Presheaf : ∀ {κ s} (C : Precategory s s) → Topos (PSh κ C) s κ
Presheaf {κ} C = psh where
  open Functor
  open Topos
  psh : Topos _ _ _
  psh .site = C
  psh .ι = Id
  psh .has-ff = id-equiv
  psh .L = Id
  psh .L-lex .is-lex.pres-⊤ c = c
  psh .L-lex .is-lex.pres-pullback pb = pb
  psh .L⊣ι = adj where
    open _⊣_
    adj : Id ⊣ Id
    adj .unit = NT (λ _ → idnt) λ x y f → Nat-path λ _ → refl
    adj .counit = NT (λ _ → idnt) (λ x y f → Nat-path λ _ → refl)
    adj .zig = Nat-path λ _ → refl
    adj .zag = Nat-path λ _ → refl
```

# Properties of topoi

The defining property of a topos $\ca{T}$ is that it admits a
geometric embedding into a presheaf category, meaning the adjunction
$L : \ca{T} \xadj{}{} \psh(\ca{C}) : \iota$ is very special indeed: Since
the right adjoint is fully faithful, the adjunction is [monadic],
meaning that it exhibits $\ca{T}$ as the category of [algebras] for
a (lex, idempotent) monad: the "sheafification monad". This gives us
completeness in $\ca{T}$ for "free" (really, it's because presheaf
categories are complete, and those are complete because $\sets$ is.)

```agda
module _ {o ℓ} {𝓣 : Precategory o ℓ} {s κ} (T : Topos 𝓣 s κ) where
  open Topos T

  Sheafify : Monad (PSh κ site)
  Sheafify = Adjunction→Monad L⊣ι

  Sheafify-monadic : is-monadic L⊣ι
  Sheafify-monadic = is-reflective→is-monadic L⊣ι has-ff

  Topos-is-complete : is-complete κ κ 𝓣
  Topos-is-complete = equivalence→complete
    (is-equivalence.inverse-equivalence Sheafify-monadic)
    (Eilenberg-Moore-is-complete
      (Functor-cat-is-complete (Sets-is-complete {ι = κ} {κ} {κ})))
```

[monadic]: Cat.Functor.Adjoint.Monadic.html
[algebras]: Cat.Diagram.Monad.html#algebras-over-a-monad

Furthermore, since $L$ preserves colimits (it is a left adjoint), then
we can compute the colimit of some diagram $F : J \to \ca{T}$ as the
colimit (in $\psh(\ca{C})$) of $\iota F$ --- which exists because
$\sets$ is cocomplete --- then apply $L$ to get a colimiting cocone for
$L \iota F$. But the counit of the adjunction $\eps : L \iota \To
\id{Id}$ is a natural isomorphism, so we have a colimiting cocone for
$F$.

```agda
  Topos-is-cocomplete : is-cocomplete κ κ 𝓣
  Topos-is-cocomplete F =
    Colimit-ap-iso _
      (F∘-iso-id-l (is-reflective→counit-iso L⊣ι has-ff))
      sheafified
      where
      psh-colim : Colimit (ι F∘ F)
      psh-colim = Functor-cat-is-cocomplete (Sets-is-cocomplete {ι = κ} {κ} {κ}) _

      sheafified : Colimit ((L F∘ ι) F∘ F)
      sheafified = subst Colimit F∘-assoc $
        left-adjoint-colimit L⊣ι psh-colim
```

Since the reflector is left exact, and thus in particular preserves
finite products, a theorem of Johnstone (Elephant A4.3.1) implies the
topos $\ca{T}$ is an _exponential ideal_ in $\psh(\ca{C})$: If $Y$ is a
sheaf, and $X$ is any presheaf, then the internal hom $[X,Y]$ is a
sheaf: topoi are [cartesian closed].

[cartesian closed]: Cat.CartesianClosed.Base.html

<!-- TODO [Amy 2022-04-02]
prove all of the above lmao
-->

# Geometric morphisms

The definition of a topos as a generalisation of topological space leads
us to look for a categorification of "continuous map" to functors
between topoi. In the same way that a continuous function $f : X \to Y$
may be seen as a homomorphism of frames $f^* : O(Y) \to O(X)$, with
defining feature the preservation of finite meets and arbitrary joins,
we shall define a **geometric morphism** $\topos(X,Y)$ to be a functor
$f^* : Y \to X$ which is left exact and admits a right adjoint.

<!--
```agda
module _ where
  private
    variable
      o ℓ o′ ℓ′ κ κ′ s s′ : Level
      E F : Precategory o ℓ
    lvl : ∀ {o ℓ o′ ℓ′} → Precategory o ℓ → Precategory o′ ℓ′ → Level
    lvl {o} {ℓ} {o′} {ℓ′} _ _ = o ⊔ ℓ ⊔ ℓ′ ⊔ o′
```
-->

```agda
  record Top[_,_] (_ : Topos E s κ) (_ : Topos F s′ κ′) : Type (lvl E F) where
    field
      Inv[_]  : Functor F E
      Inv-lex : is-lex Inv[_]
      Dir[_]  : Functor E F
      Inv⊣Dir : Inv[_] ⊣ Dir[_]

  open Top[_,_]
```

<!-- TODO [Amy 2022-04-02]
talk about geometric logic?
-->
