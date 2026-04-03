<!--
```agda
open import 1Lab.Reflection.HLevel
open import 1Lab.HLevel.Closure
open import 1Lab.Reflection
open import 1Lab.Underlying
open import 1Lab.HLevel
open import 1Lab.Path
open import 1Lab.Type hiding (id ; _∘_)

open import Cat.Base
```
-->

```agda
module Cat.Displayed.Base where
```

<!--
```agda
private
  variable o ℓ : Level
  lvl : ∀ {o ℓ} → Precategory o ℓ → Level → Level → Level
  lvl {o} {ℓ} _ o' ℓ' = o ⊔ ℓ ⊔ lsuc (o' ⊔ ℓ')
```
-->

# Displayed categories

::: note
This section presents motivation and a conceptual introduction to
displayed categories.

[Click here to skip to the definition](#the-definition).
:::

Any [[functor]] $P : \cE \to \cB$ can be thought of as decomposing the
[[precategory]] $\cE$ into a *family* $P_\bull$ of categories indexed by
the objects $x : \cB$,[^decomposing] where the objects of $P_x$ should
be those objects of $\cE$ *sent to $x$ by $P$*, in a situation analogous
to how funct*ion*s $f : A \to B$ [[decompose|object classifier]] their
domain $A$ as a sum, namely of the [[fibres]] of $f$ over the points of
$B$.

[^decomposing]: This idea is formalised in the page on [[free isofibrations]].

Indeed, a literal approach to this decomposition would define the type
of objects of $P_x$ to be exactly the type-theoretic fibre $P^*x$. In
our setting, this interpretation is problematic for two complementary
reasons. First, if $\cB$ is an arbitrary precategory, the [[path
types|path]] of its type of objects should be regarded as a vestigial
structure left over from the encoding of category theory into type
theory, and not as an intrinsic property of the category.

This *could* be fixed by considering only functors into [[univalent
categories]], which are precisely those where identity of objects
corresponds coherently to isomorphism in the category. However, this
would prevent the discussion of categories defined over diagram
shapes like the [[walking isomorphism]], which are most convenient to
work with when defined in a non-univalent manner.[^walking-iso]

[^walking-iso]:
    To wit: the [[Rezk completion]] of the walking isomorphism is the
    [[terminal category]].

    While it is still true that the category of functors $[*, \cC]$ is
    equivalent to the category of isomorphisms in $\cC$, sending an
    isomorphism $(A, B, f)$ along equivalence results in $(A, A, \id)$.

    If we instead work with the non-univalent construction of $\{ 0
    \cong 1 \}$, the isomorphism is recovered definitionally.

Second, and perhaps more importantly, even *if* a definition
involving equality of objects were mathematically correct, it would
still be extremely inconvenient to work with in intensional type
theory. This is because the informal mathematical pratice for which
the traditional definitions are adapted enjoys *equality
reflection*, which we lack.

To be specific, whenever we have at hand some construction $c$ whose
type mentions $x$, but we want to use it in a context where Agda demands
we talk about $P(y)$, while an informal mathematician would use $c$
as-is, we must *transport* $c$ over a particular identification $P(y) =
x$, thus incurring a dependence on this identification which
*subsequent* constructions will have to deal with.

For example, the action of $P$ on morphisms has type-theoretic
fibres *only* over maps $\cB(P(x), P(y))$, so that if we have
objects $(x', p) : P^*(x)$ and $(y', q) : P^*(y)$, to talk about
maps $x' \to y'$ lying over $f : \cB(x, y)$, we must instead
consider the fibres of the map
$$
\cE(x', y') \xto{P} \cB(P(x'), P(y')) \xto{\rm{subst}_2\ \cB(-,-)\ \dots} \cB(x, y)
$$,
where the elided term in the second map makes explicit reference to
the identifications $p : P(x') = x$, resp. $q : P(y') = y$,
witnessing that $x'$ lies over $x$.

The gist of these objections is that, even *if* working with the fibres
of $P$ were mathematically correct, we would still prefer to avoid this,
for the same reason that we prefer type families over fibrations in
general. Moving from fibrations to families prioritises the
decomposition of $\cE$ over $\cB$, by making the notion of *being
defined over $x : \cB$* primitive.

A **displayed category** $\cE \liesover \cB$ is an equivalent
representation of the *pair* $(\cE, P)$, with one direction of the
equivalence being the construction of [[total categories]] and the other
being that of [[free isofibrations]]. Both the construction and study of
displayed categories is often simpler than working with functors:

*
    Every category[^construction] $\cE$ whose objects are described in
    natural language as "an object of $\cB$, equipped with such-and-such
    structure", and whose maps are "such-and-such preserving maps", is
    naturally a displayed category, where the type of objects over $x :
    \cB$ is the type of "such-and-such structures" with carrier $x$.

    A [[fibre category]] of $\cE$-qua-displayed-category over $x$ has,
    as its type of objects, precisely the type of structures with
    carrier $x$; if we instead considered $(\cE, U)$ as a
    category-functor pair, the objects of $U^*(x)$ would consist of
    nested triples $((x', S), \phi)$ where $x' : \cB$, $S$ is a
    structure with carrier $x'$, and $\phi : x' \cong x$.

    Many properties of the forgetful functor, like being [[faithful]],
    [[fully faithful]], or [[amnestic]], become simpler when phrased as
    properties of its generating displayed category. For example, it is
    faithful when each `Hom[_]`{.Agda} is a [[proposition]], and
    amnestic when $\cE$ is [[displayed univalent|displayed univalent
    category]].

[^construction]:
    Examples include the category of [[groups]], [[monoids]], [[rings]],
    [[modules]] over a ring, and more generally every *concrete
    category*; but also examples not over $\Sets$, e.g. [[algebras|monad
    algebras]] over a [[monad]] on arbitrary $\cC$.

*
    The prioritisation of indexing offered by displayed categories is a
    natural fit for the study of *indexed categories*, and results in
    notions that make no reference to identity of objects. Concepts in
    this direction include [[Cartesian|cartesian fibration]],
    [[right|right fibration]], [[discrete|discrete fibration]], and
    [[iso-|isofibration]] fibrations; concrete examples include the
    [[canonical self-indexing]], the [[family fibration]], and the
    [[externalisations]] of [[internal categories]].

    Additionally, the notion of [[section of a displayed category]]
    captures the idea that a category $\cB$ may be [[initial]] among
    some class of structure categories in terms of an
    *eliminator*, so that the values of the section
    *definitionally* lie over the inputs in $\cB$. This rephrasing was
    instrumental to the formalisation of [[free Cartesian closed
    categories]].

::: {.definition .commented-out #displayed-categories alias="displayed-category"}
A **category $\cE$ displayed over a [[category]] $\cB$** consists of

* A type $\cE_x$ of **objects over $x$**, for each $x : \cB$;
* A [[set]] $x' \to_f y'$ of **morphisms (from $x'$ to $y'$) over $f$**
  for each map $f : \cB(x, y)$, and objects $x' : \cE_x$, $y' : \cE_y$;
* Identity morphisms `id'`{.Agda}, assigning a $\id : x' \to_{\id} x'$
  to each $x'$; and
* A composition operation `_∘'_`{.Agda}, assigning
  $(g' \circ f') : x' \to_{g \circ f} z'$
  to each $f' : y' \to_f z'$, $g' : x' \to_g y'$.

These must satisfy [[dependent|path over]] analogues of the identity
(`idl'`{.Agda}, `idr'`{.Agda}) and associativity (`assoc'`{.Agda}) laws
for a category, defined over the corresponding laws in $\cB$.
:::


## The definition

```agda
record Displayed (B : Precategory o ℓ) o' ℓ' : Type (lvl B o' ℓ') where
```

<!--
```agda
  no-eta-equality
  open Precategory B
  infixr 40 _∘'_
  infix 30 _≡[_]_
```
-->

A displayed category $\cE$ is specified in terms of a family
`Ob[_]`{.Agda} of objects, indexed by those of $\cB$; we write $\cE_x$
for the value of the family at $x : \cB$, and if $x' : \cE_x$, we may
write $x' \liesover x$ if $\cE$ is understood. We then have a family of
[[sets]] `Hom[_]`{.Agda}, indexed by a map $f : \cB(x, y)$, and objects
$x' \liesover x$ and $y' \liesover y$; we write $x' \to_f y'$ for its
values.

```agda
  field
    Ob[_]  : ⌞ B ⌟ → Type o'
    Hom[_] : ∀ {x y} → Hom x y → Ob[ x ] → Ob[ y ] → Type ℓ'
```

<!--
```agda
    Hom[_]-set
      : ∀ {a b} (f : Hom a b) (x : Ob[ a ]) (y : Ob[ b ])
      → is-set (Hom[ f ] x y)
```
-->

A displayed category is also equipped with the algebraic operations of a
category --- identity and composition --- where each is indexed by its
corresponding operations in $\cB$. That is to say, the "identity over",
`id'`{.Agda}, is a map $x' \to_{\id} x'$, and, given composable $f' : y'
\to_{f} z'$ and $g' : x' \to_{g} y'$, their "composite over",
`_∘'_`{.Agda}, lives in $x' \to_{f \circ g} z'$.

```agda
    id' : ∀ {a} {x : Ob[ a ]} → Hom[ id ] x x
    _∘'_
      : ∀ {a b c x y z} {f : Hom b c} {g : Hom a b}
      → Hom[ f ] y z → Hom[ g ] x y → Hom[ f ∘ g ] x z
```

These operations are required to satisfy the laws analogous to those of
a category. However, considering (e.g.) the left identity law, we run
into a problem when stating them as equations: The composite
$$ (\id \circ f') : x' \to_{\id \circ f} y' $$
is displayed over a map that is only identical, but not definitionally
equal to, $f$. Therefore, the laws of a displayed category $\cE
\liesover \cB$ must be [[*dependent*|path over]] on the corresponding
law in $\cB$. We introduce the notation `_≡[_]_`{.Agda}, written $f'
\is_{p} g'$, to compare maps $f' : x' \to_{f} y'$ and $g' : x' \to_{g}
y$ over an identification $p : f \is g$.

```agda
  _≡[_]_
    : ∀ {a b x y} {f g : Hom a b} → Hom[ f ] x y → f ≡ g → Hom[ g ] x y → Type ℓ'
  _≡[_]_ {a} {b} {x} {y} f' p g' = PathP (λ i → Hom[ p i ] x y) f' g'
```

This makes it straightforward to write down the three laws, though they
remain quite wordy.

```agda
  field
    idr' : ∀ {a b x y} {f : Hom a b} (f' : Hom[ f ] x y) → (f' ∘' id') ≡[ idr f ] f'
    idl' : ∀ {a b x y} {f : Hom a b} (f' : Hom[ f ] x y) → (id' ∘' f') ≡[ idl f ] f'
    assoc'
      : ∀ {a b c d w x y z} {f : Hom c d} {g : Hom b c} {h : Hom a b}
      → (f' : Hom[ f ] y z) (g' : Hom[ g ] x y) (h' : Hom[ h ] w x)
      → f' ∘' (g' ∘' h') ≡[ assoc f g h ] ((f' ∘' g') ∘' h')
```

Finally, we can equip displayed categories with a distinguished
*transport* operation for moving displayed morphisms between equal
bases. While in general there may be many such, we can pair the "homwise
transport" `hom[_]`{.Agda} operation with a coherence datum
`coh[_]`{.Agda}, and this *pair* inhabits a contractible type (a centre
of contraction being the native `subst`{.Agda} operation, paired with
its filler). Therefore, these fields do not affect the "homotopy type"
of `Displayed`{.Agda}.

Their purpose is strictly as an aid in mechanisation: often (e.g. in the
[[fundamental fibration]] $\underline{\cB}$), the type $x \to_f y$
consists of some "relevant" data together with some "irrelevant"
[[propositions]], and, importantly, *only the propositions mention the
base morphism $f$*. This means that a "bespoke" `hom[_]`{.Agda}
implementation can then choose to leave the data fields definitionally
unchanged, whereas the native `subst`{.Agda} would surround them with
reflexive transports.

Counterintuitively, this extra field actually *increases* reusability,
despite nominally increasing the amount of data that goes into a
displayed category: If another construction needs to transport morphisms
in $\underline{\cB}$ to work, e.g. the [[pullback fibration]] for
[sconing] or [[Artin gluing]], or [[fibre categories]] of
[[subobjects]], dealing with the leftover `subst`{.Agda}s that arise in
(e.g.) composition of morphisms can be quite annoying, and while
cleaning them up can be automated, using the "bespoke" transport avoids
introducing them in the first place.

[sconing]: Cat.Displayed.Instances.Scone.html

```agda
  field
    hom[_]
      : ∀ {a b x y} {f g : Hom a b} (p : f ≡ g) (f' : Hom[ f ] x y)
      → Hom[ g ] x y
    coh[_]
      : ∀ {a b x y} {f g : Hom a b} (p : f ≡ g) (f' : Hom[ f ] x y)
      → f' ≡[ p ] hom[ p ] f'
```

# Developer documentation

::: warning
This section serves to document constructs derived from the definition
of displayed categories that aid in the formalisation, and not
necessarily interesting mathematical concepts.
:::

<!--
```agda
  private variable
    a b : Ob
    a' b' x y : Ob[ a ]

    e f g h : Hom a b
    e' f' g' h' : Hom[ f ] a' b'
    p q r s : f ≡ g
    p' q' r' s' : f' ≡[ p ] g'
```
-->

## Operators for composing paths-over

Since Agda often struggles to infer the arguments to the generic
displayed composition operator `_∙P_`{.Agda} in the setting of displayed
categories, we provide variants which specify that the dependency is
only on paths in the base category. One variant (`∙[-]-syntax`{.Agda})
takes the path over which the left argument is displayed explicitly, and the
other `_∙[]_`{.Agda} does this implicitly.

```agda
  ∙[-]-syntax
    : (p : f ≡ g) {q : g ≡ h}
    → f' ≡[ p ] g' → g' ≡[ q ] h' → f' ≡[ p ∙ q ] h'
  ∙[-]-syntax p p' q' = _∙P_ {B = λ f → Hom[ f ] _ _} p' q'

  syntax ∙[-]-syntax p p' q' = p' ∙[ p ] q'
```

```agda
  _∙[]_ : {p : f ≡ g} {q : g ≡ h} → f' ≡[ p ] g' → g' ≡[ q ] h' → f' ≡[ p ∙ q ] h'
  _∙[]_ p' q' = p' ∙[ _ ] q'

  infixr 30 _∙[]_ ∙[-]-syntax
```

## Equational reasoning in displayed categories

Iterated composition of dependent paths incurs a quadratic overhead when
compared to composition of ordinary paths, since the elaborated form of
each composition operator must store the paths over which both sides are
displayed:

<!--
```agda
  -- Generalisation really doesn't like generalising over the bases here
  module
    _ {a b} {d e f g h : Hom a b} {p : d ≡ e} {q : e ≡ f} {r : f ≡ g} {s : g ≡ h}
    where
```
-->

```agda
    _ : p' ∙[] q' ∙[] r' ∙[] s' ≡
      _∙[]_      {p = p} {q = q ∙ r ∙ s} p'
        (_∙[]_   {p = q} {q = r ∙ s}     q'
          (_∙[]_ {p = r} {q = s}         r'
            s'))
    _ = refl
```

Predictably, this is quite bad for performance: any part of the Agda
implementation which needs to traverse terms will spend $O(n^2)$ time
going through this redundant information, which could in principle be
recovered from the types of the arguments.

Surprisingly, we can alleviate this by working instead with paths in the
*total space* of $x' \to_{-} y'$, as a family over $x \to y$. We
introduce an auxiliary type `_∫≡_`{.Agda}, from which we can project a
path in $x' \to_{-} y'$, either over the constructed path between the
base maps, or (because $\hom$-sets are [[sets]]) over an arbitrary path
in the base.

```agda
  _∫≡_ : Hom[ f ] x y → Hom[ g ] x y → Type _
  f' ∫≡ g' = Path (Σ (Hom _ _) λ f → Hom[ f ] _ _) (_ , f') (_ , g')

  begin_ : (p : f' ∫≡ g') → f' ≡[ ap fst p ] g'
  begin_ = ap snd

  begin[]_ : f' ∫≡ g' → f' ≡[ p ] g'
  begin[]_ {f' = f'} {g' = g'} p = subst (f' ≡[_] g') prop! (ap snd p)

  infix 1 begin_ begin[]_
```

We can then provide combinators for composing a path in the total space
with an ordinary dependent path, with variants for explicitly specifying
the base path and for inverting the path to be composed.

```agda
  ≡[-]⟨⟩-syntax
    : (f' : Hom[ f ] x y) (p : f ≡ g) → g' ∫≡ h' → f' ≡[ p ] g' → f' ∫≡ h'
  ≡[-]⟨⟩-syntax f' p q' p' = ap₂ _,_ (p ∙ ap fst q') (p' ∙[] ap snd q')

  syntax ≡[-]⟨⟩-syntax f' p q' p' = f' ≡[ p ]⟨ p' ⟩ q'

  ≡[]⟨⟩-syntax : (f' : Hom[ f ] x y) → g' ∫≡ h' → f' ≡[ p ] g' → f' ∫≡ h'
  ≡[]⟨⟩-syntax {p = p} f' q' p' = f' ≡[ _ ]⟨ p' ⟩ q'

  ≡[]˘⟨⟩-syntax : (f' : Hom[ f ] x y) → g' ∫≡ h' → g' ≡[ p ] f' → f' ∫≡ h'
  ≡[]˘⟨⟩-syntax f' q' p' = f' ≡[]⟨ symP p' ⟩ q'

  syntax ≡[]⟨⟩-syntax f' q' p' = f' ≡[]⟨ p' ⟩ q'
  syntax ≡[]˘⟨⟩-syntax f' q' p' = f' ≡[]˘⟨ p' ⟩ q'

  infixr 2 ≡[-]⟨⟩-syntax ≡[]⟨⟩-syntax ≡[]˘⟨⟩-syntax
```

Finally, for the final step, we must provide a slight variation on the
reflexivity operator which pairs the given displayed map with its base.

```agda
  _∎[] : (f' : Hom[ f ] x y) → f' ∫≡ f'
  _∎[] _ = refl

  infix 3 _∎[]
```

<!--
```agda
record Trivially-graded {o ℓ} (B : Precategory o ℓ) (o' ℓ' : Level) : Type (o ⊔ ℓ ⊔ lsuc o' ⊔ lsuc ℓ') where
  open Precategory B
  field
    Ob[_]  : Ob → Type o'
    Hom[_] : ∀ {x y} → Hom x y → Ob[ x ] → Ob[ y ] → Type ℓ'

    instance
      ⦃ H-Level-Hom[_] ⦄
        : ∀ {a b} {f : Hom a b} {x : Ob[ a ]} {y : Ob[ b ]}
        → H-Level (Hom[ f ] x y) 2

    id'  : ∀ {a} {x : Ob[ a ]} → Hom[ id ] x x
    _∘'_ : ∀ {a b c x y z} {f : Hom b c} {g : Hom a b}
         → Hom[ f ] y z → Hom[ g ] x y → Hom[ f ∘ g ] x z

  infixr 40 _∘'_

  _≡[_]_ : ∀ {a b x y} {f g : Hom a b} → Hom[ f ] x y → f ≡ g → Hom[ g ] x y → Type ℓ'
  _≡[_]_ {a} {b} {x} {y} f' p g' = PathP (λ i → Hom[ p i ] x y) f' g'

  infix 30 _≡[_]_
  field
    idr' : ∀ {a b x y} {f : Hom a b} (f' : Hom[ f ] x y) → (f' ∘' id') ≡[ idr f ] f'
    idl' : ∀ {a b x y} {f : Hom a b} (f' : Hom[ f ] x y) → (id' ∘' f') ≡[ idl f ] f'
    assoc'
      : ∀ {a b c d w x y z} {f : Hom c d} {g : Hom b c} {h : Hom a b}
      → (f' : Hom[ f ] y z) (g' : Hom[ g ] x y) (h' : Hom[ h ] w x)
      → f' ∘' (g' ∘' h') ≡[ assoc f g h ] ((f' ∘' g') ∘' h')

{-# INLINE Displayed.constructor #-}

record Thinly-displayed {o ℓ} (B : Precategory o ℓ) (o' ℓ' : Level) : Type (o ⊔ ℓ ⊔ lsuc o' ⊔ lsuc ℓ') where
  open Precategory B
  field
    Ob[_]  : Ob → Type o'
    Hom[_] : ∀ {x y} → Hom x y → Ob[ x ] → Ob[ y ] → Type ℓ'

    instance
      ⦃ H-Level-Hom[_] ⦄
        : ∀ {a b} {f : Hom a b} {x : Ob[ a ]} {y : Ob[ b ]}
        → H-Level (Hom[ f ] x y) 1

    id'  : ∀ {a} {x : Ob[ a ]} → Hom[ id ] x x
    _∘'_ : ∀ {a b c x y z} {f : Hom b c} {g : Hom a b}
         → Hom[ f ] y z → Hom[ g ] x y → Hom[ f ∘ g ] x z

with-trivial-grading
  : ∀ {o ℓ} {B : Precategory o ℓ} {o' ℓ' : Level} → Trivially-graded B o' ℓ'
  → Displayed B o' ℓ'
{-# INLINE with-trivial-grading #-}
with-trivial-grading triv = record
  { Trivially-graded triv
  ; Hom[_]-set = λ f x y → hlevel 2
  ; hom[_]     = subst (λ e → Hom[ e ] _ _)
  ; coh[_]     = λ p → transport-filler _
  }
  where open Trivially-graded triv using (Hom[_] ; H-Level-Hom[_])

with-thin-display
  : ∀ {o ℓ} {B : Precategory o ℓ} {o' ℓ' : Level} → Thinly-displayed B o' ℓ'
  → Displayed B o' ℓ'
{-# INLINE with-thin-display #-}
with-thin-display triv = with-trivial-grading record where
  open Thinly-displayed triv using (Ob[_] ; Hom[_] ; id' ; _∘'_) renaming (H-Level-Hom[_] to i)
  H-Level-Hom[_] = basic-instance 2 $ is-prop→is-set (hlevel 1)
  idr'   f     = prop!
  idl'   f     = prop!
  assoc' f g h = prop!

open hlevel-projection

private
  Hom[]-set
    : ∀ {o ℓ o' ℓ'} {B : Precategory o ℓ} (E : Displayed B o' ℓ') {x y} {f : B .Precategory.Hom x y} {x' y'}
    → is-set (E .Displayed.Hom[_] f x' y')
  Hom[]-set E = E .Displayed.Hom[_]-set _ _ _

instance
  Hom[]-hlevel-proj : hlevel-projection (quote Displayed.Hom[_])
  Hom[]-hlevel-proj .has-level   = quote Hom[]-set
  Hom[]-hlevel-proj .get-level _ = pure (lit (nat 2))
  Hom[]-hlevel-proj .get-argument (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ arg _ t ∷ _) =
    pure t
  {-# CATCHALL #-}
  Hom[]-hlevel-proj .get-argument _ =
    typeError []

  Funlike-Displayed : ∀ {o ℓ o' ℓ'} {B : Precategory o ℓ} → Funlike (Displayed B o' ℓ') ⌞ B ⌟ λ _ → Type o'
  Funlike-Displayed = record { _·_ = Displayed.Ob[_] }

module _ {o ℓ o' ℓ'} {B : Precategory o ℓ} {E : Displayed B o' ℓ'} where
  _ : ∀ {x y} {f : B .Precategory.Hom x y} {x' y'} → is-set (E .Displayed.Hom[_] f x' y')
  _ = hlevel 2
```
-->
