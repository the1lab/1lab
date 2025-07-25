```agda
module index where
```

# 1Lab

This website is an experiment in **discoverable formalisation**: an
extensive library of formalised mathematics, presented as an explorable
reference resource. Our implementation of a mathematical library, using
*literate source code*, has allowed us a dual approach to the
explanation of mathematical concepts: the code and the prose are
complementary, and everyone is presented with the opportunity to choose
their own balance between the rigid formalisation and the intuitive
explanations.

<!--
```agda
open import 1Lab.Univalence
open import 1Lab.Equiv
open import 1Lab.HLevel
open import 1Lab.Type
open import 1Lab.Path
open import Cat.Base
_ = Precategory
```
-->

Rather than *yet another category theory library*, the 1Lab aims to be
an accessible introduction to structuralist mathematics, formalised in
the setting of homotopy type theory, using a theorem prover to check and
structure our work. As a result of using Agda, everything we mention
*knows its own definition*, whether we are talking about a specific
principle (like `univalence`{.Agda}), a big idea (like [[monoidal
categories]]), or a punctual observation (like [[surjections are
quotient maps]]).

::: mathpar

```agda
_ : ∀ {ℓ} {A B : Type ℓ} → is-equiv (path→equiv {A = A} {B})
_ = univalence
```

:::

The code snippet above, a re-statement of `univalence`{.Agda},
demonstrates how to explore the formalisation. Every mention of a
non-local name in the code above is a link to its definition (try
clicking on `path→equiv`{.Agda}!) --- on hover, you're presented with a
pop-up of their types. Everything we have formalised is accompanied by
prose, just like this --- which will contain links to the higher-level
concepts involved in the proof, such as [[universes]], [[path]] types,
and [[equivalences]].

We have developed a sizeable library of formalised mathematics, centered
around category theory and "adjacent" fields: abstract algebra, order
theory, logic, and synthetic homotopy theory. Unlike some of the [other
resources] listed below, the 1Lab takes an opinionated stance on its
type-theoretic foundations: we use **cubical type theory** (in the style
of @CCHM), and freely assume [[**propositional resizing**]].

Since the size of the library may make jumping into a particular topic
slightly daunting, we have put a lot of effort into making entry points
accessible as well. The simplest way to find something is by searching
for it. You can hit <kbd>Ctrl+K</kbd>/<kbd>Cmd+K</kbd> to bring up the
search prompt, as long as you have JavaScript enabled. Anything that has
a name can be searched for:

- Pages can be looked up by their module name (e.g. _[Algebra.Ring]_),
  or by their title (e.g. _[Abelian groups]_). These are organised
  hierarchically like an ordinary software library: Foundational results
  are under `1Lab`, a variety of data types are under `Data`, abstract
  algebra is under `Algebra`, category theory is under `Cat`, etc.

- Sections within a page can be looked up by their title, like _[The
  canonical self-indexing > As a fibration][selfindex]_. Keep in mind that
  the fuzzy matching means that writing out the prefix is entirely
  optional --- it's only displayed in the search results so you know where
  you'll be taken.

- Particular *concepts* can be looked up by a number of specific
  shorthands, e.g. [[adjunctions compose]] or [[composition of
  adjunctions]].

- Every definition in the library can be looked up by its identifier,
  like `Precategory`{.Agda}.

[Algebra.Ring]: Algebra.Ring.html
[Abelian groups]: Algebra.Group.Ab.html
[selfindex]: Cat.Displayed.Instances.Slice.html#as-a-fibration

While the library's size makes it infeasible to curate a list of every
single page, we have made an attempt to catalogue results we have
formalised and which appear in standard reference materials, essentially
by enumerating each book's index:

* The [HoTT](HoTT.html) page correlates with the book *Homotopy Type
  Theory: Univalent Foundations of Mathematics* [-@HoTT], which is also
  referred throughout the 1Lab as *the HoTT book*;

* The [Borceux](Borceux.html) page correlates with the first volume
  of the *Handbook of Categorical Algebra* [-@Borceux:vol1].

* The [Elephant](Elephant.html) page correlates with Johnstone's
  *Sketches of an Elephant: A Topos Theory Compendium* [-@Elephant].

Since both of these pages are also indexed for searching, you can
navigate to a specific section in these book indices by searching for
their names or section numbers: For example, try searching for [*the
Freudenthal suspension theorem*][hott86] or for section
[*A1.3*][elephanta13].

[hott86]: HoTT.html#the-freudenthal-suspension-theorem
[elephanta13]: Elephant.html#a1.3-regular-categories

## Getting involved

Our purpose is to make univalent mathematics accessible to everyone who
is interested, regardless of cultural background, age, educational
background, ethnicity, gender identity, or gender expression. **HoTT is
for everyone, and we are committed to fostering a kind, welcoming
environment**.

Even though the 1Lab is maintained primarily by [the authors][authors],
it is first and foremost a community project. The actual formalisation
work takes place on [GitHub], but ongoing discussion happens on
[Discord]. We welcome all contributions, though we would kindly ask that
anyone submitting a substantial change discuss it on Discord first.

[GitHub]: https://github.com/the1lab/1lab
[Discord]: https://discord.gg/eQDNM26uKP
[authors]: Authors.html

We accept contributions in all areas of mathematics, not just the ones
which already feature, or the ones listed above. Our lack of results in
real analysis is not because real analysis is *forbidden*, but rather
just because it's not the area of expertise of any of the authors. We
would be happy to help anyone to formalise and write about their
favourite subject, but do keep in mind that developing all of the
supporting theory might be a significant undertaking.

## Technology

The 1Lab would not be possible without a myriad other free and
open-source projects. In addition to our dearest proof assistant
[Agda](https://github.com/agda/agda) --- no part of which is distributed
--- we would like to mention the following open-source projects for
their fundamental importance:

* **Fonts**: Our monospace typeface is [Julia Mono] ([license][LICENSE.JuliaMono]),
  chosen for its excellent unicode coverage. The textual content can be
  read in either [Inria Sans] ([license][LICENSE.InriaSans]) or [EB
  Garamond] ([license][LICENSE.EBGaramond]), according to the user's
  preference. All of these fonts are distributed under the terms of the
  [SIL Open Font License, v1.1][OFL].

* **Prose**: We write our textual content in Markdown, which is rendered
  using [Pandoc], then put through a variety of filters to implement
  things like diagrams, folding equations, highlighted divs/details,
  etc. Despite our extensive use of Pandoc, no part of the project is
  distributed.

* **Mathematics**: We type-set our mathematics, at build-time, using
  [KaTeX](https://katex.org). Even though the rendering is done
  ahead-of-time, we distribute their CSS and fonts. KaTeX is distributed
  under the terms of the MIT license: a copy is available
  [here][LICENSE.KaTeX].

* **Iconography**: Our favicon is the ice-cube emoji from [Noto
  Emoji](https://github.com/googlefonts/noto-emoji), distributed under
  the terms of the Apache License, 2.0; a copy is available
  [here][LICENSE.Noto]. Other icons come from
  [octicons](https://github.com/primer/octicons), distributed under the
  terms of the MIT license, which you can find [here][LICENSE.Octicons].

* **Diagrams**: Our diagrams are created using [quiver], and rendered
  to SVG using [LaTeX] and [pdftocairo], which is part of the
  Poppler project. No part of these projects is redistributed.

* **Web**: All of the JavaScript we ship is free and open source
  software, and most of it is developed in-house --- you can find it on
  [our GitHub]. We use the [fast-fuzzy] library to power the search
  dialog, which is distributed under the terms of the ISC license,
  available [here][LICENSE.fast-fuzzy].

  None of our content relies on JavaScript to function, but enabling it
  does improve the experience --- allowing you control over theming, use
  of the search function, exploring the link graph, type-on-hover, and
  more. If you have JS disabled for privacy concerns, rest assured: The
  1Lab does not track you, or collect any sort of personally identifying
  information.

[quiver]: https://q.uiver.app
[LaTeX]: https://tug.org/texlive
[pdftocairo]: https://poppler.freedesktop.org
[Pandoc]: https://pandoc.org

[Julia Mono]: https://juliamono.netlify.app/
[Inria Sans]: https://github.com/BlackFoundryCom/InriaFonts
[EB Garamond]: https://github.com/georgd/EB-Garamond
[OFL]: https://openfontlicense.org/

[LICENSE.JuliaMono]: static/licenses/LICENSE.JuliaMono.txt
[LICENSE.InriaSans]: static/licenses/LICENSE.InriaSans.txt
[LICENSE.EBGaramond]: static/licenses/LICENSE.EBGaramond.txt
[LICENSE.Noto]: static/licenses/LICENSE.Noto.txt
[LICENSE.Octicons]: static/licenses/LICENSE.Octicons.txt
[LICENSE.KaTeX]: static/licenses/LICENSE.KaTeX.txt
[LICENSE.fast-fuzzy]: static/licenses/LICENSE.fast-fuzzy.txt

[KaTeX]: https://katex.org

[fast-fuzzy]: https://www.npmjs.com/package/fast-fuzzy
[our GitHub]: https://github.com/the1lab/1lab/tree/main/support/web/js

## Other resources

This is a list of freely available, online resources on homotopy type
theory, whose differing presentations (and axiomatics) might be more
inviting to particular readers. Please check them out!

* The aforementioned [*Homotopy Type Theory: Univalent Foundations of
  Mathematics*](https://homotopytypetheory.org/book) [-@HoTT] is split
  down the middle between being an introduction to the practice of
  homotopy type theory, and to the beginnings of the applications of
  univalence to category theory, homotopy theory, set theory and real
  analysis.

* Egbert Rijke's more recent *Introduction to Homotopy Type Theory*
  [-@Rijke:2022] is a more comprehensive introduction to the practice of
  dependent type theory in general, and homotopy type theory in
  particular, with no pre-existing familiarity assumed; it also includes
  applications of univalence to algebra, combinatorics, and homotopy
  theory.

* Martin Escardó's [*Introduction to Univalent Foundations of
  Mathematics with Agda*][martin] applies a theorem prover to the
  production of *lecture notes*, which are sequentially structured,
  unlike the 1Lab. Escardó takes a rather unusual approach to
  formalisation in Agda, using it as a proof assistant for a very basic
  ("spartan") type theory. His lecture notes include an introduction to
  working practically with type theory in its purest form.

* The [*agda-unimath* library] is a project very similar to the 1Lab,
  though using *axiomatic* homotopy type theory, rather than the cubical
  type theory which we prefer. It is currently maintained by Egbert
  Rijke, Fredrik Bakke, and Vojtěch Štěpančík, and contains a
  formalisation of a wide variety of topics in undergraduate
  mathematics, and a considerable selection of novel results in the
  field of univalent combinatorics.

* The [*TypeTopology* library], primarily by Escardó, but featuring
  collaborations, functions primarily as a formalisation of *novel*
  results in constructive mathematics. Its authors describe it as a
  *mathematical blackboard*; rather than employing a proof assistant to
  record and verify existing knowledge, its authors use Agda primarily
  to assist with discovering new ideas.

[*agda-unimath* library]: https://unimath.github.io/agda-unimath/HOME.html
[martin]: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html
[*TypeTopology* library]: https://www.cs.bham.ac.uk/~mhe/TypeTopology/

# Highlighted topics

While we can not maintain a list of every single page in the 1Lab, the
following pages define some of the central concepts the fields we have
formalised. They serve as great jumping-off points to explore them!

## Type theory

The modules under the `1Lab` namespace serve to bootstrap our type
theory. They provide the definitions of primitive concepts required for
Agda to function, and a firm conceptual basis which allows us to develop
higher-level mathematics. The highlights here are the key modules
leading up to the proof of the [[univalence principle|univalence]]:

```agda
open import 1Lab.Type        -- Basics of type universes
open import 1Lab.Path        -- The key idea in cubical type theory
open import 1Lab.HLevel      -- The hierarchy of homotopy n-types
open import 1Lab.Equiv       -- Equivalences, the notion of sameness for types
open import 1Lab.Univalence  -- The proof of univalence, and a few equivalents
```

### Metaprogramming

To support the rest of the formalisation, we engage not only in writing
mathematics, but also *meta*mathematics. These are *tactics*, which
teach Agda to handle more and more of what is *trivial*, allowing us to
focus on what is truly interesting. These pages are primarily
interesting for those interested in the use of Agda --- therefore, they
are more code than prose.

```agda
open import 1Lab.Reflection.HLevel
  -- Some h-level proofs are mechanically derivable from the structure
  -- of a type --- this tactic discharges those proof obligations.

open import 1Lab.Extensionality
  -- Given only a type, this type computes a "best" extensional equality
  -- to use at a given point of the formalisation, narrowing an identity
  -- to the data that matters.

open import 1Lab.Reflection.Induction
open import 1Lab.Reflection.Induction.Examples
  -- While Agda natively supports inductive types and pattern matching,
  -- it's often useful to have explicit elimination principles. This
  -- tactic automatically writes them.
```


## Category theory

The 1Lab was originally a project by one of the authors to learn
category theory by formalising it; unsurprisingly, this attracted other
category theorists, and this is the most comprehensive part of the
library. These files set up the core of the subject:

```agda
open import Cat.Base                -- Core definitions
open import Cat.Univalent           -- Univalent categories
open import Cat.Functor.Base        -- Functor categories
open import Cat.Functor.Adjoint     -- Adjoint functors
open import Cat.Functor.Equivalence -- Equivalences of categories
```

While there's way too much category theory to list, these are some of
the cooler things we have formalised.

### Bicategory theory

Try as we might, univalent mathematics do not let us consider a
1-category of general categories: we would have to focus on the [[strict
categories]], which are quite rare in comparison to the [[univalent
categories]]. However, we can fit them into a higher-dimensional
structure: a [[**bicategory**]].

```agda
open import Cat.Bi.Base -- The basic definitions
```

In addition to their importance as an organizational principle, we can
prove a theorem that exposes a funny circularity in category theory: a
[[strict category]] is given by a [[monad]] in the bicategory of spans
of [[sets]].

```agda
open import Cat.Bi.Instances.Spans
open import Cat.Bi.Diagram.Monad.Spans
```

### Cartesian closed categories

To a type theorist, a [[Cartesian closed]] category is exactly a
simply-typed lambda calculus. To cement this connection, we have an
implementation of normalisation-by-evaluation for STLC, whose
correctness is established relative to its semantics in an arbitrary
CCC:

```agda
open import Cat.CartesianClosed.Lambda
```

### Regular categories

[[Regular categories]] are often defined as those which have a
well-behaved calculus of relations --- we have a proof that the
relations in a regular category form a [[bicategory]], and so have
associative and unital composition.

```agda
open import Cat.Regular -- Regular categories
open import Cat.Bi.Instances.Relations
  -- The bicategory of relations in a regular category
```

A related concept is that of [[allegories]], which, rather than
axiomatising the structure which *leads to* a calculus of relations,
axiomatises the behaviour of the relations directly:

```agda
open import Cat.Allegory.Base -- Allegories
open import Cat.Allegory.Instances.Mat
  -- The allegory of matrices with values in a frame
```

### Monoidal categories

A [[monoidal category]] is the higher-dimensional counterpart of a
[[monoid]] --- a *category* with an associative and unital composition
*functor*. These are equivalently the $\hom$-categories in a
[[bicategory]].

```agda
open import Cat.Monoidal.Base
```

Monoidal categories turn out to involve quite a lot of data ---
constructing them in a proof assistant is onerous. In addition to the
first formalisation of the Day convolution in a type-theoretic proof
assistant, we also have a proof that every category with finite
[[products]] is monoidal.

```agda
open import Cat.Monoidal.Instances.Day
open import Cat.Monoidal.Instances.Cartesian
```

### Internal category theory

We can *internalise* the construction of [[strict categories]], beyond
$\Sets$, to any category with sufficient structure --- this results in
**internal category theory**.

```agda
open import Cat.Internal.Base
```

## Displayed categories

A [[displayed category]] (over $\cB$) is a type-theoretic repackaging of
the data of a category $\cE$ and a functor $\pi : \cE \to \cB$. Since
quite a few structures can be presented as categories-with-functors,
displayed categories are used quite a lot in the 1Lab in an
organizational role.

```agda
open import Cat.Displayed.Base            -- Displayed categories
open import Cat.Displayed.Univalence.Thin -- As categories of structured objects
```

However, displayed categories really come into their own to formalise
the concept of [[fibration]] --- a much nicer presentation of a
*functorial family of categories* over $\cB$.

```agda
open import Cat.Displayed.Cartesian          -- Definition of fibrations
open import Cat.Displayed.Cartesian.Indexing -- From fibrations to families
```

These families of categories arise naturally in the study of type
theories, and of logics as a special case.

```agda
open import Cat.Displayed.Comprehension -- An axiomatisation of context extension
open import Cat.Displayed.Doctrine      -- An axiomatisation of regular logic
```

### Examples

The following examples of displayed categories are particularly notable
to motivate the subject.

```agda
open import Cat.Displayed.Instances.Slice      -- Canonical self-indexing
open import Cat.Displayed.Instances.Family     -- Family fibration
open import Cat.Displayed.Instances.Subobjects -- Fibration of subobjects
```

Fibrations are also intimately connected with the study of [[internal
categories]], in particular through the construction of the
externalisation.

```agda
open import Cat.Displayed.Instances.Externalisation
```

## Order theory

The study of sets equipped with a notion of precedence, or containment;
while the theory of [[partial orders]] is naturally seen as a
restriction of the theory of categories, formalising these concepts
separately leads to cleaner mathematics.

```agda
open import Order.Base -- Definitions
```

By asking for the existence of operations assigning [[meets]] and
[[joins]], we can use posets to formalise structures in both logic and
geometry: [[frames]] and [[lattices]].

```agda
open import Order.Frame
open import Order.Lattice
```

### Domain theory

Domain theory is the study of posets that are complete under various
classes of [[least upper bounds]]. Domains naturally lead to
formalisations of *partiality*, which makes them important tools in the
semantics of programming languages.

```agda
open import Order.DCPO         -- Directed-complete partial orders
open import Order.DCPO.Free    -- Free DCPOs and free pointed DCPOs
open import Order.DCPO.Pointed -- Pointed directed-complete partial orders
```

## Synthetic homotopy theory

**Synthetic homotopy theory** is the name given to the application of
type theory to the study of homotopy invariants of spaces --- in fancier
words, for speaking to $\infty$-groupoids in their own terms.

```agda
open import Homotopy.Base          -- Basic definitions
open import Homotopy.Connectedness -- Connected types
```

The most famous result in synthetic homotopy theory is the fundamental
group of the circle, defined as a higher inductive type. But we also
have a formalisation that any group is the fundamental group of a
specific space:

```agda
open import Homotopy.Space.Circle
open import Homotopy.Space.Delooping
```

We have also recorded a few facts about the following spaces:

```agda
open import Homotopy.Space.Torus  -- The torus
open import Homotopy.Space.Sphere -- Spheres of arbitrary dimension
open import Homotopy.Space.Sinfty -- The infinite-dimensional sphere
open import Homotopy.Space.Suspension -- Suspensions
```

## Algebra

Formalisations of some of the basic notions in abstract algebra, such as
[[monoids]], [[groups]], [[rings]], and [[modules]] over these. Groups,
rings, and modules have further theory developed, but even then, we
freely admit that no deep results in algebra are formalised here.

```agda
open import Algebra.Monoid
open import Algebra.Group
open import Algebra.Ring
open import Algebra.Ring.Module
```

### Group theory

Groups are an abstraction of the idea of *symmetry* --- which is central
to homotopy type theory. See also [synthetic homotopy theory] above.

```agda
open import Algebra.Group.Free     -- Free groups
open import Algebra.Group.Action   -- Group actions
open import Algebra.Group.Cayley   -- Cayley's theorem
open import Algebra.Group.Concrete -- Groups as higher types
```

We also have a few results about the large-scale categorical structure
of $\Ab$, the category of abelian (or commutative) groups:

```agda
open import Algebra.Group.Ab                -- Abelian groups, and the category Ab
open import Algebra.Group.Ab.Tensor         -- Tensor product of abelian groups
open import Algebra.Group.Ab.Abelianisation -- Abelianisations
```

## Recent additions {#recently-added}

These are the ten most recent commits to the repository, which
introduced new modules. Looking through these would be a good way to
find which of the topics above are currently seeing activity!

::: {#recent-additions}
:::

<!-- Mastodon author links: !-->
<div style="display: none;">
<a rel="me" href="https://types.pl/@amy"></a>
<a rel="me" href="https://types.pl/@totbwf"></a>
</div>
