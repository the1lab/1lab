```agda
module index where
```

# 1Lab

This website is an experiment in **discoverable formalisation**: an
extensive library of formalised mathematics, presented as an explorable
reference resource. The implementation of a mathematical library as
*literate source code* enables a dual approach to the explanation of
mathematical concepts: the code and the prose are complementary, and
each reader is presented with the opportunity to choose their own
balance of rigid formalisation vs. intuitive explanation.

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

Making the formalisation explorable requires taking the Web-native
nature of such a document seriously: the reader must be able to quickly
jump to a definition if they have not encountered it before, regardless
of whether it is an identifier in the library itself (like
`univalence`{.Agda}), whether it is a _big idea_ mathematical concept
(like a [[monoidal category]]), or whether it is a _punctual_ notion (like
[[surjections are quotient maps]]).

::: mathpar

```agda
_ : ∀ {ℓ} {A B : Type ℓ} → is-equiv (path→equiv {A = A} {B})
_ = univalence
```

:::

The source code snippet above, a re-statement of the [[univalence
principle|univalence]], exemplifies the **web of concepts** perfectly.
Each reader is invited to explore the statement, which leads one to
uncover [[type universes|universe]], [[equivalences]], and
[[path types|path]].

Since the library's size may make jumping into a particular topic feel
daunting, we have done our best to make entry points discoverable as
well. The simplest way to find something is by searching for it. If you
have JavaScript enabled, you can hit <kbd>Ctrl+K</kbd>/<kbd>Cmd+K</kbd>
to bring up the search prompt. Anything that has a name can be searched
for:

- Pages can be looked up by their module name (e.g. _[Algebra.Ring]_),
  or by their title (e.g. _[Abelian groups]_);

- Sections within a page can be looked up by their title, like _[The
  canonical self-indexing > As a fibration][selfindex]_. Keep in mind that
  the fuzzy matching means you don't have to write out the entire
  prefix; it's only displayed so you know where you'll be taken.

- Particular *concepts* can be looked up by any of their shorthands,
  e.g. [[adjunctions compose]] or [[composition of adjunctions]].

- Every definition in the library can be looked up by its identifier,
  like `Precategory`{.Agda}.

[Algebra.Ring]: Algebra.Ring.html
[Abelian groups]: Algebra.Group.Ab.html
[selfindex]: Cat.Displayed.Instances.Slice.html#as-a-fibration

While it is infeasible to maintain a list of everything noteworthy, we
do maintain an association between definitions in the 1Lab and in the
HoTT book: the [HoTT](HoTT.html) page. It's worth mentioning explicitly
that this page is also indexed for search, so you can find definitions
by searching for their name in the book.

## Getting involved

Even though the 1Lab is maintained primarily by [the authors][authors],
it is first and foremost a community project. The literal work takes
place on [GitHub], but ongoing discussion happens on [Discord]. We
welcome all contributions, though we would kindly ask that anyone
submitting a substantial change discuss it on Discord first.

[GitHub]: https://github.com/plt-amy/1lab
[Discord]: https://discord.gg/eQDNM26uKP
[authors]: Authors.html

Our purpose is to make univalent mathematics accessible to everyone who
is interested, regardless of cultural background, age, educational
background, ethnicity, gender identity, or gender expression. **We
believe HoTT is for everyone and are committed to fostering a kind,
welcoming environment**.

## Open-source software

The 1Lab would not be possible without a myriad other free and
open-source projects. Other than our dearest proof assistant
[Agda](https://github.com/agda/agda), the following projects are
integral to the website:

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
  [octicons](https://github.com/primer/octicons), which is distributed
  under the MIT license, which you can find
  [here][LICENSE.Octicons].

* **Diagrams**: Our diagrams are created using [quiver], and rendered
  to SVG using [LaTeX] and [pdftocairo], which is part of the
  Poppler project. No part of these projects is redistributed.

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

[KaTeX]: https://katex.org

## Recently added files

::: {#recent-additions}
:::

<!-- Mastodon author links: !-->
<div style="display: none;">
<a rel="me" href="https://types.pl/@amy"></a>
<a rel="me" href="https://types.pl/@totbwf"></a>
</div>
