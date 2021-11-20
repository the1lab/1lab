```

module index where
```

# Cubical 1lab {style="margin-top: 0;"}

A formalised, cross-linked reference resource for mathematics done in
Homotopy Type Theory. Unlike the [HoTT book], the 1lab is not a "linear"
resource: Concepts are presented as a directed graph, with links
indicating _dependencies_. For instance, the statement of the univalence
axiom depends on [_universes_](agda://1Lab.Type), [_propositional
equality_](agda://1Lab.Path) (paths) and [_equivalences_](agda://1Lab.Equiv):

[HoTT book]: https://homotopytypetheory.org/book/

<!--
```
open import 1Lab.Type
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Univalence
open import 1Lab.HLevel
```
-->

```
_ : {ℓ : _} {A B : Type ℓ} → isEquiv (pathToEquiv {A = A} {B})
_ = univalence
```

If you don't know what those concepts refer to, it could be challenging
to figure out what the definition above is even saying - or how it's
proven. Fortunately, every single element there is a link! Try clicking
on the word `isEquiv`{.Agda} - either here in the text, or there in the
code. It'll take you to the definition, which will be highlighted in
orange to draw your attention.

Links are colour-coded to indicate what they point to. In body text,
links rendered in [blue (or purple) sans-serif font](index.html) link to
_pages_; Links rendered in one of the syntax highlighting colours and
`monospace`{.agda ident=Category} link to a _definition_. Specifically,
the following colours are used:

* Blue for records and functions: `isEquiv`{.Agda}, `sym`{.agda}

* Green for inductive constructors, coinductive constructors, and the
endpoints of the interval: `i0`{.agda}

* Maroon for modules: `1Lab.Type`{.Agda}

* Purple for record selectors: `isEqv`{.agda ident="isEquiv.isEqv"}

<!--
```
_ = i0
_ = isEquiv
_ = isEquiv.isEqv
_ = sym
```
-->

## Technology

The 1Lab uses [Iosevka](https://typeof.net/Iosevka/) as its monospace
typeface. Iosevka is licensed under the SIL Open Font License, v1.1, a
copy of which can be found [here](/static/licenses/LICENSE.Iosevka).

Mathematics is rendered using [KaTeX](https://katex.org), and as so, the
1Lab redistributes KaTeX's fonts and stylesheets, even though the
rendering is done entirely at build-time. KaTeX is licensed under the
MIT License, a copy of which can be found
[here](/static/licenses/LICENSE.KaTeX).

Our favicon is Noto Emoji's ice cube (cubical type theory - get it?),
codepoint U+1F9CA. This is the only image from Noto we redistribute.
Noto fonts are licensed under the Apache 2.0 License, a copy of which
can be found [here](/static/licenses/LICENSE.Noto).

Commutative diagrams appearing in body text are created using
[quiver](https://q.uiver.app), and rendered to SVG using a combination of
[rubber-pipe](https://github.com/petrhosek/rubber) and
[pdftocairo](https://poppler.freedesktop.org/), part of the Poppler
project. No part of these projects is redistributed.

And, of course, the formalisation would not be possible without [Agda](https://github.com/agda/agda).

# Type Theory

The first things to be explained are the foundational constructions in
(cubical) type theory - things like types themselves, [universes],
[paths], [equivalences], [glueing] and the [univalence] "axiom". These
are developed under the `1Lab` namespace. Start here:

[universes]: agda://1Lab.Type
[paths]: agda://1Lab.Path
[equivalences]: agda://1Lab.Equiv
[glueing]: agda://1Lab.Univalence#Glue
[univalence]: agda://1Lab.Univalence#univalence

```
-- All of these module names are links you can click!

open import 1Lab.Type            -- Universes

open import 1Lab.Path            -- Path types
open import 1Lab.Path.Groupoid   -- The groupoid structure on types

open import 1Lab.Equiv           -- Equivalences
open import 1Lab.Equiv.Fibrewise -- Fibrewise equivalences

open import 1Lab.HLevel          -- h-Levels
open import 1Lab.HLevel.Retracts -- Closure of h-levels under retractions/isos/equivs
open import 1Lab.HLevel.Sets     -- K, Rijke's theorem, Hedberg's theorem

open import 1Lab.Univalence      -- The univalence "axiom"

open import 1Lab.Data.Dec        -- Decidability, discreteness
open import 1Lab.Data.Bool       -- The type of booleans and its automorphisms
```