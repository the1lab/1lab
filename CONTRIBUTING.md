Contributing
------------

Thanks for taking the time to contribute!

This file holds the conventions we use around the codebase, but they're
guidelines, and not strict rules: If you're unsure of something, hop on
[the Discord](https://discord.gg/Zp2e8hYsuX) and ask there, or open [a
discussion thread](https://github.com/plt-amy/1lab/discussions)
if that's more your style.

## General guidelines

British spelling **must** be used throughout: Homotopy fib**re**,
fib**red** category, colo**u**red operad, etc --- both in prose and in
Agda.

Headers **should** be written in sentence case, *not* title case, except
when the concept they introduce is itself commonly written in title case
(e.g. "Structure Identity Principle").

Prose **should** be kept to a width of 72 characters.

The first time a concept is introduced, it **should** appear in bold.

If some text needs to call the reader's attention, it **should** use one
of the "highlight" classes, which have names corresponding to each of the
icons in [`support/web/highlights`]. These **should** use `:::`-fenced
divs:

[`support/web/highlights`]: https://github.com/plt-amy/1lab/blob/main/support/web/highlights

    ::: warning
    Warning text goes here.
    :::

A call-out is also supported in `<details>` elements, but using a plain
attribute rather than a class:

    <details warning>
    <summary>The summary is mandatory.</summary>

    ...

    </details>

## Links

For internal links, wikilinks **should** be used. A wikilink is written
`[[title]]`, or `[[title|anchor]]`. The concrete anchor to which a
wikilink points is determined by its anchor, which is globally unique.

Link targets, called definitions, can be introduced in two ways:

* In a header:
  ```
  # Foo {defines="anchor-1 anchor-2"}
  ```

* As a div:
  ```
  ::: {.definition #anchor-1 alias="anchor-2"}
  [the definition]
  ```

Wikilink targets are case insensitive, and get "mangled" for whitespace:
the anchor `least-upper-bound` can be referred to as `[[least upper
bound]]`, or `[[lub|least upper bound]]` if different textual content is
required, or `[[lub|least-upper-bound]]`. White space **should** be used
instead of dashes at use sites.

## Linking identifiers

An Agda identifier that _has been referred to_ in the current module can
be referred to in prose using `` `name`{.Agda} `` (an inline code block
with class `Agda`). The [HoTT book comparison] uses this feature
extensively.

[HoTT book comparison]: https://github.com/plt-amy/1lab/blob/main/src/HoTT.lagda.md

If the definition does not naturally appear in the code, the following
idiom can be used. The implementation of identifier links prevents their
use in a mutually-recursive way, since it should only be used for things
that the proof actually *depends* on. Cyclic links **should** be
[wikilinks](#links) instead.

    <!--
    ```agda
    _ = identifier-you-want-to-link
    ```
    -->

If the text needs to differ from the identifier, the `ident` attribute
can be used: `` `is an equivalence`{.Agda ident=is-equiv} ``.

Mixfix operators **must** use their "full name" to be picked up: ``
`_∘_`{.Agda} `` is the proper way to refer to the composition operator,
even if it only ever appears infix in the code.

## Commutative diagrams

Our build process supports converting arbitrary bits of LaTeX to SVGs to
be referred to from pages. [These LaTeX packages] are supported, but the
recommended way of working out whether or not a diagram renders
correctly is to actually build the website, since that lets you see
whether or not the image has a reasonable size in the page.

[These LaTeX packages]: https://github.com/plt-amy/1lab/blob/main/default.nix#L18-L27

Diagrams are compiled if they appear in a *fenced* code block with class
`quiver`. Accordingly, most of us use [q.uiver.app](https://q.uiver.app)
to generate our diagrams, using the `tikz-cd` package. After creating
your diagram with Quiver, copy the LaTeX export, sans the permalink
comment, and paste it — maths delimiters and all — into a code block.
The indentation **should** be changed from tabs to two spaces.

    ~~~{.quiver .short-2}
    \[\begin{tikzcd}
      a && b
      \arrow[from=1-1, to=1-3]
    \end{tikzcd}\]
    ~~~

Any LaTeX commands defined in [the preamble] are available in diagrams.
Note that the preamble is not directly loadable using Quiver's macros
functionality since it relies on `\definealphabet`, which is implemented
separately since it requires a shim to work on KaTeX.

[the preamble]: https://github.com/plt-amy/1lab/blob/main/src/preamble.tex

## The structure of a page

Every literate Agda file on the 1Lab **must** follow the following
general structure:

- All import statements **must** appear at the top of the module, within
  an HTML comment.

  Imports **must** grouped by the first component of the module name,
  with the groups sorted alphabetically, with modules _within_ the
  groups sorted by length, longest-first. These rules apply separately
  for `open import`, `import` and `open` statements, which
  **must** appear in this order.

  The tool `support/sort-imports.hs` **should** be used to update code
  to comply to these rules. It can be run as a standalone executable if `stack` is
  available, or with Nix using the following command:

  ```sh
  nix run --experimental-features nix-command -f . sort-imports
  ```

  The modules to format are given as command-line arguments.

- The top-level module name, together with any parameters, **must**
  appear before any prose (incl. the initial header), and **must not**
  be commented.

- Opening and defining private local modules **may** appear before the
  initial header, but **must** appear in an HTML comment if so.

- A level-1 heading **must** be present, with a readable page name. If
  no title is provided, this will be used as the title for the page.

A perfect example of these guidelines is [`Order.Semilattice.Free`],
since it has four different import blocks.

[`Order.Semilattice.Free`]: https://github.com/plt-amy/1lab/blob/main/src/Order/Semilattice/Free.lagda.md

## Agda code style

Agda code **should** be kept to less than 85 columns (this is informed
by how much code can fit on a 1920x1080 screen without a scroll bar). In
an equational reasoning block, anything between `⟨_⟩` does not count for
the line length limit, since those spans can be removed by the user.
(example: the [dual of the modular law] reaches column 136!)

[dual of the modular law]: https://github.com/plt-amy/1lab/blob/main/src/Cat/Allegory/Reasoning.lagda.md#L110

Types **should** be defined directly in `Type _`, if possible, then
later shown to be of a particular truncation level. This rule **may** be
ignored when defining a type out of a truncated HIT.

When mapping from a higher inductive type, any proposition-valued
coherences **should** be defined in an `abstract` block:

```agda
    fold : (f : G → G' .fst) → is-group-hom Grp G' f → G^ab → G' .fst
    fold f gh = Coeq-rec G'.has-is-set f l1
      where abstract
        l1 : ((x , y , z) : G × G × G) → f (x ⋆ y ⋆ z) ≡ f (x ⋆ z ⋆ y)
        l1 (x , y , z) = ...
```

### Things to know

There is a dedicated operator for projecting the "underlying type" of
anything for which this concept makes sense: `⌞ T ⌟`; see
[1Lab.Underlying](https://1lab.dev/1Lab.Underlying.html). Underlying
instances are available for things like:

- `Type` (no effect)
- `n-Type` and `Ω` (projects the underlying type)
- A type like `Σ U ...` (projects the underlying type of the first component)
- Concrete groups (projects the delooping)
- ... probably others ...

### Naming convention

Identifiers **must** be `kebab-case`, though a context-appropriate
separator **should** replace the dash:

- An arrow `→` can replace "to", "implies", etc.:
  `is-equiv→is-embedding`
- The equivalence symbol `≃` can replace "is equivalent to",
  "equivalence", etc.: `Ωⁿ≃Sⁿ-map`
- The identity symbol `≡` can replace "is equal to", etc.: `hcomp≡Glue`,
  `PathP≡Path`

The names of propositions **should** start with the prefix `is-`:
`is-equiv`, `is-group-hom`. The names of more general types **should**
start with an uppercase letter: `Group-on`, `Glue`.

In a theorem, the predicate **should** appear _after_ the thing it
applies to: correct English, not a correct type. `Nat-is-set`, not
`is-set-Nat`. The object should only be named if it is another
definition, and **must not** be included if it is universally
quantified: `is-equiv→is-embedding`, not `f-is-equiv→f-is-embedding`.

Definitions **should** have their names informed by what they prove, but
this process does not need to be entirely mechanic (don't turn the
entire function's type into a name!). If a theorem has an accepted
common name, that **can** be used instead of deriving a name based on
its type.

Sometimes, this can result in verbose names. A bit of verbosity is
preferrable to having a theorem whose name is not memorable. Deciding on
a good name for your lemma can be very hard: don't hesitate to ask on
Discord for help.

Names of record fields whose type is proposition valued **should** start
with the rather silly prefix `has-is`: `has-is-set` is the most common.

When naming a duality lemma, the "concrete dual" (e.g. `Coproduct`)
**should** be a single word, and the dual notion (e.g. `Product` in an
opposite category) **should** have `co` appear as a separate prefix:
hence `is-coproduct→is-co-product`.

The types `PathP` and `SquareP` are the only exceptions to the
kebab-case rule.

### Literate vs code files

All mathematically interesting notions **must** be defined in a literate
Agda file. Non-literate Agda files **should** only be used to define
code that fits under "unfortunately, proof assistants":

- Metaprogramming. Solvers **may** be defined in a non-literate file,
  but a literate explanation is preferred.
- Prelude/re-export modules.
- Modules that simply define more convenient notations
  (e.g. `Algebra.Group.Notation`).
