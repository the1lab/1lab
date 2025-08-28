Contributing
------------

The 1Lab accepts contributions primarily through pull requests on
GitHub.

* Familiarise yourself with the guidelines below.

* If you're opening a larger pull request, it's a good idea to make
  yourself available for IM discussion on [Discord] or on IRC (`#1lab`
  on [Libera Chat]).

  It's generally a good idea for your PR to consist of a series of
  individually-reviewable commits. If these adhere to the [commit
  guidelines](#commit-guidelines), your PR will be merged rebase. It
  will otherwise be merged squash.
  If you have a bunch of disconnected commits, you can try an
  interactive rebase to arrive at a more logical structure.

* If you're not using Nix, make sure you're using the [correct
  Agda commit] to build your code: we're generally on a bleeding-edge
  version, and testing new language features "in the wild".

[correct Agda commit]: https://github.com/the1lab/1lab/blob/main/support/nix/dep/Agda/github.json#L6
[Discord]: https://discord.gg/Zp2e8hYsuX
[Libera Chat]: https://libera.chat

We welcome all contributions, but please understand that the 1Lab has a
very small team of part-time maintainers. It might take a while for your
PR to be reviewed. Adhering to the guidelines below will help the review
process focus on the things that actually matter instead of wasting
everyones' cycles on style quibbles.

## General guidelines

British spelling **must** be used throughout: homotopy fib**re**,
fib**red** category, colo**u**red operad, etc --- both in prose and in
Agda.

Headers **should** be written in sentence case, *not* title case, except
when the concept they introduce is itself most commonly written in title
case (e.g. "Structure Identity Principle").

Prose **should** be kept to a width of 72 characters. It is recommended
that you configure your editor to display a vertical ruler on both the
72nd and 85th columns, for wrapping prose and code respectively.

Asterisks **must** be used instead of underlines for both emphasis and
strong emphasis. [ATX-style] (`### foo`) headers **must** be used
instead of [setext-style] (`=====`) headers. Headers **must not** have a
closing run of `#`s.

[setext-style]: https://spec.commonmark.org/0.31.2/#setext-headings
[ATX-style]:    https://spec.commonmark.org/0.31.2/#atx-headings

Footnotes should be written with the understanding that, on the primary
(desktop) layout, they will be turned into sidenotes. The content of a
footnote **must** be a complete paragraph, capitalised and punctuated as
such. A footnote marker **must** be attached *after* any punctuation
*attached* to the same word --- including periods, commas, and quotation
marks; but not dashes. Having footnote markers adjacent to closing
parentheses should be avoided.

Footnotes **may** include arbitrary block-level elements, including
display-level maths and commutative diagrams. The content of a footnote
**must be indented by 4 spaces**, if it is to contain multiple blocks.
Follow the indentation-over-alignment rule.

Both enclosing and coordinating dashes **must** be written as
em-dashes with spaces on either side, and they **must** be written in
ASCII in the source code: `A --- b`. We make no use of en-dashes.

Double quotation marks **must** always be used. Clause-final punctuation
**should not** be placed inside quotation marks:

```markdown
<!-- Always -->
However, we can give an intuitive explanation: "A type is a thing that things can be".

<!-- Never -->
However, we can give an intuitive explanation: "A type is a thing that things can be."
```

The abbreviations "i.e." and "e.g." **may** be freely used, but they
**must** be punctuated as indicated. If they appear before a comma,
include both the period and the comma (i.e., like this.)

## Commit guidelines

The first line of a commit **should** have the form `<type>: <short description>`.
Please try to keep the subject line to less than 50 characters (the
`gitcommit` filetype in `vim` will highlight characters past this in
red). The following `<type>`s are commonly used:

* `defn`: Generically used for new maths with accompanying prose.

  The short description should just be what you added, as a noun phrase.

* `chore`: Repository maintenance and mathematically uninteresting refactors.

  The short description should be present tense and imperative mood
  ("move loop spaces to their own file", not "moved loop spaces to their
  own file" or "moves loop spaces to their own file").

* `web`: Changes to the website infrastructure, including the build system.

  The short description should be in the imperative mood, as above.

* `fixup`: Generally squashed away.

The commit body **may** include further elaboration on what is being
done, if necessary; simple changes can get away with no commit body at
all, but in that case please mention them in the pull request. The
commit body **should** be line-wrapped at 72 characters.

The build system understands `Co-Authored-By` lines, and will consider
anyone mentioned there as an author when generating the page's sidebar
credits.

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
  to comply to these rules. It can be run as a standalone executable if
  `stack` is available, or with Nix using the following command:

  ```sh
  nix run --experimental-features nix-command -f . sort-imports
  ```

  The modules to format are given as command-line arguments. If none are
  given, the default is to format everything.

- The top-level module name, together with any parameters, **must**
  appear before any prose (incl. the initial header), and **must not**
  be commented.

  If the top-level module has a long telescope, *it* **may** be
  commented out, but the keyword `module` and the module name **must**
  still appear on the page.

  Opening and defining private local modules **may** appear before the
  initial header, but **must** appear in an HTML comment if so.

- A level-1 heading **must** be present, with a readable page name. If
  no title is provided, this will be used as the title for the page.

- Pandoc block-level elements (*including* comments) **must** always
  have a blank line between them, even if Pandoc would naturally insert a
  paragraph break there.

  Keep in mind that display maths can act as both a block-level (if it
  is *between* paragraphs) and an inline-level element (if it *belongs
  to* a paragraph). This is reflected in the source code by whether the
  maths is separated with blank lines.

- HTML `<details>` tags **should** be used both for the purposes of
  eliding uninteresting formalisation and **may** be used for including
  digressions/alternative perspectives/extra details in the prose.

  Sidenotes **should** be preferred for elaborating on parts of a
  sentence without interrupting the block-level flow of an article.

### Callouts

If some text needs to call the reader's attention, it **should** use one
of the "highlight" classes, which have names corresponding to each of the
icons in [`support/web/highlights`]. These **should** use `:::`-fenced
divs:

[`support/web/highlights`]: https://github.com/the1lab/1lab/blob/main/support/web/highlights

    ::: warning
    Warning text goes here.
    :::

A call-out is also supported in `<details>` elements, but using a plain
attribute rather than a class:

    <details warning>
    <summary>The summary is mandatory.</summary>

    ...

    </details>

### Wikilinks

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
  :::
  ```

The contents of a definition `<div>` are saved as a "fragment", and will
be displayed to the user when they hover any link which points to that
definition; write them with this in mind. The definiens **must** appear,
in bold, within the definition block.

If a term has a definition, it **should** be linked to the first time it
appears under each level-2 header. It **must** be linked the first time
it appears inside a definition `<div>`; the frontend supports recursive
popups.

Definitions **may** point to a commented-out `<div>`, so that (they by
default) they don't interrupt the flow of the page. These commented-out
div definitions **should** be preferred over header definitions. They
**should** be written in traditional mathematical
"definition-theorem-proof" style.

Wikilink targets are case insensitive, and get "mangled" for whitespace:
the anchor `least-upper-bound` can be referred to as `[[least upper
bound]]`, or `[[lub|least upper bound]]` if different textual content is
required, or `[[lub|least-upper-bound]]`. White space **should** be used
instead of dashes at use sites.

### Linking to Agda names

An Agda identifier that _has been referred to_ in the current module can
be referred to in prose using `` `name`{.Agda} `` (an inline code block
with class `Agda`). The [HoTT book comparison] uses this feature
extensively.

[HoTT book comparison]: https://github.com/the1lab/1lab/blob/main/src/HoTT.lagda.md

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

### Commutative diagrams

Our build process supports converting arbitrary bits of LaTeX to SVGs to
be referred to from pages. [These LaTeX packages] are supported, but the
recommended way of working out whether or not a diagram renders
correctly is to actually build the website, since that lets you see
whether or not the image has a reasonable size in the page.

[These LaTeX packages]: https://github.com/the1lab/1lab/blob/main/default.nix#L18-L27

Diagrams are compiled if they appear in a *fenced* code block with class
`quiver`. Accordingly, most of us use [q.uiver.app](https://q.uiver.app)
to generate our diagrams, using the `tikz-cd` package. After creating
your diagram with Quiver, copy the LaTeX export, sans the permalink
comment, and paste it — maths delimiters and all — into a code block.
The indentation **should** be changed from tabs to two spaces.

    ~~~{.quiver}
    \[\begin{tikzcd}
      a && b
      \arrow[from=1-1, to=1-3]
    \end{tikzcd}\]
    ~~~

Any LaTeX commands defined in [the preamble] are available in diagrams.
Note that the preamble is not directly loadable using Quiver's macros
functionality since it relies on `\definealphabet`, which is implemented
separately since it requires a shim to work on KaTeX.

[the preamble]: https://github.com/the1lab/1lab/blob/main/src/preamble.tex

If commutative diagrams on the page should be rendered as part of a
paragraph, i.e. they logically belong to the sentence, you can add the
classes `attach-above`, `attach-below` and/or `attach-around` to remove
margin above, below, or in both block directions.

## The structure of a module

Agda code **should** be kept to less than 85 columns (this is informed
by how much code can fit on a 1920x1080 screen without overflow in the
inline direction). In an equational reasoning block, anything between
`⟨_⟩` does not count for the line length limit, since those spans can be
removed by the user. (e.g., the [dual of the modular law] reaches
column 136!)

[dual of the modular law]: https://github.com/the1lab/1lab/blob/main/src/Cat/Allegory/Reasoning.lagda.md#L110

In laid-out syntax, **two spaces of indentation should be used**,
instead of alignment, whenever possible. We refer to moving to the next
multiple-of-two indentation as "a step". There are some situations
where Agda's grammar *mandates* deeper indentation, particularly when
layout stacking and `module` declarations are involved. Specific rules
for laying out function bodies and declaration signatures are made
explicit below.

```agda
-- Always:
foo =
  let
    x = 1
  in x

-- Never (code aligned rather than indented):
foo =
  let x = 1
   in x

foo = let x = 1
       in x
```

Modules in the `Cat` and `Order` namespaces **should** use `Cat.Prelude`
over `1Lab.Prelude`. Modules in the `1Lab` namespace **should not**
import `1Lab.Prelude`.

Generalizable variables **must not** be exported. Their use is
encouraged to clean up long telescopes. Keep in mind that instance
search does not work in contexts where there are indeterminate types. In
these situations (e.g., theorems about list membership), binders
**should** be explicitly annotated.

Local instances of record and "reasoning" modules **may** *only* be
exported from record declarations *if* they are instantiated with one of
the fields. Keep in mind that this will increase the time spent checking
the record, proportional to how many definitions are in the instantiated
module. In general, large `record` declarations **should** export only
instances of other `record` modules, and not "reasoning" modules.

Instantiated module aliases **must not** be exported from parametrised
anonymous modules.

Top-level modules **may** be parametrised. There are reasons to avoid
this: if you open the module *without* parameters, any instances defined
therein will be unusable. This is frequently a problem when defining
constructions on categories, where the new type of morphisms should be
visibly parametrised by the category it is defined over, but there are
cases where we need to mention this type applied to distinct categories,
and we need an [`H-Level`] instance at both instantiations. In cases
like this, generalizable variables and/or anonymous parametrised modules
**should** be used instead.

### Formatting function definitions

These rules apply to the right-hand sides of clauses (top-level, `let`
and `where` function definitions); to the bodies of trailing `λ`
expressions; and to the clauses in a `λ where` expression (extended
lambda).

In most situations, the RHS of a clause **should**, to the extent
possible, be on the same line as the LHS; see [formatting equational
reasoning](#formatting-equational-reasoning) for the primary exception.
The conflicts this may cause with the indentation-over-alignment rule
are to be resolved as follows:

* If the RHS is a `let` expression, break *before* `let`; but see the
  [exception for short `let`s](#exceptional-formatting-for-lets) below.
* If the RHS is a `record` expression, break *after* `record`.
* If the RHS is a `λ where` or `record where` expression, break *before*
  `λ`/`record` if the clause being defined has a `where` declaration
  (this is required by Agda's syntax); and break *after* `where`
  otherwise.

```agda
-- Never (bindings backwards relative to `let` keyword):
f x = let
  y = 1
  in y

-- Okay:
f x = record where
  ...

f x = record
  { a = _
  ; b = _
  }

f x =
  record where
    ...
  where
    ...
```

If the RHS is an application, the LHS line **should** include the head
function, and as many arguments as possible, respecting the rules above
if there is a trailing block argument. Arguments placed on continuing
lines **must** be indented a step relative to the clause. If the head
function can't be placed on the LHS line because of the length limit,
the entire body **should** be moved to a continuing line, which itself
**must** be indented a step. In this situation, the subsequent arguments
**should** be indented *two* steps (relative to the clause).

```agda
-- If possible, prefer:
RL[e]-invertible : C.is-invertible (R.₁ (L.₁ e))
RL[e]-invertible = C.strong-mono+epi→invertible
  RL[e]-strong-mono
  RL[e]-epic

-- Over:
RL[e]-invertible : C.is-invertible (R.₁ (L.₁ e))
RL[e]-invertible =
  C.strong-mono+epi→invertible
    RL[e]-strong-mono
    RL[e]-epic

-- But this is allowable if C.strong-mono+epi→invertible wouldn't fit on
-- the line above due to the line length limit.
```

When broken over multiple lines, binary operators (including the `$`
application operators) **should** always be on the *start* ("leading")
of continuing lines, rather than on the end of the line above ("trailing").

```agda
-- Always:
RL[m]∘RL[e]-invertible
  : C.is-invertible (R.₁ (L.₁ m) C.∘ R.₁ (L.₁ e))
RL[m]∘RL[e]-invertible = C.subst-is-invertible (R.expand (L.expand factors))
  $ R.F-map-invertible
  $ is-reflective→left-unit-is-iso L⊣R reflective

-- Never (trailing operators):
RL[m]∘RL[e]-invertible
  : C.is-invertible (R.₁ (L.₁ m) C.∘ R.₁ (L.₁ e))
RL[m]∘RL[e]-invertible =
  C.subst-is-invertible (R.expand (L.expand factors)) $
  R.F-map-invertible $
  is-reflective→left-unit-is-iso L⊣R reflective
```

If a continuing line *itself* has continuing arguments, *these* should
be indented *farther* than the function itself, and always aligned to a
multiple of two spaces.

```agda
-- Prefer:
unit-strong-mono : C.is-strong-mono (η x)
unit-strong-mono = C.strong-mono-cancell (R.₁ (L.₁ f)) (η x)
  $ C.subst-is-strong-mono (unit.is-natural _ _ _)
  $ C.strong-mono-∘ (η (R.₀ a)) f
      (C.invertible→strong-mono
        (is-reflective→unit-right-is-iso L⊣R reflective))
      f-strong-mono

-- Over:
unit-strong-mono : C.is-strong-mono (η x)
unit-strong-mono = C.strong-mono-cancell (R.₁ (L.₁ f)) (η x)
  $ C.subst-is-strong-mono (unit.is-natural _ _ _)
  $ C.strong-mono-∘ (η (R.₀ a)) f
    (C.invertible→strong-mono
      (is-reflective→unit-right-is-iso L⊣R reflective))
    f-strong-mono
```

If the entire body is operator applications, you **may** indent the
*first* line enough to bring all the operands into alignment (which,
depending on the length of the operator, may not be an integer number of
indentation steps), while keeping the subsequent lines aligned a single
step ahead of the clause.

```agda
-- Okay (discretionary extra indentation for first line of body):
stability-var {Γ = Γ , σ} {τ = τ} (pop x) =
    (⟦ ⟦ x ⟧ⁿ ⟧₁ .map .is-natural Γ (Γ , σ) (drop stop) $ₚ idsec Γ)
  ∙ ap (⟦ τ ⟧₀ .dom .F₁ (drop stop)) (stability-var x)
  ∙ sym (Nfa.reflectₙ (normalisation τ))

-- Also okay (normal rule for continuing arguments applies)
stability-var {Γ = Γ , σ} {τ = τ} (pop x) =
  (⟦ ⟦ x ⟧ⁿ ⟧₁ .map .is-natural Γ (Γ , σ) (drop stop) $ₚ idsec Γ)
    ∙ ap (⟦ τ ⟧₀ .dom .F₁ (drop stop)) (stability-var x)
    ∙ sym (Nfa.reflectₙ (normalisation τ))
```

#### Exceptional formatting for `let`s

If a function body is a `let` expression with a single binding, and
short enough for the *entire* `let` construct to fit in a single line,
you **may** write it as a "header" for the body of the function. In this
case, the `let` should appear in its own line, indented a step relative
to the clause. The body **should not** be indented a step relative to
the `let` keyword: it should start aligned with the `let`.

```agda
-- Okay:
foo =
  let bar = 123 in
  bar
```

#### Formatting equational reasoning

Exceptionally, a proof by equational reasoning **should** always start
on a new line, indented a step relative to the function definition.  Two
styles are allowed depending on the length of the expressions being
equated.

* You **should** have the equations to the right of the expressions, with
  all the `≡⟨`s aligned. The `⟩`s need not be aligned.

    ```agda
    proof =
      some expression ≡⟨ a proof ⟩
      some other term ≡⟨ other proof ⟩
      the final term  ∎
    ```

* Alternatively, if the expressions being compared are themselves very
  long, you **may** have the equations on lines *between* the expressions,
  in which case they should be indented an additional step.

    ```agda
      proof =
        some expression
          ≡⟨ a proof ⟩
        some other term
          ≡⟨ other proof ⟩
        the final term
          ∎
    ```

This applies to any analogous form of transitive reasoning combinator
(e.g. equivalence reasoning, preorder reasoning, pointed function
reasoning). As usual, code within the `⟨_⟩` does not contribute to the
line length limit.

#### Formatting `where` clauses

If the RHS of a clause is a single line, regardless of whether it is on
the same line as the LHS, a `where` clause **should** be attached on
this line, and the `where` declarations **should** be indented another
step.

```agda
-- Always:
foo = {! some short code !} where
  bar = ...

-- Never (early break for where clause):
foo = {! some short code !}
  where
    bar = ...

-- Never (early break for where clause with unindented declarations):
foo = {! some short code !}
  where
  bar = ...

```

If the RHS is too long for the `where` clause to fit on the same line,
it **should** appear in a continuing line; it **must** be on a
continuing line if the RHS itself has continuing lines. As usual, this
mandates a step of indentation for the `where` keyword. In this case,
the `where` declarations **should** be indented *two* steps, four
spaces, relative to the function declaration.

```agda
-- Always:
foo = {! some extremely long code that that works out to just about 85 characters !}
  where
    bar = ...

foo =
  {! some very long code !}
  $ {! with continuation lines !}
  where
    bar : ...

-- Never (line length limit violation):
foo = {! some extremely long code that that works out to just about 85 characters !} where
  bar = ...

-- Never (no indentation before where decls in anonymous where module):
foo = {! some extremely long code that that works out to just about 85 characters !}
  where
  bar = ...

-- Never (additional indentation relative to continuing lines):
foo =
  {! some very long code !}
  $ {! with continuation lines !}
    where
      bar : ...
```

The extra step of indentation for the `where`-declarations **may** be
skipped if the `where` module is named.

```agda
-- These are both okay:
foo = {! some very long code !}
  module foo where
    bar : ...

foo = {! some very long code !}
  module foo where
  bar : ...
```

The line break after the `where` keyword **may** be skipped if the
resulting layout respects the line length limit.

```agda
-- Both okay:
foo = {! pretty short code !} where bar = 123
foo = {! some extremely long code that that works out to just about 85 characters !}
  where bar = 123
```

Helper functions that may need to be used in client code, but have very
long telescopes/no sensible top-level name, **may** be placed in a named
`where` module:

```agda
ua→ {e = e} {B} {f₀ = f₀} {f₁} h =
  (λ i a → comp (λ j → B (i ∨ ~ j) (x' i (~ j) a)) (∂ i) (sys i a))
  module ua→ where

  -- ...

  filler : ∀ i j (a : ua e i) → B (i ∨ ~ j) (x' i (~ j) a)
  filler i j a = fill (λ j → B (i ∨ ~ j) (x' i (~ j) a)) (∂ i) j (sys i a)
```

> [!WARNING]
> Anything inside a named `where` module has the same visibility as the
> function it belongs to. Be careful not to accidentally export, e.g.,
> local copies of helper modules from a named `where` module!

The clauses of pattern- and copattern-matching definitions **should**
maintain vertical alignment between corresponding arguments, and between
their `=` signs, wherever this wouldn't conflict with the line length
limit. This **may** be skipped if the patterns on distinct lines have
too great a length difference. If a clause is multiple lines, subsequent
clauses **should not** have their arguments aligned.

```agda
-- Prefer:
max zero    zero    = zero
max zero    (suc n) = suc n
max (suc n) zero    = suc n
max (suc n) (suc k) = suc k

-- Over:
max zero zero = zero
max zero (suc n) = suc n
max (suc n) zero = suc n
max (suc n) (suc k) = suc k

-- Never (aligned '='s are visually disconnected by body of first clause):
foo (very-long a) (even-longer b) =
  let
    ...
  in ...
foo short short                   = ?
```

Definitions, including `let` bindings, **must** be separated by at least
one blank line *in the same code block*, or by prose. A declaration and
a definition for the same function **should not** have a line break, but
may have a prose break.

When giving a copattern-matching definition with many fields, you
**should** try to sink all the "proof" fields towards the bottom, and
**may** include a blank line between the "data" and the "proofs".

```agda
-- Prefer:
ni .eta x .η _ = B.id
ni .inv x .η _ = B.id

ni .eta x .is-natural _ _ _ = B.id-comm-sym
ni .inv x .is-natural _ _ _ = B.id-comm-sym
ni .eta∘inv x     = ext λ _ → B.idl _
ni .inv∘eta x     = ext λ _ → B.idl _
ni .natural x y f = ext λ _ → B.idr _ ∙ ap (B._∘ _) (y .F-id)

-- Over:
ni .eta x .η _              = B.id
ni .eta x .is-natural _ _ _ = B.id-comm-sym
ni .inv x .η _              = B.id
ni .inv x .is-natural _ _ _ = B.id-comm-sym
ni .eta∘inv x               = ext λ _ → B.idl _
ni .inv∘eta x               = ext λ _ → B.idl _
ni .natural x y f           = ext λ _ →
  B.idr _ ∙ ap (B._∘ _) (y .F-id)
```

In a case like the above, where all the "proof" fields are
uninteresting, consider putting them in a `<details>` block, or in a
Markdown comment.

### Formatting type signatures

Unlike a function body, if a type signature needs to be broken over
multiple lines, it **must** *start* on the next line, and on the next
indentation step. Arrows in continuing lines **must** be aligned with
the colon on the first line.

```agda
-- Always:
Triangle
  : ∀ {ℓ} {A : Type ℓ} {x y z : A}
  → (p : x ≡ y) (q : x ≡ z) (r : y ≡ z)
  → Type ℓ

-- Never (indentation over alignment):
Triangle : ∀ {ℓ} {A : Type ℓ} {x y z : A}
         → (p : x ≡ y) (q : x ≡ z) (r : y ≡ z)
         → Type ℓ

Triangle : ∀ {ℓ} {A : Type ℓ} {x y z : A}
  → (p : x ≡ y) (q : x ≡ z) (r : y ≡ z)
  → Type ℓ
```

If you have a long chain of named binders, you **may** either break
these onto multiple lines with arrows (which should be aligned to the
colon as above), or without. If you choose to break them without arrows,
the binders **must** be indented another step, which brings them into
alignment with the binders on the preceding line:

```agda
-- Okay:
Triangle
  : ∀ {ℓ} {A : Type ℓ} {x y z : A}
  → (p : x ≡ y) (q : x ≡ z)
    (r : y ≡ z)
  → Type ℓ

-- Never (binder backwards relative to others in its group):
Triangle
  : ∀ {ℓ} {A : Type ℓ} {x y z : A}
  → (p : x ≡ y) (q : x ≡ z)
  (r : y ≡ z)
  → Type ℓ
```

If possible within the bounds of comprehensibility, record fields and
inductive constructor names **should** be chosen to encourage vertical
alignment at use-sites. *Example*: we generally shorten `commutes` to
`com` to match the length of `map` when defining e.g. maps in slice
categories, but we would *not* shorten `monic` to `mon`.

In a sequence of adjacent inductive constructors/record fields with
single-line type signatures, these signatures **should** be vertically
aligned, by inserting whitespace *before* the colon. This **may** be
skipped if the fields have long types and a big difference in name
length.

In a sequence of adjacent inductive constructors/record fields with
single-line type signatures, their return types **may** be aligned at
your discretion; you **may** also align the types of "analogous"
arguments. When foregoing alignment, the signatures **should** be
ordered to avoid "jumps" between line lengths.

```agda
-- Okay (return types aligned):
data Nf where
  lam  : Nf (Γ , τ) σ       → Nf Γ (τ `⇒ σ)
  pair : Nf Γ τ → Nf Γ σ    → Nf Γ (τ `× σ)
  unit :                      Nf Γ `⊤
  ne   : ∀ {x} → Ne Γ (` x) → Nf Γ (` x)

-- Okay (no alignment, but line lengths are monotonic)
data Nf where
  unit : Nf Γ `⊤
  lam  : Nf (Γ , τ) σ → Nf Γ (τ `⇒ σ)
  pair : Nf Γ τ → Nf Γ σ → Nf Γ (τ `× σ)
  ne   : ∀ {x} → Ne Γ (` x) → Nf Γ (` x)

-- Suboptimal (strange jump in line lengths):
data Nf where
  lam  : Nf (Γ , τ) σ → Nf Γ (τ `⇒ σ)
  pair : Nf Γ τ → Nf Γ σ → Nf Γ (τ `× σ)
  unit : Nf Γ `⊤
  ne   : ∀ {x} → Ne Γ (` x) → Nf Γ (` x)
```

### Notation classes

There is a dedicated operator for projecting the "underlying type" of
anything for which this concept makes sense: `⌞ T ⌟`; see
[1Lab.Underlying](https://1lab.dev/1Lab.Underlying.html). Underlying
instances are available for things like:

- `Type` (no effect)
- `n-Type` and `Ω` (projects the underlying type)
- A type like `Σ U ...` (projects the underlying type of the first component)
- Concrete groups (projects the delooping)
- ... probably others ...

Other "notation classes" include `Idiom`, `Bind`, `Membership` and
`Funlike`. Ordinary definitions **must not** quantify over instances of
these classes: they have no laws, and should not appear in any theorem
statements. They **may** be quantified over to define "lifting"
instances, however.

### H-Level automation

The [`H-Level`] class **should** be used, wherever possible, for
deriving hlevels. As explained there, "leaf" instances should be
declared in terms of a lower bound, not an exact level. Local
assumptions, e.g. that some map is an embedding, generally overlap with
existing instances, and should not be made into local overlapping
instances.

```agda
-- This will not work:
instance H-Level-Nat : H-Level Nat 2
```

[`H-Level`]: https://1lab.dev/1Lab.HLevel.Closure.html#automation

You can use [`prop!`] to summon a `PathP` in any propositional type, and
[`hlevel!`] to summon the canonical element of a contractible type.

[`prop!`]: https://1lab.dev/1Lab.Reflection.HLevel.html#prop!
[`hlevel!`]: https://1lab.dev/1Lab.HLevel.Closure.html#hlevel!

Definitions which take [`is-hlevel`] arguments often have a version
which take [`H-Level`] instances, having the same name, but suffixed
with a `!`: [`el!`], [`n-Tr-elim!`], [`injection→extensional!`]. Use
sites **should** prefer the instance-argument version. You **should**
provide these versions for any definitions you make. If the `is-hlevel`
arguments are for level two and above, you **may** write *only* the
version taking an instance argument.

[`is-hlevel`]: https://1lab.dev/1Lab.HLevel.html#is-hlevel
[`el!`]: https://1lab.dev/1Lab.Reflection.HLevel.html#el!
[`n-Tr-elim!`]: https://1lab.dev/Homotopy.Truncation.html#n-Tr-elim!
[`injection→extensional!`]: https://1lab.dev/1Lab.Extensionality.html#injection→extensional!

Instances of `H-Level` **must not** appear as instance *fields* in a
record type. This will simply not work. Instead, you can define an
[`hlevel-projection`] instance as a stand-in for an instance of
`H-Level` for *any* neutral which quotes to a `def` headed by its index.

An instance of `hlevel-projection` for some name `func` requires an
hlevel lemma that takes a single visible argument. The `get-argument`
function must recover this relevant argument from *the argument list* of
a neutral application of `func`. The `has-level` field should produce a
`Term` representing the hlevel *for a recovered argument*. Generally,
`has-level` will be a constant function returning `lit (nat K)`.

[`hlevel-projection`]: https://1lab.dev/1Lab.Reflection.HLevel.html#hlevel-projection

Generally, `hlevel-projection` instances are used for record fields.
They can be used instead of overlapping instances to write `H-Level`
instances for type families defined by recursion, see
[`hlevel-proj-is-iterative-embedding`].

[`hlevel-proj-is-iterative-embedding`]: https://1lab.dev/Data.Set.Material.html#hlevel-proj-is-iterative-embedding

### Record types

Record types that carry identities **should** be `no-eta-equality`. In
general, `no-eta-equality` should be preferred over `eta-equality`, as
this gives us better control over which telescopes the conversion
checker will look into. Record constructors **may** be named, especially
`eta-equality` record constructors; but, in general, `record` literals
(and `record where` syntax) **should** be preferred.

Constructors of `no-eta-equality` records **may** be marked `INLINE`.
Agda will turn `INLINE` record constructors into coclauses when they
appear, *even if by inlining*, on the immediate RHS of a definition.
This allows giving definitions with short normal forms without repeating
a long list of copatterns. You can refer to the anonymous constructor of
a record as the `constructor` "field in the record module":

```agda
record Prebicategory o ℓ where
  no-eta-equality
  field
    Ob  : Type o
    Hom : Ob → Ob → Precategory ℓ ℓ'
  ...
{-# INLINE Prebicategory.constructor #-}
```

Constructor inlining does not happen on the right-hand sides of `INLINE`
functions. For this to happen, *the function **must** be marked `INLINE`
between its declaration and definition*, after its type signature but
before any of its clauses. This allows convenient definitions of
"copattern-matching macros", see e.g. [`with-trivial-grading`] and
[`with-thin-display`] in `Cat.Displayed.Base`.

[`with-trivial-grading`]: https://1lab.dev/Cat.Displayed.Base.html#with-trivial-grading
[`with-thin-display`]: https://1lab.dev/Cat.Displayed.Base.html#with-thin-display

When defining a type family by recursion, it is often convenient to make
it definitionally injective by wrapping it in a single-field `record`
type; see the [orderings on rationals]. The constructor and field
**should** be named `lift` and `lower`. These records **may** be
`eta-equality`. If they're not propositions, they **should** have an
`Extensional` instance projecting the underlying field.

[orderings on rationals]: https://1lab.dev/Data.Rational.Order.html#_%E2%89%A4_

If a type is a `record` or `data`type, it **should** have an `H-Level`
instance. Instances for `record` types can often be defined
automatically by [`declare-record-hlevel`], exported from both preludes.
Record types **should** also generally have [`Extensional`] instances.
At time of writing, there is no automation for writing these, but
[`declare-record-iso`] produces an isomorphism that you can use to lift
`Extensional` instances.

[`declare-record-hlevel`]: https://1Lab.dev/1Lab.Reflection.Record.html#declare-record-hlevel
[`declare-record-iso`]: https://1Lab.dev/1Lab.Reflection.Record.html#declare-record-iso
[`Extensional`]: https://1lab.dev/1Lab.Extensionality.html#Extensional

### Algebraic structures

We define algebraic structures in layers, roughly corresponding to
*stuff*, *structure*, and *property*. The later layers should be
*parametrised over* the earlier layers: the properties are parametrised
over the structure and the structure is parametrised over the stuff.
Generically, this looks like:

```agda
record is-widget {A : Type} (op : A → A → A) : Type
record Widget-on (A : Type) where
  field
    op            : A → A → A
    has-is-widget : is-widget op
  open is-widget has-is-widget public
```

The type of properties **must** have an accompanying `H-Level` instance
expressing that it is a proposition. Otherwise, property is to be
understood in the sense of "fully faithful" rather than "pseudomonic":
property-like structure, which places additional preservation demands on
the morphisms, should be part of the structure.

The type packaging together stuff, structure and property is usually
*defined* as the type of objects of a category of widgets. We tend to
define these categories as displayed over `Sets`, using
[Cat.Displayed.Univalence.Thin](https://1Lab.dev/Cat.Displayed.Univalence.Thin.html).
This requires you to set up a proposition expressing what it means for a
function of sets to preserve Widget-structure:

```agda
record is-widget-hom {A B : Type} (f : A → B) (x : Widget-on A) (y : Widget-on B) where
  private
    module x = Widget-on x
    module y = Widget-on y

  field
    pres-op : ∀ {a b} → f (x.op a b) ≡ y.op (f a) (f b)

Widget-structure : Thin-structure _ Widget-on
Widget-structure .is-hom f x y = el! (is-widget-hom f x y)
[...]

module Widgets = Cat.Reasoning Widgets
Widget = Widgets.Ob
```

This applies beyond finitary algebraic theories on the category of sets:
for example, monads and comonads are defined in a similar way, with
`is-monad`/`Monad-on`/`Monad` records.

#### Universal objects

We define concrete cases universal objects in components, following a
"representability determines functoriality" philosophy. The result ends
up in layers similar to those of algebraic structures, though we
generally stop at the "structure" layer, since (e.g.) "some product of
unspecified objects in a fixed category" is not a very useful type.

The property record **should** be a proposition, with no extra
assumptions (strictness/univalence) imposed on the category; if the
category is univalent, then the resulting structure **should** be a
proposition, too. Good category theory ensures that this is always the
case if you place the structure/property split on the correct field.
Generally, the property includes the universal map, but is parametrised
over an entire *diagram* we're showing is universal.

```agda
record is-product {A B P} (π₁ : Hom P A) (π₂ : Hom P B) : Type (o ⊔ ℓ) where
record Product (A B : Ob) : Type (o ⊔ ℓ) where
  field
    apex : Ob
    π₁ : Hom apex A
    π₂ : Hom apex B
    has-is-product : is-product π₁ π₂
```

If `is-product` were defined only over the objects, it would not be a
proposition. Preservation of universal objects is usually stated as
saying that *pasting* with a functor preserves the property.

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
this process does not need to be entirely mechanical (don't turn the
entire function's type into a name!). If a theorem has an accepted
common name, that **can** be used instead of deriving a name based on
its type.

Sometimes, this can result in verbose names. A bit of verbosity is
preferable to having a theorem whose name is not memorable. Deciding on
a good name for your lemma can be very hard: don't hesitate to ask on
Discord for help.

Names of record fields whose type is proposition valued **should** start
with the rather silly prefix `has-is`: `has-is-set` is the most common.

When naming a duality lemma, the "concrete dual" (e.g. `Coproduct`)
**should** be a single word, and the dual notion (e.g. `Product` in an
opposite category) **should** have `co` appear as a separate prefix:
hence `is-coproduct→is-co-product`.

The displayed version of a `Thing` **may** be called `ThingP`, following
`Pathp` and `SquareP`.

### Literate vs code files

All mathematically interesting notions **must** be defined in a literate
Agda file. Non-literate Agda files **should** only be used to define
code that fits under "unfortunately, proof assistants":

- Metaprogramming. Solvers **may** be defined in a non-literate file,
  but a literate explanation is preferred.
- Prelude/re-export modules.
- Modules that simply define more convenient notations
  (e.g. `Algebra.Group.Notation`).
