<!--
```agda
{-# OPTIONS --allow-unsolved-metas #-}
open import 1Lab.Reflection.Induction
open import 1Lab.Path.Cartesian
open import 1Lab.Prelude

open import Data.Id.Properties
open import Data.Bool
```
-->

```agda
module Mikan where
```

# Mikan {defines="mikan"}

Mikan[^fork] is a free and libre interactive proof assistant for cubical
type theory, featuring a computational interpretation of univalence
among a variety of schemas for inductive and coinductive definitions.
Proofs are constructed incrementally in a flexible concrete syntax based
on mixfix operators, and organised through an expressive system of
parametrised modules. Mikan is maintained on [Codeberg] as part of the
[1Lab] project.

::: note
More about the motivation behind the fork can be read in the original
[announcement]. This page serves as a temporary home for Mikan-related
documentation.
:::

[Codeberg]: https://codeberg.org/1lab/mikan
[announcement]: https://types.pl/@amy/116522250630340534
[1Lab]: index.html

[^fork]:
    Mikan (/mɪˈkɑːn/) is named after the Japanese name for the [*Citrus
    unshiu*](https://en.wikipedia.org/wiki/Citrus_unshiu).

    Mikan was forked from the dependently-typed programming language
    Agda during development of upstream version 2.9.0; specifically, the
    last commit that is part of upstream history is
    [`a96a3920`].

    Mikan is dually licensed under the terms of the GNU General Public
    License v3 (or later) and under the Agda (MIT) license.

[`a96a3920`]: https://codeberg.org/1lab/mikan/commit/a96a39205d4b423c494124cfaee586cd336e674d

### About the fork

This section collects the answers to questions that have been asked
regarding Mikan development since the original announcement, as well as
clarifying some points in the original FAQ.

#### What's the news on Mikan development?

For the technically minded, an up-to-date summary of Mikan's development
compared to upstream will always be available by inspecting the commit
history, which [can be done online][history]. Work has progressed on the
following fronts:

[history]: https://codeberg.org/1lab/mikan/compare/a96a39205d4b423c494124cfaee586cd336e674d..main

* As of writing (June 2026), **work has concluded on removing the
  language features we planned to cut,** including those that were
  deeply entwined with the syntax of the core type theory. This has
  simplified many parts of the codebase which, for example, no longer
  need to keep track of modalities, or do not need to support two
  disjoint behaviours toggled by a flag.

  Test cases for the removed features have either been revised, if they
  could be adapted to stress a behaviour of the type theory we support,
  or removed entirely. We've also removed a lot of other obsolete files
  when compared to upstream, including kept tests that were *already*
  outdated, thousands of lines of notes, the source code for a variety
  papers, and a lot of stale documentation.

  The test suite, which was previously a `sed`-powered and in large
  driven by the `Makefile`, was entirely ported to `tasty`, and made to
  work through `Cabal` as for an ordinary Haskell package. This includes
  the ordinary interaction tests, which can now be executed in parallel,
  and the interaction tests driven by a custom Haskell program, whose
  linking requirements previously locked developers into the deprecated
  `v1` Cabal workflow. Our CI has been thoroughly Nix-ified and now
  publishes [developer documentation] for the `main` branch.

[developer documentation]: https://1lab.codeberg.page/mikan/

* The error reporting infrastructure in Mikan's elaborator has been
  refactored to ease the distinction between errors, which are thrown
  for control flow, and warnings, which are accumulated in a side table
  and reported when elaboration finishes.  This is a marked improvement
  in developer experience, since new diagnostics no longer need to be
  added to one of two monster types at the root of the dependency tree,
  but the primary motivation is user experience.

  Mikan **now reports multiple type errors**, in particular
  through a generic recovery strategy for errors thrown during term
  elaboration, but also through focused refactorings of the error
  reporting in components like instance search. Not every error can be
  recovered from yet: scope-checking errors are still fatal, as are
  those thrown during checking of left-hand sides.

#### Will Mikan keep support for book HoTT?

This is a question from the original FAQ which subsequent discussion has
revealed is secretly two questions wearing a trench coat. The original
answer attempted to address both; this FAQ has split them. They are:

* [What will happen to the language variants?](#without-k)
* [Does Mikan support Martin-Löf's identity type?](#jdentity)

#### What will happen to the language variants? {#without-k}

Some Agda developments make use of a variety of command-line options to
disable features which fall outside the type theory they are interested
in working in. The flags among these which have cross-module
effects[^infective] been removed from Mikan, and, in particular, the
flags `--without-K`, `--cubical-compatible` and `--cubical` are
effectively "always on", and specifying them results in a warning.

[^infective]:
    The command-line options for tuning the type theory must be used
    consistently across a set of modules. Suppose that we have a module
    `A` importing a module `B`. A flag can be:

    * **Infective**, e.g. `--prop`: if the flag is used in `B`, it must be used in `A`.
    * **Coinfective**, e.g. `--safe`: if the flag is used in `A`, it must have been used in `B`.

<details>
<summary>
The behaviour of these flags is surprisingly subtle and, strictly
speaking, when Mikan was forked, *no* combination of them actually
selected a language variant compatible with HoTT but without cubical
features.
</summary>

* The `--without-K` flag controls whether *anti-*homotopical features
  should be *dis*abled. In particular:

  + When determining whether matching on a specific instance of an
    indexed inductive family is allowed, reflexive equations between
    neutrals are not discarded. This is the actual source of the K rule
    in a language based on dependent pattern matching.

    Reflexive equations may still be discarded by pattern matching if
    the endpoints are constructors of an inductive data type, as this is
    justified by injectivity of constructors. For example:

    ```agda
does-not-use-K : _≡ᵢ_ {A = Nat} 0 0 → Type
does-not-use-K reflᵢ = ⊤
    ```

  + When checking the declaration of an indexed inductive family, it
    is checked that the index telescope fits in the declared sort of the
    type. Moreover, the types of *all* constructor arguments must fit in
    the type's declared sort, including the arguments which need not be
    stored because they appear in pattern position in an index.

  + When checking a group of mutually recursive functions for
    termination, structural recursion only considers the subterms of
    patterns which match arguments whose *declared* type is an inductive
    data type. Moreover, making guarded corecursive calls is only
    allowed when the function is *declared* as returning a coinductive
    record type.

    Both of these restrictions do not take into account computation in
    the function's type prompted by the matching of (other) patterns.
    This means in particular that a function whose arity depends on one
    of its arguments can not be structurally recursive in one of the
    newly-introduced arguments.

* The `--cubical-compatible` flag implies `--without-K` and additionally
  generates supporting definitions and clauses needed for the
  computation of the Kan operations. In particular:

  + When checking a data or record type, Mikan synthesizes helper
    functions necessary for the computation of the `transp`{.Agda} and
    `hcomp`{.Agda} primitives. When checking an indexed inductive type,
    this includes additional "constructors" for formal homogeneous
    compositions and for formal transport along indices.

  + When checking a function that pattern matches on an indexed
    inductive type, Mikan synthesizes clauses to cover the formal Kan
    operations for that data type. More details on this translation make
    up the answer to [Does Mikan support Martin-Löf's identity
    type?](#jdentity).

  The split between `--without-K` and `--cubical-compatible` is
  primarily an **optimisation**, allowing libraries that do not care
  about compatibility with cubical code to save the time that would be
  spent generating the support code. The specification of these flags
  say that they *should* accept the exact same programs, but this
  requires a lot of subtle code to replicate checks that would have been
  performed on the `--cubical-compatible` support code without actually
  generating it.

<!--
```agda
_ = transp (λ i → Nat) i0 0 -- "transp must be fully applied"… I just want an anchor
_ = hcomp
```
-->

* The `--cubical` implies `--cubical-compatible` and, ultimately,
  controls whether some* cubical primitives can be bound. Since this
  flag is infective, user code can not *generally* use cubical features
  unless it is enabled, since the primitives are bound in modules that
  declare it.

  However, some cubical primitives are accessible *regardless* of flags
  since they are bound in the `Agda.Primitive.Cubical` module, which is
  always loaded into the TC state on startup, bypassing the options
  compatibility check. Moreover, the `--cubical` flag is required to
  make the elaborator treat `Path`{.Agda} abstractions correctly. This
  has an observable effect on type inference even when no cubical
  features are used, see [Help! All my lambdas are
  yellow!](#inferred-lambdas).

</details>

Other than `--safe`, we will **not** support flags which disable parts
of the type theory across modules.

Since many flags change the behaviour of the elaborator *even for common
language features*, synchronising their behaviour poses a significant
challenge. We also expect that removing the flags will surface many bugs
that exist in combinations that had not been routinely stressed, and
supporting only one language mode is part of our strategy to avoid
introducing more of these in the future.

Flags which only disable features locally, like `--no-pattern-matching`,
are not slated for removal.

#### Does Mikan support Martin-Löf's identity type? {#jdentity}

The identity type can be defined as an ordinary indexed inductive family
and its eliminator will enjoy a strict computation rule, exactly as
expected.[^elim-reflection]

[^elim-reflection]:
    In the 1Lab, we can even use `make-elim`{.Agda} to automatically
    define the eliminator from the data type declaration.

    We export the inductive identity type as `_≡ᵢ_`{.Agda}, and the rest
    of this section will use that to avoid having to repeat a bunch of
    definitions.

```agda
data Id {ℓ} {A : Type ℓ} (x : A) : A → Type ℓ where
  id-refl : Id x x

unquoteDecl Id-J = make-elim Id-J (quote Id)

Id-J-β
  : ∀ {ℓ ℓ'} {A : Type ℓ} {x : A} {P : {y : A} → Id x y → Type ℓ'}
  → {pr : P id-refl} → Id-J {P = P} pr id-refl ≡ pr
Id-J-β = refl
```

Because Mikan is a cubical type theory, this `Id`{.Agda} type has closed
normal forms distinct from `id-refl`{.Agda}, coming from the computation
of `transp`{.Agda} and `hcomp`{.Agda}, or, at a higher level, from the
equivalence between `Path`{.Agda}s and identities. Because these Kan
operations behave like extra constructors, they must be handled by
functions defined by pattern matching, and indeed in many cases Mikan
performs the automatic synthesis of these extra clauses. For example:

```agda
_ : transportᵢ (Id≃path.from (ua not≃)) true ≡ false
_ = refl
```

The synthetic clauses **augment** those written by the user. This means
that, as long as the function is not applied to an argument defined
through a cubical primitive (like `Id≃path.to`{.Agda}), the
computational behaviour will be exactly that prescribed by the user's
clauses. In particular, the computation on declared constructors does
**not** involve cubical primitives, and the function is **still** stuck
when applied to a non-constructor, non-cubical normal form (like a
variable or a postulate). When porting a codebase that makes **no use of
cubical features**, the result of elaboration **does not depend on the
synthetic clauses**.

The exact behaviour of the synthetic clauses depends on the index at
which the function is matching and, in particular, in how the elaborator
simplifies equations between indices at each user clause. Not all
simplification steps can currently be translated to a synthetic clause,
but the steps involved in matching at fully-general indices (i.e., when
defining an eliminator) **are** supported. Mikan can raise a warning
`UnsupportedIndexedMatch`[^uim] whenever clause synthesis fails.
Functions **without** synthetic clauses will be stuck when applied to an
argument defined through the use of cubical primitives.

[^uim]:
    This warning is disabled by default, but enabled through
    `--exact-split`.

#### Help! All my lambdas are yellow! {#inferred-lambdas}

When elaborating a lambda expression at an unresolved expected type,
upstream Agda by default makes the unforced choice that the expected
type *must* be a function type with the same visibility as the lambda.
However, it is possible for elaboration to succeed *even if* the
unresolved type is solved with a distinct function type, by inserting
implicit binders:

```agda
mutual
  T = _
  -- introduce a named but unresolved type

  f : T
  f = λ x → x
  -- elaborate a lambda against it

  p : T ≡ (∀ {A : Type} → A → A)
  p = refl
  -- now solve T with an implicit function type.
  -- f can still be elaborated, by inserting a hidden binder.
  -- this program should check, but Agda rejects it
```

Because Mikan must support checking both function *and* path
abstractions, Mikan can not commit to solving `T` with a function type
when `f` is checked. This means the program above is correctly accepted.
However, this also means that being used as the expected type of a
lambda abstraction is *not* enough to determine an unresolved type, so
many lambda abstractions which previously had inferred types will result
in unsolved constraints when checked in Mikan. For example:

```agda
ex₁ : Nat
ex₁ = not-specified 5 where
  not-specified = λ x → x + x
```

This can be solved by adding a dummy type signature:

```agda
ex₂ : Nat
ex₂ = specified-enough 5 where
  specified-enough : ∀ _ → _
  specified-enough = λ x → x + x
```

#### Will Mikan support compilation?

Efficient compilation for the entirety of cubical type theory including
a foreign function interface is an open research problem, which we are
not currently pursuing. Were someone to propose a schema, we would not
be fundamentally opposed to implementing it.

However, we will **not** add support for a *partial* compilation mode,
like upstream's `--cubical=erased`, since this approach is fundamentally
anti-modular:

* If modules available for compilation are sectioned off through a
  language variant, then *every* reusable library must defensively be
  written with the expectation that client code will want to use it in
  compilation.

  If support for compilation additionally imposes changes on the type
  theory to make sure compilation of marked modules is possible,
  libraries must additionally adopt this modified type theory and adhere
  to the new restrictions.

* If compilation does not need modules to be marked ahead of time, and
  instead proceeds by chasing necessary definitions starting from an
  entry-point function, then whether a program is compilable depends on
  the implementation details of library functions in a way that is not
  reflected in the type theory; in particular, compilation becomes
  vulnerable to refactoring even of `abstract`{.Agda} lemmata, and,
  e.g., changing an `abstract`{.Agda} proof of a [[proposition]] to use
  a high-powered lemma based on `ua`{.Agda} becomes a breaking change.

<!--
```agda
_ = ua
```
-->

#### Did rewrite rules have to go?

While useful, rewrite rules are, fundamentally, a form of equality
reflection, and, since we're removing support for `--with-K`, there
would be no language variant left for them to be *safely* used with.
Moreover, upstream already claims that confluence checking is not
supported with `--cubical`, so even the check that the loaded rewrite
rules aren't nonsense would not be usable.

<details>
<summary>
We recommend that, whenever possible, rewrite rules are replaced with
native Mikan features. For example, it is possible to implement higher
inductive types, with computation only on the points, using native
higher inductive types, the module system, and `abstract`{.Agda}
definitions.
</summary>

```agda
private module S¹-impl where
  data S¹ : Type where
    base  : S¹
    loop' : base ≡ base

  abstract -- prevent computation on identities
    loop : base ≡ᵢ base
    loop = Id≃path.from loop'

  S¹-elim
    : ∀ {ℓ} (P : S¹ → Type ℓ) (pb : P base)
    → substᵢ P loop pb ≡ᵢ pb
    → ∀ x → P x
  -- point cases are easy:
  S¹-elim P pb ploop base = pb

  -- path cases need a bit of mangling since pattern matching expects
  -- cases-with-boundary but we have identities:
  S¹-elim P pb ploop (loop' i) = h₁ i where abstract
    h₁ : PathP (λ i → P (loop' i)) pb pb
    h₁ = substᵢ-filler {P = P} loop' {pb} ▷ Id≃path.to ploop

open S¹-impl hiding (module S¹) using (S¹ ; base ; loop ; S¹-elim) public
```

</details>

If you have an application of rewrite rules that makes sense within
Mikan's type theory, but which is not currently addressed by the
elaborator implementation, please reach out! We may be able to suggest a
workaround, or to implement an escape hatch if necessary.

#### Do all the modalities have to go?

In general, please understand that all the modal systems upstream
supports are ill-understood in combination with cubical type theory, and
that none of us are experts in modal type theory. There are also the
following specific points:

* Erasure (`@0`) is primarily useful in combination with compilation,
  so it has been removed.

  See [Will Mikan support compilation?] above.

* Irrelevance (`@irr`/`.A`) is inconsistent with univalence. While we
  could keep following upstream's game of whac-a-mole against
  irrelevance, `Prop` actually integrates smoothly into cubical type
  theory, and serves our need for definitional proof-irrelevance (only
  `¬¬`-stable propositions) perfectly well.

* Guarded (`@lock`) integrates poorly with postponement, is somewhat
  inelegant in that locks must both live in a special universe *and* be
  marked with a modality, and only serves to permit safely postulating
  Löb induction.

#### Will you change the cubical type theory?

There are a lot of variants of cubical type theory, differring in what
structure the interval is equipped with, what structure the cofibration
classifier is closed under, and what Kan operations are primitives.
Mikan implements a De Morgan interval, with cofibrations closed under
conjunction, disjunction, and dependent sum, and Kan operations
`transp`{.Agda} and `hcomp`{.Agda}.

It is not yet known whether this theory admits a model whose homotopy
theory is that of classical spaces. Moreover, removing some of the
structure on the interval and/or adopting a different set of primitive
Kan operations *could* yield a more usable type theory, e.g. by making
`coei→i`{.Agda} into a definitional equality, or by obviating the need
for cubical subtyping when defining derived Kan operations like
`hfill`{.Agda}.

<!--
```agda
_ = coei→i
_ = hfill
```
-->

However, recent work by Cavallo and Sattler [-@Cavallo:reversals] points
towards the *possibility* an interpretation of Mikan's type theory in
the homotopy theory of spaces, rather than its impossibility. Moreover,
it is possible for users to define uniform friendly versions of
`hcomp`{.Agda} and `hfill`{.Agda} which even display properly in goals
through use of the module system, as demonstrated on the 1Lab.

Since changing the cubical type theory would present a significant
implementation challenge, along with necessitating an unknown amount of
work to adapt user code, we do not presently see either of these
arguments as sufficient motivation for pursuing changes of this flavour.
