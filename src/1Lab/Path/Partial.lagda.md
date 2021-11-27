```agda
open import 1Lab.HLevel
open import 1Lab.Path
open import 1Lab.Type

module 1Lab.Path.Partial where
```

# Partial elements

Recall that a term in a context with $n$ interval variables corresponds
to a way of mapping $n$-cubes into the type. Iteratively: No variables
is just an inhabitant, one variable is a [Path], two variables is a path
between paths, etc, and that we can [raise the dimension of a path]
using structural and logical operations on the interval.

[path]: 1Lab.Path.html
[raise the dimension of a path]: 1Lab.Path.html#raising-dimension

However, in addition to _completely defined_ $n$-cubes, for operations
such as [composition] and [glueing], we need _partially defined_
$n$-cubes. These are represented in Agda using terms of `Partial`{.Agda}
type. These represent sub-shapes of a cube, by constraining where values
are specified in terms of a formula.

[composition]: agda://1Lab.Path#hfill
[glueing]: 1Lab.Univalence.html#Glue

For instance, if we have a variable `i : I` of interval type, we can
represent _disjoint endpoints_ of a [Path] by a partial element with
formula $\neg i \lor i$:

```agda
private
  notAPath : (i : I) → Partial (~ i ∨ i) Bool
  notAPath i (i = i0) = true
  notAPath i (i = i1) = false
```

This represents the following shape: Two disconnected points, with
completely unrelated values at each endpoint of the interval.

~~~{.quiver .short-2}
\[\begin{tikzcd}
  {\mathrm{true}} && {\mathrm{false}}
\end{tikzcd}\]
~~~

A `Partial`{.Agda} element can be understood as a function where the
domain is the predicate `IsOne`{.Agda}, which has an inhabitant
`1=1`{.Agda}, stating that one is one:

```agda
  _ : notAPath i0 1=1 ≡ true
  _ = refl
```

In a context with two interval variables, we can form more interesting
shapes. For instance, in the definition of [double composition], the
following _tube_ is employed:

[double composition]: 1Lab.Path.html#transitivity

~~~{.quiver}
\[\begin{tikzcd}
  w && z \\
  \\
  x && y
  \arrow["p"', from=1-1, to=3-1]
  \arrow["r", from=1-3, to=3-3]
\end{tikzcd}\]
~~~

This is a partial element of two variables, $i, j : I$, defined when
$\neg i \lor i$: only the two faces going top-down.

# Extensibility

A partial element in a context with $n$-variables gives us a way of
mapping some subobject of the $n$-cube into a type. A natural question
to ask, then, is: Given a partial element $e$ of $A$, can we extend that
to a honest-to-god _element_ of $A$, which agrees with $e$ where it is
defined?

Specifically, when this is the case, we say that $x : A$ _extends_ $e :
\mathrm{Partial}\ \phi\ A$. We can depict the situation by drawing a
commutative triangle like the one below, with $\phi$ representing the
subobject of the $n$-cube defined by $\phi$.

~~~{.quiver}
\[\begin{tikzcd}
  \phi \\
  \\
  {\square^n} && A
  \arrow[hook, from=1-1, to=3-1]
  \arrow["e", from=1-1, to=3-3]
  \arrow["x"', dashed, from=3-1, to=3-3]
\end{tikzcd}\]
~~~

In Agda, extensions are represented by the type `_[_↦_]`{.Agda}. For
instance, we can define a partial element of `Bool` - `true`{.Agda} on
the left endpoint of the interval - and prove that the path
`refl`{.Agda} _extends_ this to a line in `Bool`{.Agda}.

```agda
private
  left-true : (i : I) → Partial (~ i) Bool
  left-true i (i = i0) = true

  refl-extends : (i : I) → Bool [ _ ↦ left-true i ]
  refl-extends i = inS true
```

The constructor `inS` expresses that _any_ totally-defined cube $u$ can
be seen as a partial cube, one that agrees with $u$ for any choice of
formula $\phi$:

```agda
  _ : ∀ {ℓ} {A : Type ℓ} {φ : I} (u : A) → A [ φ ↦ (λ _ → u) ]
  _ = inS
```

## Contractibility

The idea of extensibility can be used, for instance, to define a
_geometric_ notion of [contractibility]: A type $A$ is contractible if,
and only if, any partial element of $A$ is extensible.

[contractibility]: agda://1Lab.HLevel#isContr

```agda
isContr' : {ℓ : _} → Type ℓ → _
isContr' A = {φ : I} (u : Partial φ A) → A [ φ ↦ u ]
```

In the "only if" direction, we can fill the cube defined by $\phi$ (for
any $\phi$) using the paths that contract $A$; The base of this cube can
be taken to be the centre of contraction.

```agda
isContr→isContr' : {ℓ : _} {A : Type ℓ} → isContr A → isContr' A
isContr→isContr' isc {φ} u0 =
  inS (hcomp (λ j → λ { (φ = i1) → isc .isContr.paths (u0 1=1) j })
             (isc .isContr.centre))
```

In the "if" direction, given a proof that any partial element is
extensible, we can extend the _empty_ element to get a point of $A$:

```agda
isContr'→isContr : {ℓ : _} {A : Type ℓ} → isContr' A → isContr A
isContr.centre (isContr'→isContr extend) = outS (extend {φ = i0} λ { () })
```

And the family of paths can be defined by extending the element which is
$x$ when $i = i1$, and undefined otherwise.

```agda
isContr.paths (isContr'→isContr extend) x i = outS (extend λ { (i = i1) → x })
```

This interface - having any partial element extensible, as a notion of
contractibility - is the interface that Agda expects for its type of
equivalences: See [`isEqv'`](agda://1Lab.Equiv#isEqv').

## Composition

The notion of extensibility also lets us give a more precise definition
to the notion of "filling a cube": The primitive `hcomp`{.Agda}
expresses that _if a family of paths is extensible at `i0`{.Agda}, then
it's extensible at `i1`{.Agda}_:

```agda
private
  hcomp-verbose : {ℓ : _} {A : Type ℓ} {φ : I}
                → (u : (i : I) → Partial φ A) -- A family of partial paths
                → A [ φ ↦ u i0 ]              -- extensible at i0
                → A [ φ ↦ u i1 ]              -- is extensible at i1
  hcomp-verbose u u0 = inS (hcomp u (outS u0))
```
