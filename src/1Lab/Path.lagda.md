```agda
open import 1Lab.Type

module 1Lab.Path where
```

# The Interval

In HoTT, the inductively-defined identity type gets a new meaning
explanation: continuous paths, in a topological sense. The "key idea" of
cubical type theory --- and thus, Cubical Agda --- is that we can take
this as a new _definition_ of the identity type, where we interpret a
`Path`{.Agda} in a type by a function where the domain is the _interval
type_.

<details>
<summary>
**Aside**: A brief comment on the meanings of "equal", "identical" and
"identified", and how we refer to inhabitants of path types.
</summary>

Before getting started, it's worth taking a second to point out the
terminology that will be used in this module (and most of the other
pages). In intensional type theory, there is both an external notion of
"sameness" (definitional equality), and an internal notion of
"sameness", which goes by many names: identity type, equality type,
propositional equality, path type, etc.[^starthere]

[^starthere]: The distinction between these two is elaborated on in the
[Intro to HoTT](1Lab.intro.html) page.

In this module, we refer to the type `A ≡ B` as either (the type of)
_paths from A to B_ or (the type of) _identifications between A and B_,
but **never** as "equalities between A and B". In particular, the HoTT
book comments that we may say "$a$ and $b$ are equal" when the type $a
\equiv b$ is inhabited, but in this development we refer this
terminology for the case where $a$ and $b$ inhabit a [set].

[set]: 1Lab.HLevel.html

Instead, for general types, we use "$a$ and $b$ are **identical**" or
"$a$ and $b$ are **identified**" (or even the wordier, and rather more
literal, "there is a path between $a$ and $b$"). Depending on the type,
we might use more specific words: Paths are said to be **homotopic**
when they're connected by a path-of-paths, and types are said to be
**equivalent** when they are connected by a path.

</details>

<!--
```agda
open import Agda.Builtin.Cubical.Path public
open import Agda.Builtin.Cubical.Sub public
  renaming ( inc to inS
           ; primSubOut to outS
           )
open import Agda.Primitive.Cubical public
  renaming ( primIMin       to _∧_
           ; primIMax       to _∨_
           ; primINeg       to ~_
           ; isOneEmpty     to empty
           ; primComp       to comp
           ; primHComp      to hcomp
           ; primTransp     to transp
           ; itIsOne        to 1=1 )
```
-->

```agda
Path : ∀ {ℓ} (A : Type ℓ) → A → A → Type ℓ
Path A = PathP (λ i → A)
```

The type `I`{.Agda} is meant to represent the (real, closed) unit
interval $[0,1]$, the same unit interval used in the topological
definition of path. Because the real unit interval has a least and
greatest element --- 0 and 1 --- the interval _type_ also has two global
inhabitants, `i0`{.Agda} and `i1`{.Agda}. This is where the analogy with
the reals breaks down: There's no such thing as `i0.5` (much less
`i1/π`). In reality, the interval type internalises an abstract interval
_object_.

Regardless, since all functions definable in type theory are
automatically continuous, we can take a path to be any value in the
function type `I → A`. When working with paths, though, it's useful to
mention the endpoints of a path in its type --- that is, the values the
function takes when applied to `i0` and to `i1`. We can "upgrade" any
function `f : I → A` to a `Path`{.Agda}, using a definition that looks
suspiciously like the identity function:

```agda
private
  to-path : ∀ {ℓ} {A : Type ℓ} → (f : I → A) → Path A (f i0) (f i1)
  to-path f i = f i

refl : ∀ {ℓ} {A : Type ℓ} {x : A} → x ≡ x
refl {x = x} = to-path (λ i → x)
```

The type `Path A x y` is also written `x ≡ y`, when `A` is not important
- i.e. when it can be inferred from `x` and `y`. Under this
interpretation, proof that identification is reflexive (i.e. that $x =
x$) is given by a `Path`{.Agda} which yields the same element everywhere
on `I`: The function that is constantly $x$.

If we have a `Path`{.Agda}, we can apply it to a value of the interval
type to get an element of the underlying type. When a path is applied to
one of the endpoints, the result is the same as declared in its type ---
even when we're applying a path we don't know the definition of.[^cofibration]

[^cofibration]: For the semantically inclined, these correspond to face inclusions
(including the inclusions of endpoints into a line) being monomorphisms,
and thus _cofibrations_ in the model structure on cubical sets.

```agda
module _ {ℓ} {A : Type ℓ} {x y : A} {p : x ≡ y} where
  private
    left-endpoint : p i0 ≡ x
    left-endpoint i = x

    right-endpoint : p i1 ≡ y
    right-endpoint i = y
```

In addition to the two endpoints `i0`{.Agda} and `i1`{.Agda}, the
interval has the structure of a De Morgan algebra. All the following
equations are respected (definitionally), but they can not be expressed
internally as a `Path`{.Agda} because `I`{.Agda} is not in
`Type`{.Agda}.[^inotkan]

[^inotkan]: Since `I`{.Agda} is not Kan (that is --- it does not have a
[_composition_](#composition) structure), it is not an inhabitant of the
“fibrant universe” `Type`{.Agda}. Instead it lives in `SSet`, or, in
Agda 2.6.3, its own universe -- `IUniv`.

- $x \land \id{i0} = \id{i0}$, $x \land \id{i1} = x$
- $x \lor \id{i0} = x$, $x \lor \id{i1} = \id{i1}$
- $\neg(x \land y) = \neg x \lor \neg y$
- $\neg\id{i0} = \id{i1}$, $\neg\id{i1} = \id{i0}$, $\neg\neg x = x$
- $\land$ and $\lor$ are both associative, commutative and idempotent,
and distribute over eachother.

Note that, in the formalisation, $\neg x$ is written `~ x`. As a more
familiar description, a De Morgan algebra is a Boolean algebra that does
not (necessarily) satisfy the law of excluded middle. This is necessary
to maintain type safety.

## Raising Dimension

To wit: In cubical type theory, a term in a context with $n$ interval
variables expresses a way of mapping an $n$-cube into that type. One
very important class of these maps are the $1$-cubes --- lines or
_`paths`{.Agda ident=Path}_ --- which represent identifications between
terms of that type.

Iterating this construction, a term in a context with 2 interval
variables represents a square in the type, which can be read as saying
that some _paths_ (specialising one of the variables to $i0$ or $i1$) in
that space are identical: A path between paths, which we call a
_homotopy_.

The structural operations on contexts, and the $\land$ and $\lor$
operations on the interval, give a way of extending from $n$-dimensional
cubes to $n+k$-dimensional cubes. For instance, if we have a path like
the one below, we can extend it to any of a bunch of different squares:

~~~{.quiver .short-2}
\[\begin{tikzcd}
  a && b
  \arrow[from=1-1, to=1-3]
\end{tikzcd}\]
~~~

```agda
module _ {ℓ} {A : Type ℓ} {a b : A} {p : Path A a b} where
```

The first thing we can do is introduce another interval variable and
ignore it, varying the path over the non-ignored variable. These give us
squares where either the top/bottom or left/right faces are the path
`p`, and the other two are refl.

```agda
  private
    drop-j : PathP (λ i → p i ≡ p i) refl refl
    drop-j i j = p i

    drop-i : PathP (λ i → a ≡ b) p p
    drop-i i j = p j
```

These squares can be drawn as below. Take a moment to appreciate how the
_types_ of `drop-j`{.Agda} and `drop-i`{.Agda} specify the _boundary_ of
the diagram --- A `PathP (λ i → p i ≡ p i) refl refl` corresponds to a
square whose top/bottom faces are both `p`, and whose left/right faces
are both `refl`{.Agda} (by convention). Similarly, `PathP (λ i → a ≡ b)
p p` has `refl`{.Agda} as top/bottom faces (recall that `refl`{.Agda} is
the constant function regarded as a path), and `p` as both left/right
faces.

<div class="mathpar">

~~~{.quiver}
\[\begin{tikzcd}
  a && b \\
  \\
  a && b
  \arrow["p", from=1-1, to=1-3]
  \arrow["p"', from=3-1, to=3-3]
  \arrow["{\id{refl}}"{description}, from=1-1, to=3-1]
  \arrow["{\id{refl}}"{description}, from=1-3, to=3-3]
\end{tikzcd}\]
~~~

~~~{.quiver}
\[\begin{tikzcd}
  a && a \\
  \\
  b && b
  \arrow["{\id{refl}}", from=1-1, to=1-3]
  \arrow["{\id{refl}}"', from=3-1, to=3-3]
  \arrow["p"{description}, from=1-1, to=3-1]
  \arrow["p"{description}, from=1-3, to=3-3]
\end{tikzcd}\]
~~~

</div>

The other thing we can do is use one of the binary operators on the
interval to get squares called _connections_, where two adjacent faces
are `p` and the other two are refl:

```agda
    ∧-conn : PathP (λ i → a ≡ p i) refl p
    ∧-conn i j = p (i ∧ j)

    ∨-conn : PathP (λ i → p i ≡ b) p refl
    ∨-conn i j = p (i ∨ j)
```

These correspond to the following two squares:

<div class="mathpar">

~~~{.quiver}
\[\begin{tikzcd}
  a && a \\
  \\
  a && b
  \arrow["{\id{refl}}", from=1-1, to=1-3]
  \arrow["p"', from=3-1, to=3-3]
  \arrow["{\id{refl}}"{description}, from=1-1, to=3-1]
  \arrow["{p}"{description}, from=1-3, to=3-3]
\end{tikzcd}\]
~~~

~~~{.quiver}
\[\begin{tikzcd}
  a && b \\
  \\
  b && b
  \arrow["{p}", from=1-1, to=1-3]
  \arrow["{\id{refl}}"', from=3-1, to=3-3]
  \arrow["p"{description}, from=1-1, to=3-1]
  \arrow["{\id{refl}}"{description}, from=1-3, to=3-3]
\end{tikzcd}\]
~~~

</div>

Since iterated paths are used _a lot_ in homotopy type theory, we
introduce a shorthand for 2D non-dependent paths. A `Square`{.Agda} in a
type is exactly what it says on the tin: a square.

```
Square : ∀ {ℓ} {A : Type ℓ} {a00 a01 a10 a11 : A}
       → (p : a00 ≡ a01)
       → (q : a00 ≡ a10)
       → (s : a01 ≡ a11)
       → (r : a10 ≡ a11)
       → Type ℓ
Square p q s r = PathP (λ i → p i ≡ r i) q s
```

The arguments to `Square`{.Agda} are as in the following diagram, listed
in the order “PQSR”. This order is a bit unusual (it's one off from
being alphabetical, for instance) but it does have a significant
benefit: If you imagine that the letters are laid out in a circle,
_identical paths are adjacent_. Reading the square in the left-right
direction, it says that $p$ and $r$ are identical --- these are adjacent
if you "fold up" the sequence `p q s r`. Similarly, reading top-down, it
says that $q$ and $s$ are identical - these are directly adjacent.

~~~{.quiver}
\[\begin{tikzcd}
  \bullet && \bullet \\
  \\
  \bullet && \bullet
  \arrow["p"', from=1-1, to=3-1]
  \arrow["q", from=1-1, to=1-3]
  \arrow["r", from=1-3, to=3-3]
  \arrow["s"', from=3-1, to=3-3]
\end{tikzcd}\]
~~~

## Symmetry

The involution `~_`{.Agda} on the interval type gives a way of inverting
paths --- a proof that identification is symmetric.

```agda
sym : ∀ {ℓ₁} {A : Type ℓ₁} {x y : A}
    → x ≡ y → y ≡ x
sym p i = p (~ i)
```

<!--
```
symP : ∀ {ℓ₁} {A : I → Type ℓ₁} {x : A i0} {y : A i1}
     → PathP A x y → PathP (λ i → A (~ i)) y x
symP p i = p (~ i)
```
-->

As a minor improvement over "Book HoTT", this operation is
_definitionally_ involutive:

```agda
module _ {ℓ} {A : Type ℓ} {x y : A} {p : x ≡ y} where
  private
    sym-invol : sym (sym p) ≡ p
    sym-invol i = p
```

# Paths

While the basic structure of the path type is inherited from its nature
as functions out of an internal De Morgan algebra, the structure of
_identifications_ presented by paths is more complicated. For starters,
let's see how paths correspond to identifications in that they witness
the logical principle of "indiscernibility of identicals".

## Transport

A basic principle of identity is that _identicals are indiscernible_: if
$x = y$ and $P(x)$ holds, then $P(y)$ also holds, for any choice of
predicate $P$. In type theory, this is generalised, as $P$ can be not
only a predicate, but any type family.

The way this is incarnated is by an operation called `transport`{.Agda},
which says that every path between `A` and `B` gives rise to a
_function_ `A → B`.

```agda
transport : ∀ {ℓ} {A B : Type ℓ} → A ≡ B → A → B
transport p = transp (λ i → p i) i0
```

The transport operation is the earliest case of when thinking of `p : A
≡ B` as merely saying "A and B are equal" goes seriously wrong. A path
gives a _specific_ identification of `A` and `B`, which can be highly
non-trivial.

As a concrete example, it can be shown that the type `Bool ≡ Bool` has
exactly two inhabitants ([see here]), which is something like saying
"the set of booleans is equal to itself in two ways". That phrase is
nonsensical, which is why "there are two paths Bool → Bool" is
preferred: it's not nonsense.

[see here]: Data.Bool.html#Bool-aut≡2

In Cubical Agda, `transport`{.Agda} is a derived notion, with the actual
primitive being `transp`{.Agda}. Unlike `transport`{.Agda}, which has
two arguments (the path, and the point to transport), `transp` has _three_:

- The first argument to `transp`{.Agda} is a _line_ of types, i.e. a
function `A : I → Type`, just as for `transport`{.Agda}.

- The second argument to `transp`{.Agda} has type `I`{.Agda}, but it's
not playing the role of an endpoint of the interval. It's playing the
role of a _formula_, which specifies _where the transport is constant_:
In `transp P i1`, `P` is required to be constant, and the transport is
the identity function:

  ```
_ : ∀ {ℓ} {A : Type ℓ} → transp (λ i → A) i1 ≡ id
_ = refl
  ```

- The third argument is an inhabitant of `A i0`, as for `transport`{.Agda}.

This second argument, which lets us control where `transp`{.Agda} is
constant, brings a lot of power to the table! For example, the proof
that transporting along `refl`{.Agda} is `id`{.Agda} is as follows:

```agda
transport-refl : ∀ {ℓ} {A : Type ℓ} (x : A)
               → transport (λ i → A) x ≡ x
transport-refl {A = A} x i = transp (λ _ → A) i x
```

Since `λ i → A` is a constant function, the definition of
`transport-refl`{.Agda} is well-typed, and it has the stated endpoints
because `transport`{.Agda} is defined to be `transp P i0`, and `transp P
i1` is the identity function.

In fact, this generalises to something called the _filler_ of
`transport`{.Agda}: `transport p x` and `x` _are_ identical, but they're
identical _over_ the given path:

```agda
transport-filler : ∀ {ℓ} {A B : Type ℓ}
                 → (p : A ≡ B) (x : A)
                 → PathP (λ i → p i) x (transport p x)
transport-filler p x i = transp (λ j → p (i ∧ j)) (~ i) x
```

<details>
<summary>
We also have some special cases of `transport-filler`{.Agda} which are
very convenient when working with iterated transports.
</summary>

```agda
transport-filler-ext : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B)
                     → PathP (λ i → A → p i) (λ x → x) (transport p)
transport-filler-ext p i x = transport-filler p x i

transport⁻-filler-ext : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B)
                     → PathP (λ i → p i → A) (λ x → x) (transport (sym p))
transport⁻-filler-ext p i x = transp (λ j → p (i ∧ ~ j)) (~ i) x

transport⁻transport : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) (a : A)
                    → transport (sym p) (transport p a) ≡ a
transport⁻transport p a i =
  transport⁻-filler-ext p (~ i) (transport-filler-ext p (~ i) a)
```
</details>

The path is constant when `i = i0` because `(λ j → p (i0 ∧ j))` is
`(λ j → p i0)` (by the reduction rules for `_∧_`{.Agda}). It has the
stated endpoints, again, because `transp P i1` is the identity function.

By altering a path `p` using a predicate `P`, we get the promised
principle of _indiscernibility of identicals_:

```agda
subst : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} (P : A → Type ℓ₂) {x y : A}
      → x ≡ y → P x → P y
subst P p x = transp (λ i → P (p i)) i0 x
```

### Computation

In “Book HoTT”, `transport`{.Agda} is defined using path induction, and
it computes definitionally on `refl`{.Agda}. We have already seen that
this is not definitional in cubical type theory, which might lead you to
ask: When does `transport`{.Agda} compute? The answer is: By cases on
the path. The structure of the path `P` is what guides reduction of
`transport`{.Agda}. Here are some reductions:

For the natural numbers, and other inductive types without parameters,
transport is always the identity function. This is justified because
there's nothing to vary in `Nat`{.Agda}, so we can just ignore the
transport:

```agda
_ : {x : Nat} → transport (λ i → Nat) x ≡ x
_ = refl
```

For other type formers, the definition is a bit more involved. Let's
assume that we have two lines, `A` and `B`, to see how transport reduces
in types built out of `A` and `B`:

```agda
module _ {A : I → Type} {B : I → Type} where private
```

For non-dependent products, the reduction rule says that
"`transport`{.Agda} is homomorphic over forming products":

```agda
  _ : {x : A i0} {y : B i0}
    → transport (λ i → A i × B i) (x , y)
    ≡ (transport (λ i → A i) x , transport (λ i → B i) y)
  _ = refl
```

For non-dependent functions, we have a similar situation, except one the
transports is _backwards_. This is because, given an `f : A i0 → B i0`,
we have to turn an `A i1` into an `A i0` to apply f!

```agda
  _ : {f : A i0 → B i0}
    → transport (λ i → A i → B i) f
    ≡ λ x → transport (λ i → B i) (f (transport (λ i → A (~ i)) x))
  _ = refl

module _ {A : I → Type} {B : (i : I) → A i → Type} where private
```

In the dependent cases, we have slightly more work to do. Suppose that
we have a line `A : I → Type ℓ` and a _dependent_ line `B : (i : I) → A
i → Type ℓ`. Let's characterise `transport`{.Agda} in the lines `(λ i →
(x : A i) → B i x)`. A first attempt would be to repeat the
non-dependent construction: Given an `f : (x : A i0) → B i0 x` and an
argument `x : A i1`, we first get `x' : A i0` by transporting along `λ i
→ A (~ i)`, compute `f x' : B i0 x`, then transport along `(λ i → B i
x')` to g- Wait.

```agda
  _ : {f : (x : A i0) → B i0 x}
    → transport (λ i → (x : A i) → B i x) f
    ≡ λ (x : A i1) →
        let
          x' : A i0
          x' = transport (λ i → A (~ i)) x
```

We can't "transport along `(λ i → B i x')`", that's not even a
well-formed type! Indeed, `B i : A i → Type`, but `x' : A i1`. What we
need is some way of connecting our original `x` and `x'`, so that we may
get a `B i1 x'`. This is where `transport-filler`{.Agda} comes in:

```agda
          x≡x' : PathP (λ i → A (~ i)) x x'
          x≡x' = transport-filler (λ i → A (~ i)) x
```

By using `λ i → B i (x≡x' (~ i))` as our path, we a) get something
type-correct, and b) get something with the right endpoints. `(λ i → B i
(x≡x' (~ i)))` connects `B i0 x` and `B i1 x'`, which is what we wanted.

```agda
          fx' : B i0 x'
          fx' = f x'
        in transport (λ i → B i (x≡x' (~ i))) fx'
  _ = refl
```

The case for dependent products (i.e. general `Σ`{.Agda} types) is
analogous, but without any inverse transports.

## Path Induction

The path induction principle, also known as "axiom J", essentially
breaks down as the following two statements:

- Identicals are indiscernible (`transport`{.Agda})

- Singletons are contractible. The type `Singleton A x` is the "subtype
of A of the elements identical to x":

```agda
Singleton : ∀ {ℓ} {A : Type ℓ} → A → Type _
Singleton x = Σ[ y ∈ _ ] (x ≡ y)
```

There is a canonical inhabitant of `Singleton x`, namely `(x, refl)`. To
say that `singletons`{.Agda ident=singleton} are contractible is to say
that every other inhabitant has a path to `(x, refl)`:

```agda
Singleton-is-contr : ∀ {ℓ} {A : Type ℓ} {x : A} (y : Singleton x)
                   → Path (Singleton x) (x , refl) y
Singleton-is-contr {x = x} (y , path) i = path i , square i where
  square : Square refl refl path path
  square i j = path (i ∧ j)
```

Thus, the definition of `J`{.Agda}: `transport`{.Agda} +
`Singleton-is-contr`{.Agda}.

```agda
J : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {x : A}
    (P : (y : A) → x ≡ y → Type ℓ₂)
  → P x refl
  → {y : A} (p : x ≡ y)
  → P y p
J {x = x} P prefl {y} p = transport (λ i → P (path i .fst) (path i .snd)) prefl where
  path : (x , refl) ≡ (y , p)
  path = Singleton-is-contr (y , p)
```

This eliminator _doesn't_ definitionally compute to `prefl` when `p` is
`refl`, again since `transport (λ i → A)` isn't definitionally the
identity.  However, since it _is_ a transport, we can use the
`transport-filler`{.Agda} to get a path expressing the computation rule.

```agda
J-refl : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {x : A}
           (P : (y : A) → x ≡ y → Type ℓ₂)
       → (pxr : P x refl)
       → J P pxr refl ≡ pxr
J-refl {x = x} P prefl i = transport-filler (λ i → P _ (λ j → x)) prefl (~ i)
```

<!--
```agda
inspect : ∀ {a} {A : Type a} (x : A) → Singleton x
inspect x = x , refl
```
-->

## Functorial Action

In HoTT, every function behaves like a funct**or**, in that it has an
action on objects (the actual computational content of the function) and
an action on _morphisms_ --- how that function acts on paths. Reading
paths as identity, this is a proof that functions take identical inputs
to identical outputs.

```agda
ap : ∀ {a b} {A : Type a} {B : A → Type b} (f : (x : A) → B x) {x y : A}
   → (p : x ≡ y) → PathP (λ i → B (p i)) (f x) (f y)
ap f p i = f (p i)
```

The following function expresses the same thing as `ap`{.Agda}, but for
binary functions. The type is huge! That's because it applies to the
most general type of 2-argument dependent function possible: `(x : A) (y
: B x) → C x y`. Even then, the proof is beautifully short:

```agda
ap₂ : ∀ {a b c} {A : Type a} {B : A → Type b} {C : (x : A) → B x → Type c}
      (f : (x : A) (y : B x) → C x y)
      {x y : A} {α : B x} {β : B y}
    → (p : x ≡ y)
    → (q : PathP (λ i → B (p i)) α β)
    → PathP (λ i → C (p i) (q i))
            (f x α)
            (f y β)
ap₂ f p q i = f (p i) (q i)
```

This operation satisfies many identities definitionally that are only
propositional when `ap`{.Agda} is defined in terms of `J`{.Agda}. For
instance:

```agda
module _ {A B C : Type} {f : A → B} {g : B → C} where
  ap-comp : {x y : A} {p : x ≡ y}
          → ap (λ x → g (f x)) p ≡ ap g (ap f p)
  ap-comp = refl

  ap-id : {x y : A} {p : x ≡ y}
        → ap (λ x → x) p ≡ p
  ap-id = refl

  ap-sym : {x y : A} {p : x ≡ y}
          → sym (ap f p) ≡ ap f (sym p)
  ap-sym = refl

  ap-refl : {x : A} → ap f (λ i → x) ≡ (λ i → f x)
  ap-refl = refl
```

The last lemma, that `ap` respects composition of _paths_, needs path
induction, and the rest of the groupoid structure on type formers, so
it's in [a different module].

[a different module]: 1Lab.Path.Groupoid.html#ap-comp-path

# Composition

In "Book HoTT", the primitive operation from which the
higher-dimensional structure of types is derived is the `J`{.Agda}
eliminator, with `J-refl`{.Agda} as a _definitional_ computation rule.
This has the benefit of being very elegant: This one elimination rule
generates an infinite amount of coherent data. However, it's very hard
to make compute in the presence of higher inductive types and
univalence, so much so that, in the book, univalence and HITs only
compute up to paths.

In Cubical Agda, types are interpreted as objects called _cubical Kan
complexes_[^blogpost], which are a _geometric_ description description of
spaces as "sets we can probe by cubes". In Agda, this "probing" is
reflected by mapping the interval into a type: A "probe" of $A$ by an
$n$-cube is a term of type $A$ in a context with $n$ variables of type
`I`{.Agda} --- points, lines, squares, cubes, etc. This structure lets
us “explore” the higher dimensional structure of a type, but it does not
specify how this structure behaves.

[^blogpost]: I (Amélia) wrote [a blog post] explaining the semantics of them in
a lot of depth.

[a blog post]: https://amelia.how/posts/cubical-sets.html

That's where the "Kan" part of "cubical Kan complex" comes in:
Semantically, _every open box extends to a cube_. The concept of "open
box" might make even less sense than the concept of "cube in a type"
initially, so it helps to picture them! Suppose we have three paths $p :
w ≡ x$, $q : x ≡ y$, and $r : y ≡ z$. We can pictorially arrange them
into an open box like in the diagram below, by joining the paths by
their common endpoints:

<figure>
~~~{.quiver}
\[\begin{tikzcd}
  x && y \\
  \\
  w && z
  \arrow["{\id{sym}\ p}"', from=1-1, to=3-1]
  \arrow["q", from=1-1, to=1-3]
  \arrow["r", from=1-3, to=3-3]
\end{tikzcd}\]
~~~
</figure>

In the diagram above, we have a square assembled of three lines $w ≡ x$,
$x ≡ y$, and $y ≡ z$. Note that in the left face of the diagram, the
path was inverted; This is because while we have a path $w ≡ x$, we need
a path $x ≡ w$, and all parallel faces of a cube must "point" in the
same direction. The way the diagram is drawn strongly implies that there
is a face missing --- the line $w ≡ z$. The interpretation of types as
_Kan_ cubical sets guarantees that the open box above extends to a
complete square, and thus the line $w ≡ z$ exists.

## Partial Elements

The definition of Kan cubical sets as those having fillers for all open
boxes is all well and good, but to use this from within type theory we
need a way of reflecting the idea of "open box" as syntax. This is done
is by using the `Partial`{.Agda} type former.

The `Partial`{.Agda} type former takes two arguments: A _formula_
$\varphi$, and a _type_ $A$. The idea is that a term of type
$\id{Partial}\ \varphi\ A$ in a context with $n$ `I`{.Agda}-typed
variables is a $n$-cube that is only defined when $\varphi$ "is true". In
Agda, formulas are represented using the De Morgan structure of the
interval, and they are "true" when they are equal to 1. The predicate
`IsOne`{.Agda} represents truth of a formula, and there is a canonical
inhabitant `1=1`{.Agda} which says `i1`{.Agda} is `i1`{.Agda}.

For instance, if we have a variable `i : I` of interval type, we can
represent _disjoint endpoints_ of a `Path`{.Agda} by a partial element with
formula $\neg i \lor i$. Note that this is not the same thing as
`i1`{.Agda}! Since elements of `I` are meant to represent real numbers
$r \in [0,1]$, it suffices to find one for which $\max(x, 1 - x)$ is
not $1$ --- like 0.5.

```agda
private
  not-a-path : (i : I) → Partial (~ i ∨ i) Bool
  not-a-path i (i = i0) = true
  not-a-path i (i = i1) = false
```

This represents the following shape: Two disconnected points, with
completely unrelated values at each endpoint of the interval.

~~~{.quiver .short-2}
\[\begin{tikzcd}
  {\id{true}} && {\id{false}}
\end{tikzcd}\]
~~~

More concretely, an element of `Partial`{.Agda} can be understood as a
function where the domain is the predicate `IsOne`{.Agda}, which has an
inhabitant `1=1`{.Agda}, stating that one is one. Indeed, we can _apply_
a `Partial`{.Agda} to an argument of type `IsOne`{.Agda} to get a value
of the underlying type.

```agda
  _ : not-a-path i0 1=1 ≡ true
  _ = refl
```

Note that if we _did_ have `(~i ∨ i) = i1` (i.e. our De Morgan algebra
was a Boolean algebra), the partial element above would give us a
contradiction, since any `I → Partial i1 T` extends to a path:

```
  _ : (f : I → Partial i1 Bool) → Path Bool (f i0 1=1) (f i1 1=1)
  _ = λ f i → f i 1=1
```

## Extensibility

A partial element in a context with $n$-variables gives us a way of
mapping some subobject of the $n$-cube into a type. A natural question
to ask, then, is: Given a partial element $e$ of $A$, can we extend that
to a honest-to-god _element_ of $A$, which agrees with $e$ where it is
defined?

Specifically, when this is the case, we say that $x : A$ _extends_ $e :
\id{Partial}\ \varphi\ A$. We could represent this very generically as a
_lifting problem_, i.e. trying to find a map $\square^n$ which agrees
with $e$ when restricted to $\varphi$, but I believe a specific example
will be more helpful.

Suppose we have a partial element of `Bool`{.Agda} which is
`true`{.Agda} on the left endpoint of the interval, and undefined
elsewhere. This is a partial element with one interval variable, so it
would be extended by a _path_ --- a 1-dimensional cube. The reflexivity
path is a line in `Bool`, which is `true`{.Agda} on the left endpoint of
the interval (in fact, it is `true`{.Agda} everywhere), so we say that
`refl`{.Agda} _extends_ the partial element.

~~~{.quiver .short-1}
\[\begin{tikzcd}
  \textcolor{rgb,255:red,214;green,92;blue,92}{\id{true}} && {\id{true}}
  \arrow["{\id{refl}}", from=1-1, to=1-3]
\end{tikzcd}\]
~~~

In the diagram, we draw the specific partial element being extended in
red, and the total path extending it in black. In Agda, extensions are
represented by the type former `Sub`{.Agda}, which we abbreviate by
`_[_↦_]`{.Agda}. Fully applied, that operator looks like `A [ φ → u
]`.[^extensionkind]

[^extensionkind]: `Sub`{.Agda} lives in the universe `SSetω`, which we
do not have a binding for, so we can not name the type of
`_[_↦_]`{.Agda}.

```agda
_[_↦_] : ∀ {ℓ} (A : Type ℓ) (φ : I) (u : Partial φ A) → _
A [ φ ↦ u ] = Sub A φ u
```

We can formalise the red-black extensibility diagram above by defining
the partial element `left-true`{.Agda} and giving `refl`{.Agda} to
`inS`{.Agda}, the constructor for `_[_↦_]`{.Agda}.

```agda
private
  left-true : (i : I) → Partial (~ i) Bool
  left-true i (i = i0) = true

  refl-extends : (i : I) → Bool [ (~ i) ↦ left-true i ]
  refl-extends i = inS (refl {x = true} i)
```

The constructor `inS` expresses that _any_ totally-defined cube $u$ can
be seen as a partial cube, one that agrees with $u$ for any choice of
formula $\varphi$. This might be a bit abstract, so let's diagram the case
where we have some square $a$, and the partial element has formula $i
\land j$. This extension can be drawn as in the diagram below: The red
"backwards L" shape is the partial element, which is "extended by" the
black lines to make a complete square.

~~~{.quiver}
\[\begin{tikzcd}
  {a_{0,0}} && \textcolor{rgb,255:red,214;green,92;blue,92}{a_{0,1}} \\
  & {a_{i,j}} \\
  \textcolor{rgb,255:red,214;green,92;blue,92}{a_{1,0}} && \textcolor{rgb,255:red,214;green,92;blue,92}{a_{1,1}}
  \arrow[from=1-1, to=1-3]
  \arrow[color={rgb,255:red,214;green,92;blue,92}, from=1-3, to=3-3]
  \arrow[from=1-1, to=3-1]
  \arrow[color={rgb,255:red,214;green,92;blue,92}, from=3-1, to=3-3]
\end{tikzcd}\]
~~~

```agda
  _ : ∀ {ℓ} {A : Type ℓ} {φ : I} (u : A) → A [ φ ↦ (λ _ → u) ]
  _ = inS
```

Note that since an extension must agree with the partial element
_everywhere_, there are elements that can not be extended at all. Take
`notAPath`{.Agda} from before --- since there is no path that is
`true`{.Agda} at `i0`{.Agda} and `false`{.Agda} at `i1`{.Agda}, it is
not extensible. If it were extensible, we would have `true ≡ false` ---
a contradiction.[^truenotfalse]

[^truenotfalse]: Although it is not proven to be a contradiction in
_this_ module, see [Data.Bool](Data.Bool.html) for that construction.

```agda
  not-extensible : ((i : I) → Bool [ (~ i ∨ i) ↦ not-a-path i ]) → true ≡ false
  not-extensible ext i = outS (ext i)
```

This counterexample demonstrates the eliminator for `_[_↦_]`{.Agda},
`outS`{.Agda}, which turns an `A [ φ ↦ u ]` to `A`, with a computation
rule saying that, for `x : A [ i1 ↦ u ]`, `outS x` computes to `u 1=1`:

```agda
  _ : ∀ {A : Type} {u : Partial i1 A} {x : A [ i1 ↦ u ]}
    → outS x ≡ u 1=1
  _ = refl
```

The notion of partial elements and extensibility captures the specific
interface of the Kan operations, which can be summed up in the following
sentence: _If a partial path is extensible at `i0`{.Agda}, then it is
extensible at `i1`{.Agda}_. Let's unpack that a bit:

A _partial path_ is anything of type `I → Partial φ A` -- let's say we
have an `f` in that type. It takes a value at `i0`{.Agda} (that's `f
i0`), and a value at `i1`{.Agda}. The Kan condition expresses that, if
there exists an `A [ φ → f i0 ]`, then we also have an `A [ φ → f i1 ]`.
In other words: Extensibility is preserved by paths.

Recall the open box we drew by gluing paths together at the start of the
section (on the left). It has a _top face_ `q`, and it has a _tube_ ---
its left/right faces, which can be considered as a partial (in the
left-right direction) path going in the top-down direction.

<div class=mathpar style="gap: 2em;">
<div style="display: flex; flex-flow: column nowrap; align-items: center;">
~~~{.quiver}
\[\begin{tikzcd}
  x && y \\
  \\
  w && z
  \arrow["{\id{sym}\ p\ j}", from=1-1, to=3-1]
  \arrow["q\ i", from=1-1, to=1-3]
  \arrow["r\ j"', from=1-3, to=3-3]
\end{tikzcd}\]
~~~
<figcaption>
The complete “open box”.
</figcaption>
</div>

<div style="display: flex; flex-flow: column nowrap; align-items: center;">
~~~{.quiver}
\[\begin{tikzcd}
  x && y \\
  \\
  w && z
  \arrow["{\id{sym}\ p\ j}", from=1-1, to=3-1]
  \arrow["r\ j"', from=1-3, to=3-3]
\end{tikzcd}\]
~~~
<figcaption>
The partially-defined “tube”.
</figcaption>
</div>

</div>

We can make this the construction of this “tube” formal by giving a
`Partial`{.Agda} element of `A`, which is defined on $\neg i \lor i$
(that is: only the left/right faces of a square), as is done below.
Since it is a tube of a _square_, it has _two_ interval variables: $j$
gives the top-down direction.[^partialpath]

[^partialpath]: This element has type `(i : I) → I → Partial (~ i ∨ i)
A` rather than `(i : I) → Partial (~ i ∨ i) (I → A)` because of a
universe restriction in Agda: The second argument to `Partial`{.Agda}
must be a `Type`{.Agda}, but `I`{.Agda} is not a `Type`{.Agda}.

```agda
module _ {A : Type} {w x y z : A} {p : w ≡ x} {q : x ≡ y} {r : y ≡ z} where private
  double-comp-tube : (i : I) → I → Partial (~ i ∨ i) A
  double-comp-tube i j (i = i0) = sym p j
  double-comp-tube i j (i = i1) = r j
```

When given `i0`{.Agda} as `j`, `double-comp-tube`{.Agda} has boundary
$p\ \id{i1} \to r\ \id{i0}$, which computes to $x \to y$. This means
that for this path to be extensible at `i0`{.Agda}, we need a path with
that boundary. By assumption, `q` extends `double-comp-tube`{.Agda} at
`i0`{.Agda}.

```agda
  extensible-at-i0 : (i : I) → A [ (i ∨ ~ i) ↦ double-comp-tube i i0 ]
  extensible-at-i0 i = inS (q i)
```

We can draw this as one of our red-black extensibility diagrams
colouring the left/right faces in red --- since that is the partial
element --- and colouring the top face black, since that is a
totally-defined cube.

~~~{.quiver}
\[\begin{tikzcd}
  \textcolor{rgb,255:red,214;green,92;blue,92}{x} && \textcolor{rgb,255:red,214;green,92;blue,92}{y} \\
  \\
  \textcolor{rgb,255:red,214;green,92;blue,92}{w} && \textcolor{rgb,255:red,214;green,92;blue,92}{z}
  \arrow["{\id{sym}\ p\ j}"', color={rgb,255:red,214;green,92;blue,92}, from=1-1, to=3-1]
  \arrow["{r\ j}", color={rgb,255:red,214;green,92;blue,92}, from=1-3, to=3-3]
  \arrow["{q\ i}", from=1-1, to=1-3]
\end{tikzcd}\]
~~~

The Kan condition says that this path is then extensible at `i1`, i.e.
there is some inhabitant of `A [ (i ∨ ~ i) ↦ double-comp-tube i i1 ]`.
This element is written using the operator `hcomp`{.Agda}:

```agda
  extensible-at-i1 : (i : I) → A [ (i ∨ ~ i) ↦ double-comp-tube i i1 ]
  extensible-at-i1 i =
    inS (hcomp {φ = ~ i ∨ i} (λ k is1 → double-comp-tube i k is1) (q i))
```

Unwinding what it means for this element to exist, we see that the
`hcomp`{.Agda} operation guarantees the existence of a path $w \to z$.
It is the face that is hinted at by completing the open box above to a
complete square.

```agda
  double-comp : w ≡ z
  double-comp i = outS (extensible-at-i1 i)
```

Note that `hcomp`{.Agda} gives us the missing face of the open box, but
the semantics guarantees the existence of the box itself, as a $n$-cube.
From the De Morgan structure on the interval, we can derive the
existence of the cubes themselves (called **fillers**) from the
existence of the missing faces:

```agda
hfill : ∀ {ℓ} {A : Type ℓ} {φ : I}
        (u : I → Partial φ A)
        (u0 : A [ φ ↦ u i0 ])
      → outS u0 ≡ hcomp u (outS u0)
hfill {φ = φ} u u0 i =
  hcomp (λ j → λ { (φ = i1) → u (i ∧ j) 1=1
                 ; (i = i0) → outS u0 })
        (outS u0)
```

**Note**: While every inhabitant of `Type`{.Agda} has a composition
operation, not every _type_ (something that can be on the right of type
signature `e : T`) does. We call the types that _do_ have a composition
operation “fibrant”, since these are semantically the cubical sets
which are Kan complices. Examples of types which are _not_ fibrant
include the interval `I`{.Agda}, the partial elements `Partial`{.Agda},
and the extensions `_[_↦_]`[^notfibrant].

> <a id="fibrant">**Definition**</a>: A type is _fibrant_ if it supports
`hcomp`{.Agda}. This word comes up a lot when discussing not only the
semantics of Cubical type theory, but also its practice! For instance,
the fibrancy of `Type`{.Agda} is what powers [univalence].

[univalence]: 1Lab.Univalence.html

[^notfibrant]: In Agda 2.6.2, function types `I → A` are _not_ fibrant,
even though they correspond to paths with “unmarked” endpoints. In Agda
2.6.3 (in development at the time of writing), `I` was moved to its own
universe, `IUniv`, with a typing rule for functions saying that `A → B`
is fibrant whenever `B : Type` and `A : Type` _or_ `A : IUniv` - i.e.
function types `I → A` were made fibrant whenever `A` is.

Agda also provides a _heterogeneous_ version of composition (also called
CCHM composition), called `comp`{.Agda}. It too has a corresponding
filler, called `fill`{.Agda}. The idea behind CCHM composition is --- by
analogy with `hcomp`{.Agda} expressing that "paths preserve
extensibility" --- that `PathP`{.Agda}s preserve extensibility. Thus we
have:

```agda
private
  comp-verbose : ∀ {ℓ} (A : I → Type ℓ)
                   {φ : I}
               → (u : ∀ i → Partial φ (A i))
               → (u0 : A i0 [ φ ↦ u i0 ] )
               → A i1 [ φ ↦ u i1 ]
  comp-verbose A u u0 = inS (comp A u (outS u0))

fill : ∀ {ℓ : I → Level} (A : ∀ i → Type (ℓ i))
       {φ : I}
     → (u : ∀ i → Partial φ (A i))
     → (u0 : A i0 [ φ ↦ u i0 ])
     → ∀ i → A i
fill A {φ = φ} u u0 i =
  comp (λ j → A (i ∧ j))
       (λ j → λ { (φ = i1) → u (i ∧ j) 1=1
                ; (i = i0) → outS u0 })
       (outS u0)
```

Given the inputs to a composition --- a family of partial paths `u` and
a base `u0` --- `hfill`{.Agda} connects the input of the composition
(`u0`) and the output. The cubical shape of iterated identifications
causes a slight oddity: The only unbiased definition of path composition
we can give is _double composition_, which corresponds to the missing
face for the [square] at the start of this section.

[square]: 1Lab.Path.html#composition

```agda
_··_··_ : ∀ {ℓ} {A : Type ℓ} {w x y z : A}
        → w ≡ x → x ≡ y → y ≡ z
        → w ≡ z
(p ·· q ·· r) i =
  hcomp (λ j → λ { (i = i0) → p (~ j)
                 ; (i = i1) → r j })
        (q i)
```

Since it will be useful later, we also give an explicit name for the
filler of the double composition square.

```
··-filler : ∀ {ℓ} {A : Type ℓ} {w x y z : A}
          → (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
          → Square (sym p) q (p ·· q ·· r) r
··-filler p q r i j =
  hfill (λ k → λ { (j = i0) → p (~ k)
                 ; (j = i1) → r k })
        (inS (q j)) i
```

We can define the ordinary, single composition by taking `p = refl`, as
is done below. The square associated with the binary composition
operation is obtained as the same open box at the start of the section,
the same `double-comp-tube`{.Agda}, but by setting any of the faces to
be reflexivity. For definiteness, we chose the left face:

~~~{.quiver}
\[\begin{tikzcd}
  x && y \\
  \\
  x && z
  \arrow["{p}", from=1-1, to=1-3]
  \arrow["{\id{refl}}"', from=1-1, to=3-1]
  \arrow["{q}", from=1-3, to=3-3]
  \arrow["{p \bullet q}"', from=3-1, to=3-3, dashed]
\end{tikzcd}\]
~~~

```agda
_∙_ : ∀ {ℓ} {A : Type ℓ} {x y z : A}
    → x ≡ y → y ≡ z → x ≡ z
p ∙ q = refl ·· p ·· q
```

The ordinary, “single composite” of $p$ and $q$ is the dashed face in
the diagram above.  Since we bound `··-filler`{.Agda} above, and defined
`_∙_`{.Agda} in terms of `_··_··_`{.Agda}, we can reuse the latter's
filler to get one for the former:

```agda
∙-filler : ∀ {ℓ} {A : Type ℓ} {x y z : A}
         → (p : x ≡ y) (q : y ≡ z)
         → Square refl p (p ∙ q) q
∙-filler {x = x} {y} {z} p q = ··-filler refl p q
```

The single composition has a filler “in the other direction”, which
connects $q$ and $p \bullet q$. This is, essentially, because the choice
of setting the left face to `refl`{.Agda} was completely arbitrary in
the definition of `_∙_`{.Agda}: we could just as well have gone with
setting the _right_ face to `refl`{.Agda}.

```agda
∙-filler' : ∀ {ℓ} {A : Type ℓ} {x y z : A}
          → (p : x ≡ y) (q : y ≡ z)
          → Square (sym p) q (p ∙ q) refl
∙-filler' {x = x} {y} {z} p q j i =
  hcomp (λ k → λ { (i = i0) → p (~ j)
                 ; (i = i1) → q k
                 ; (j = i0) → q (i ∧ k) })
        (p (i ∨ ~ j))
```

## Uniqueness

A common characteristic of _geometric_ interpretations of higher
categories --- like the one we have here --- when compared to algebraic
definitions is that there is no prescription in general for how to find
composites of morphisms. Instead, we have that each triple of morphism
has a _contractible space_ of composites. We call the proof of this fact
`··-unique`{.Agda}:

```agda
··-unique : ∀ {ℓ} {A : Type ℓ} {w x y z : A}
          → (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
          → (α β : Σ[ s ∈ (w ≡ z) ] Square (sym p) q s r)
          → α ≡ β
```

Note that the type of `α` and `β` asks for a path `w ≡ z` which
_specifically_ completes the open box for double composition. We would
not in general expect that `w ≡ z` is contractible for an arbitrary `a`!
Note that the proof of this involves filling a cube in a context that
*already* has an interval variable in scope - a hypercube!

```agda
··-unique {w = w} {x} {y} {z} p q r (α , α-fill) (β , β-fill) =
  λ i → (λ j → square i j) , (λ j k → cube i j k)
  where
    cube : (i j : I) → p (~ j) ≡ r j
    cube i j k =
      hfill (λ l → λ { (i = i0) → α-fill l k
                     ; (i = i1) → β-fill l k
                     ; (k = i0) → p (~ l)
                     ; (k = i1) → r l
                     })
            (inS (q k)) j

    square : α ≡ β
    square i j = cube i i1 j
```

The term `cube` above has the following cube as a boundary. Since it is
a filler, there is a missing face at the bottom which has no name, so we
denote it by `hcomp...` in the diagram.


~~~{.quiver .tall-2}
\[\begin{tikzcd}
  \textcolor{rgb,255:red,153;green,92;blue,214}{x} &&&& \textcolor{rgb,255:red,153;green,92;blue,214}{x} \\
  & \textcolor{rgb,255:red,214;green,92;blue,92}{y} && \textcolor{rgb,255:red,214;green,92;blue,92}{y} \\
  \\
  & \textcolor{rgb,255:red,214;green,92;blue,92}{z} && \textcolor{rgb,255:red,214;green,92;blue,92}{z} & {} \\
  \textcolor{rgb,255:red,153;green,92;blue,214}{w} &&&& \textcolor{rgb,255:red,153;green,92;blue,214}{w}
  \arrow[""{name=0, anchor=center, inner sep=0}, color={rgb,255:red,214;green,92;blue,92}, from=4-2, to=4-4]
  \arrow[""{name=1, anchor=center, inner sep=0}, color={rgb,255:red,214;green,92;blue,92}, from=2-4, to=4-4]
  \arrow[""{name=2, anchor=center, inner sep=0}, color={rgb,255:red,214;green,92;blue,92}, from=2-2, to=2-4]
  \arrow[""{name=3, anchor=center, inner sep=0}, color={rgb,255:red,214;green,92;blue,92}, from=2-2, to=4-2]
  \arrow[""{name=4, anchor=center, inner sep=0}, color={rgb,255:red,153;green,92;blue,214}, from=1-5, to=5-5]
  \arrow[""{name=5, anchor=center, inner sep=0}, color={rgb,255:red,153;green,92;blue,214}, from=1-1, to=5-1]
  \arrow[""{name=6, anchor=center, inner sep=0}, color={rgb,255:red,153;green,92;blue,214}, from=5-1, to=5-5]
  \arrow[""{name=7, anchor=center, inner sep=0}, color={rgb,255:red,153;green,92;blue,214}, from=1-1, to=1-5]
  \arrow[from=1-5, to=2-4]
  \arrow[from=1-1, to=2-2]
  \arrow["{\alpha\ k}"', from=5-1, to=4-2]
  \arrow["{\beta\ k}", from=5-5, to=4-4]
  \arrow["{\alpha\text{-filler}\ j\ k}"{description}, shorten >=6pt, Rightarrow, from=5, to=3]
  \arrow["{\beta\text{-filler}\ j\ k}"{description}, Rightarrow, draw=none, from=4, to=1]
  \arrow[""{name=8, anchor=center, inner sep=0}, "{\id{hcomp}\dots}"{description}, Rightarrow, draw=none, from=6, to=0]
  \arrow["{r\ j}"{description}, color={rgb,255:red,214;green,92;blue,92}, Rightarrow, draw=none, from=0, to=2]
  \arrow["{q\ k}"{description}, Rightarrow, draw=none, from=2, to=7]
  \arrow["{p\ \neg j}"{description}, shift left=2, color={rgb,255:red,153;green,92;blue,214}, Rightarrow, draw=none, from=8, to=7]
\end{tikzcd}\]
~~~

This diagram is quite busy because it is a 3D commutative diagram, but
it could be busier: all of the unimportant edges were not annotated. By
the way, the lavender face (including the lavender $p\ \neg j$) is the
$k = \id{i0}$ face, and the red face is the $k = \id{i1}$ face.

However, even though the diagram is very busy, most of the detail it
contains can be ignored. Reading it in the left-right direction, it
expresses an identification between `α-filler j k` and `β-filler j k`,
lying over a homotopy `α = β`. That homotopy is what you get when you
read the bottom square of the diagram in the left-right direction.
Explicitly, here is that bottom square:

~~~{.quiver}
\[\begin{tikzcd}
  \textcolor{rgb,255:red,214;green,92;blue,92}{z} && \textcolor{rgb,255:red,214;green,92;blue,92}{z} \\
  \\
  \textcolor{rgb,255:red,153;green,92;blue,214}{w} && \textcolor{rgb,255:red,153;green,92;blue,214}{w}
  \arrow["\alpha", from=3-1, to=1-1]
  \arrow["\beta"', from=3-3, to=1-3]
  \arrow[""{name=0, anchor=center, inner sep=0}, "w", color={rgb,255:red,153;green,92;blue,214}, from=3-1, to=3-3]
  \arrow[""{name=1, anchor=center, inner sep=0}, "z"', color={rgb,255:red,214;green,92;blue,92}, from=1-1, to=1-3]
  \arrow["{\id{hcomp}\dots}"{description}, Rightarrow, draw=none, from=0, to=1]
\end{tikzcd}\]
~~~

Note that, exceptionally, this diagram is drawn with the left/right
edges going up rather than down. This is to match the direction of the
3D diagram above. The colours are also matching.

Readers who are already familiar with the notion of h-level will have
noticed that the proof `··-unique`{.Agda} expresses that the type of
double composites `p ·· q ·· r` is a _proposition_, not that it is
contractible. However, since it is inhabited (by `_··_··_`{.Agda} and
its filler), it is contractible:

```
··-contract : ∀ {ℓ} {A : Type ℓ} {w x y z : A}
            → (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
            → (β : Σ[ s ∈ (w ≡ z) ] Square (sym p) q s r)
            → (p ·· q ·· r , ··-filler p q r) ≡ β
··-contract p q r β = ··-unique p q r _ β
```

## Syntax Sugar

When constructing long chains of identifications, it's rather helpful to
be able to visualise _what_ is being identified with more "priority"
than _how_ it is being identified. For this, a handful of combinators
with weird names are defined:

```agda
≡⟨⟩-syntax : ∀ {ℓ} {A : Type ℓ} (x : A) {y z} → y ≡ z → x ≡ y → x ≡ z
≡⟨⟩-syntax x q p = p ∙ q

infixr 2 ≡⟨⟩-syntax
syntax ≡⟨⟩-syntax x q p = x ≡⟨ p ⟩ q

_≡˘⟨_⟩_ : ∀ {ℓ} {A : Type ℓ} (x : A) {y z : A} → y ≡ x → y ≡ z → x ≡ z
x ≡˘⟨ p ⟩ q = (sym p) ∙ q

_≡⟨⟩_ : ∀ {ℓ} {A : Type ℓ} (x : A) {y : A} → x ≡ y → x ≡ y
x ≡⟨⟩ x≡y = x≡y

_∎ : ∀ {ℓ} {A : Type ℓ} (x : A) → x ≡ x
x ∎ = refl

infixr 30 _∙_
infixr 2 _≡⟨⟩_ _≡˘⟨_⟩_
infix  3 _∎
```

These functions are used to make _equational reasoning chains_. For
instance, the following proof that addition of naturals is associative
is done in equational reasoning style:

```agda
private
  +-associative : (x y z : Nat) → (x + y) + z ≡ x + (y + z)
  +-associative zero y z = refl
  +-associative (suc x) y z =
    suc ((x + y) + z) ≡⟨ ap suc (+-associative x y z) ⟩
    suc (x + (y + z)) ∎
```

If your browser runs JavaScript, these equational reasoning chains, by
default, render with the _justifications_ (the argument written between
`⟨ ⟩`) hidden; There is a checkbox to display them, either on the
sidebar or on the top bar depending on how narrow your screen is. For
your convenience, it's here too:

<div style="display: flex; flex-direction: column; align-items: center;">
  <span class="equations" style="display: flex; gap: 0.25em; flex-wrap: nowrap;">
    <input name=body-eqns type="checkbox" class="equations" id=body-eqns>
    <label for=body-eqns>Equations</label>
  </span>
</div>

Try pressing it!

<!--
```
SquareP : ∀ {ℓ}
  (A : I → I → Type ℓ)
  {a₀₀ : A i0 i0} {a₀₁ : A i0 i1}
  {a₁₀ : A i1 i0} {a₁₁ : A i1 i1}
  (p : PathP (λ i → A i i0) a₀₀ a₁₀)
  (q : PathP (λ j → A i0 j) a₀₀ a₀₁)
  (s : PathP (λ j → A i1 j) a₁₀ a₁₁)
  (r : PathP (λ i → A i i1) a₀₁ a₁₁)
  → Type ℓ
SquareP A p q s r = PathP (λ i → PathP (λ j → A i j) (p i) (r i)) q s
```
-->

# Dependent Paths

Surprisingly often, we want to compare inhabitants $a : A$ and $b : B$
where the types $A$ and $B$ are not _definitionally_ equal, but only
identified in some specified way. We call these "**paths** over
**p**paths", or `PathP`{.Agda} for short. In the same way that a
`Path`{.Agda} can be understood as a function `I → A` with specified
endpoints, a `PathP`{.Agda} (*path* over *p*ath) can be understood as a
_dependent_ function `(i : I) → A i`.

In the Book, paths over paths are implemented in terms of the
`transport`{.Agda} operation: A path `x ≡ y` over `p` is a path
`transport p x ≡ y`, thus defining dependent identifications using
non-dependent ones. Fortunately, a cubical argument shows us that these
notions coincide:

```agda
PathP≡Path : ∀ {ℓ} (P : I → Type ℓ) (p : P i0) (q : P i1)
           → PathP P p q ≡ Path (P i1) (transport (λ i → P i) p) q
PathP≡Path P p q i = PathP (λ j → P (i ∨ j)) (transport-filler (λ j → P j) p i) q

PathP≡Path⁻ : ∀ {ℓ} (P : I → Type ℓ) (p : P i0) (q : P i1)
            → PathP P p q ≡ Path (P i0) p (transport (λ i → P (~ i)) q)
PathP≡Path⁻ P p q i = PathP (λ j → P (~ i ∧ j)) p
                            (transport-filler (λ j → P (~ j)) q i)
```

We can see this by substituting either `i0` or `i1` for the variable `i`.

* When `i = i0`, we have `PathP (λ j → P j) p q`, by the endpoint rule
for `transport-filler`{.Agda}.

* When `i = i1`, we have `PathP (λ j → P i1) (transport P p) q`, again
by the endpoint rule for `transport-filler`{.Agda}.

The existence of paths over paths gives another "counterexample" to
thinking of paths as _equality_. For instance, it's hard to imagine a
world in which `true` and `false` can be equal in any interesting sense
of the word _equal_ --- but over the identification $\id{Bool} \equiv
\id{Bool}$ that switches the points around, `true` and `false` can be
identified!

## Coercion

In Cubical Agda, the interval is given the structure of a De Morgan
algebra. This is not the only choice of structure on the interval that
gives a model of univalent type theory: We could also subject the
interval to _no_ additional structure other than what comes from the
structural rules of type theory (introducing variables, ignoring
variables, swapping variables, etc). This is a different cubical type
theory, called _Cartesian cubical type theory_.

In Cartesian cubical type theory, instead of having a `transp`{.Agda}
operation which takes $A(\id{i0}) \to A(\id{i1})$, there is a “more
powerful” _coercion_ operation, written $\id{coe}^A_{i \to j}$, which
takes $A(i) \to A(j)$, as in the subscript. However, despite the seeming
added power, the coercion operation can be implemented in Cubical Agda:
First, we introduce alternative names for several uses of
`transp`{.Agda}.

```agda
coe0→1 : ∀ {ℓ} (A : I → Type ℓ) → A i0 → A i1
coe0→1 A a = transp (λ i → A i) i0 a
-- ^ This is another name for transport

coe1→0 : ∀ {ℓ} (A : I → Type ℓ) → A i1 → A i0
coe1→0 A a = transp (λ i → A (~ i)) i0 a
-- ^ This is equivalent to transport ∘ sym
```

There are also “more exciting” operations, which transport from one of
the endpoints to a path which can vary over the interval. These
generalise the `transport-filler`{.Agda} operation.

```agda
coe0→i : ∀ {ℓ : I → Level} (A : ∀ i → Type (ℓ i)) (i : I) → A i0 → A i
coe0→i A i a = transp (λ j → A (i ∧ j)) (~ i) a

coe1→i : ∀ {ℓ : I → Level} (A : ∀ i → Type (ℓ i)) (i : I) → A i1 → A i
coe1→i A i a = transp (λ j → A (i ∨ ~ j)) i a
```

We visualise `coe0→i`{.Agda} and `coe1→i`{.Agda} as being "spread"
operations, since they take a value from one endpoint of the interval (0
or 1, respectively) and "spread it" to a line varying over the variable
`i`. Similarly, we have "squeeze" operations, which take a line varying
over `i` to one of the endpoints:

```
coei→0 : ∀ {ℓ : I → Level} (A : ∀ i → Type (ℓ i)) (i : I) → A i → A i0
coei→0 A i a = transp (λ j → A (i ∧ ~ j)) (~ i) a
```

Using the filler of a square, we can put together the `0→i` and `1→i`
coercions to get the "master coercion" operation. That square is drawn
as the diagram below, where the edges are more important than the
corners, and the dashed line is `coe A i i1`.

~~~{.quiver}
\[\begin{tikzcd}
  {a} && {\id{coe}^A_{1\to0}(a)} \\
  \\
  {\id{coe}^A_{0\to1}(a)} && {a}
  \arrow["{\id{coe}^A_{0\to j}(a)}"', from=1-1, to=3-1]
  \arrow["{\id{coe}^A_{1\to j}(a)}", from=1-3, to=3-3]
  \arrow[""{name=0, anchor=center, inner sep=0}, "{\id{coe}^A_{i\to0}(a)}", from=1-1, to=1-3]
  \arrow[""{name=1, anchor=center, inner sep=0}, "{\id{coe}^A_{i\to1}(a)}"', dashed, from=3-1, to=3-3]
  \arrow["{\id{coe}^A_{i\to j}(a)}"{description}, Rightarrow, draw=none, from=0, to=1]
\end{tikzcd}\]
~~~

```agda
coe : ∀ {ℓ : I → Level} (A : ∀ i → Type (ℓ i)) (i j : I) → A i → A j
coe A i j a =
  fill A (λ j → λ { (i = i0) → coe0→i A j a
                  ; (i = i1) → coe1→i A j a
                  })
    (inS (coei→0 A i a)) j
```

As the square implies, when `j = i1`, we have the squeeze operation
opposite to `coei→0`{.Agda}, which we call `coei→1`{.Agda}.

```
coei→1 : ∀ {ℓ : I → Level} (A : ∀ i → Type (ℓ i)) (i : I) → A i → A i1
coei→1 A i a = coe A i i1 a
```

**Sidenote**: The boundary for the square implies that we can give a
more verbose type for `coe`{.Agda}, one which mentions all of the
spreads and squeezes. Note that this is a _dependent path between
functions $A\ i \to A\ j$_, a very complicated construction indeed!

```agda
private
  coe-verbose : ∀ {ℓ} (A : I → Type ℓ)
              → PathP (λ i → PathP (λ j → A i → A j)
                                (coei→0 A i)
                                (coei→1 A i))
                      (λ j → coe0→i A j)
                      (λ j → coe1→i A j)
  coe-verbose A i j = coe A i j
```

This operation satisfies, _definitionally_, a whole host of equations.
For starters, we have that the $\id{coe}^A_{i\to1}$ (resp $i \to 0$)
specialises to transport when $i = 0$ (resp. $i = 1$), and to the
identity when $i = 1$ (resp. $i = 0$):

```agda
coei0→1 : ∀ {ℓ} (A : I → Type ℓ) (a : A i0) → coei→1 A i0 a ≡ coe0→1 A a
coei0→1 A a = refl

coei1→1 : ∀ {ℓ} (A : I → Type ℓ) (a : A i1) → coei→1 A i1 a ≡ a
coei1→1 A a = refl

coei1→0 : ∀ {ℓ} (A : I → Type ℓ) (a : A i1) → coei→0 A i1 a ≡ coe1→0 A a
coei1→0 A a = refl

coei0→0 : ∀ {ℓ} (A : I → Type ℓ) (a : A i0) → coei→0 A i0 a ≡ a
coei0→0 A a = refl
```

Then we have paths connecting the "master coercion" `coe`{.Agda} and
its several faces:

```
coei→i0 : ∀ {ℓ} (A : I → Type ℓ) (i : I) (a : A i)
        → coe A i i0 a ≡ coei→0 A i a
coei→i0 A i a = refl

coei0→i : ∀ {ℓ} (A : I → Type ℓ) (i : I) (a : A i0)
        → coe A i0 i a ≡ coe0→i A i a
coei0→i A i a = refl

coei→i1 : ∀ {ℓ} (A : I → Type ℓ) (i : I) (a : A i)
        → coe A i i1 a ≡ coei→1 A i a
coei→i1 A i a = refl

coei1→i : ∀ {ℓ} (A : I → Type ℓ) (i : I) (a : A i1)
        → coe A i1 i a ≡ coe1→i A i a
coei1→i A i a = refl
```

In Cartesian cubical type theory, the following equation is
definitional. It says that the top right and bottom left corners of the
diagram are indeed what I said they were! However, in Cubical Agda, it
is only propositional:

```agda
coei→i : ∀ {ℓ} (A : I → Type ℓ) (i : I) (a : A i) → coe A i i a ≡ a
coei→i A i = coe0→i (λ i → (a : A i) → coe A i i a ≡ a) i (λ _ → refl)
```

Using the Cartesian coercions, we define maps that convert between
`PathP`{.Agda}s and Book dependent paths. These maps could also be
defined in terms of `transp`{.Agda} and `PathP≡Path`{.Agda}, but this
definition is more efficient.

```agda
to-pathp : ∀ {ℓ} {A : I → Type ℓ} {x : A i0} {y : A i1}
         → coe0→1 A x ≡ y
         → PathP A x y
to-pathp {A = A} {x} p i =
  hcomp (λ j → λ { (i = i0) → x
                 ; (i = i1) → p j })
        (coe0→i A i x)

from-pathp : ∀ {ℓ} {A : I → Type ℓ} {x : A i0} {y : A i1}
           → PathP A x y
           → coe0→1 A x ≡ y
from-pathp {A = A} p i = coei→1 A i (p i)
```

These definitions illustrate how using the named squeezes and spreads
--- `coe0→i`{.Agda}, `coei→1`{.Agda} --- can be a lot more elegant than
trying to work out what composition to use in a `transp`{.Agda}.

# Path Spaces

A large part of the study of HoTT is the _characterisation of path
spaces_. Given a type `A`, what does `Path A x y` look like? [Hedberg's
theorem] says that for types with decidable equality, it's boring. For
[the circle], we can prove its loop space is the integers --- we have
`Path S¹ base base ≡ Int`.

[Hedberg's theorem]: 1Lab.HLevel.Sets.html
[the circle]: 1Lab.HIT.S1.html

Most of these characterisations need machinery that is not in this
module to be properly stated. Even then, we can begin to outline a few
simple cases:

## Σ Types

For `Σ`{.Agda} types, a path between `(a , b) ≡ (x , y)` consists of a
path `p : a ≡ x`, and a path between `b` and `y` laying over `p`.

```agda
Σ-pathp : ∀ {a b} {A : Type a} {B : A → Type b}
        → {x y : Σ B}
        → (p : x .fst ≡ y .fst)
        → PathP (λ i → B (p i)) (x .snd) (y .snd)
        → x ≡ y
Σ-pathp p q i = p i , q i
```

We can also use the book characterisation of dependent paths, which is
simpler in the case where the `Σ`{.Agda} represents a subset --- i.e.,
`B` is a family of propositions.

```agda
Σ-path : ∀ {a b} {A : Type a} {B : A → Type b}
       → {x y : Σ B}
       → (p : x .fst ≡ y .fst)
       → subst B p (x .snd) ≡ (y .snd)
       → x ≡ y
Σ-path {A = A} {B} {x} {y} p q = Σ-pathp p (to-pathp q)
```

## Π types

For dependent functions, the paths are _homotopies_, in the topological
sense: `Path ((x : A) → B x) f g` is the same thing as a function `I →
(x : A) → B x` --- which we could turn into a product if we really wanted
to.

```agda
happly : ∀ {a b} {A : Type a} {B : A → Type b}
         {f g : (x : A) → B x}
       → f ≡ g → (x : A) → f x ≡ g x
happly p x i = p i x
```

With this, we have made definitional yet another principle which is
propositional in the HoTT book: _function extensionality_. Functions are
identical precisely if they assign the same outputs to every input.

```agda
funext : ∀ {a b} {A : Type a} {B : A → Type b}
         {f g : (x : A) → B x}
       → ((x : A) → f x ≡ g x) → f ≡ g
funext p i x = p x i
```

Furthermore, we know (since types are groupoids, and functions are
functors) that, by analogy with 1-category theory, paths in a function
type should behave like natural transformations (because they are arrows
in a functor category). This is indeed the case:

```agda
homotopy-natural : ∀ {a b} {A : Type a} {B : Type b}
                 → {f g : A → B}
                 → (H : (x : A) → f x ≡ g x)
                 → {x y : A} (p : x ≡ y)
                 → H x ∙ ap g p ≡ ap f p ∙ H y
homotopy-natural {f = f} {g = g} H p =
  J (λ _ p → H _ ∙ ap g p ≡ ap f p ∙ H _)
    (sym (∙-filler (H _) refl) ∙ ∙-filler' refl (H _))
    p
```

## Paths

The groupoid structure of _paths_ is also interesting. While the
characterisation of `Path (Path A x y) p q` is fundamentally tied to the
characterisation of `A`, there are general theorems that can be proven
about _transport_ in path spaces. For example, substituting on both
endpoints of a path is equivalent to a ternary composition:

```agda
subst-path-both : ∀ {ℓ} {A : Type ℓ} {x y : A}
                → (loop : x ≡ x)
                → (adj : x ≡ y)
                → subst (λ x → x ≡ x) adj loop ≡ sym adj ∙ loop ∙ adj
subst-path-both loop adj =
  J (λ _ adj → subst (λ x → x ≡ x) adj loop ≡ sym adj ∙ loop ∙ adj)
    (sym lemma)
    adj
  where
```

The proof is by induction on the path `adj` (for `adjustment`): It
suffices to consider the case where it is `refl`. In that case, it
becomes an application of the [groupoid laws for types].

[groupoid laws for types]: 1Lab.Path.Groupoid.html

```agda
    lemma : sym refl ∙ loop ∙ refl ≡ subst (λ x → x ≡ x) refl loop
    lemma =
      sym refl ∙ loop ∙ refl    ≡⟨⟩
      refl ∙ loop ∙ refl        ≡⟨ sym (∙-filler' refl _) ⟩
      loop ∙ refl               ≡⟨ sym (∙-filler _ refl) ⟩
      loop                      ≡⟨ sym (transport-refl _) ⟩
      subst (λ x → x) refl loop ∎
```

Similar statements can be proven about substitution where we hold the
right endpoint constant, in which case we get something homotopic to
composing with the inverse of the adjustment:

```agda
subst-path-left : ∀ {ℓ} {A : Type ℓ} {x y z : A}
                → (loop : x ≡ z)
                → (adj : x ≡ y)
                → subst (λ e → e ≡ z) adj loop ≡ sym adj ∙ loop
subst-path-left {x = x} {y} {z} loop adj =
  J (λ _ adj → subst (λ e → e ≡ z) adj loop ≡ sym adj ∙ loop)
    (sym lemma)
    adj
  where
    lemma : sym refl ∙ loop ≡ subst (λ e → e ≡ z) refl loop
    lemma =
      sym refl ∙ loop           ≡⟨⟩
      refl ∙ loop               ≡⟨ sym (∙-filler' refl _) ⟩
      loop                      ≡⟨ sym (transport-refl _) ⟩
      subst (λ x → x) refl loop ∎
```

And for the case where we hold the left endpoint constant, in which case
we get a respelling of composition:

```agda
subst-path-right : ∀ {ℓ} {A : Type ℓ} {x y z : A}
                 → (loop : x ≡ z)
                 → (adj : z ≡ y)
                 → subst (λ e → x ≡ e) adj loop ≡ loop ∙ adj
subst-path-right {x = x} loop adj =
  J (λ _ adj → subst (λ e → x ≡ e) adj loop ≡ loop ∙ adj)
    (sym lemma)
    adj
  where
    lemma : loop ∙ refl ≡ subst (λ e → x ≡ e) refl loop
    lemma =
      loop ∙ refl               ≡⟨ sym (∙-filler _ refl) ⟩
      loop                      ≡⟨ sym (transport-refl _) ⟩
      subst (λ x → x) refl loop ∎
```

<!--
TODO: Explain these whiskerings

```agda
_◁_ : ∀ {ℓ} {A : I → Type ℓ} {a₀ a₀' : A i0} {a₁ : A i1}
  → a₀ ≡ a₀' → PathP A a₀' a₁ → PathP A a₀ a₁
(p ◁ q) i =
  hcomp (λ j → λ {(i = i0) → p (~ j); (i = i1) → q i1}) (q i)

_▷_ : ∀ {ℓ} {A : I → Type ℓ} {a₀ : A i0} {a₁ a₁' : A i1}
  → PathP A a₀ a₁ → a₁ ≡ a₁' → PathP A a₀ a₁'
(p ▷ q) i =
  hcomp (λ j → λ {(i = i0) → p i0; (i = i1) → q j}) (p i)

Square≡·· : ∀ {ℓ} {A : Type ℓ}
          → {w x y z : A}
          → {p : x ≡ w} {q : x ≡ y} {s : w ≡ z} {r : y ≡ z}
          → Square p q s r ≡ (sym p ·· q ·· r ≡ s)
Square≡·· {p = p} {q} {s} {r} k =
  PathP (λ i → p (i ∨ k) ≡ r (i ∨ k))
    (··-filler (sym p) q r k) s

≡⟨⟩⟨⟩-syntax : ∀ {ℓ} {A : Type ℓ} (x y : A) {w z : A} → x ≡ y → y ≡ z → z ≡ w → x ≡ w
≡⟨⟩⟨⟩-syntax x y p q r = p ·· q ·· r
infixr 2.5 ≡⟨⟩⟨⟩-syntax
syntax ≡⟨⟩⟨⟩-syntax x y B C = x ≡⟨ B ⟩≡ y ≡⟨ C ⟩≡

J′ : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁}
     (P : (x y : A) → x ≡ y → Type ℓ₂)
   → (∀ x → P x x refl)
   → {x y : A} (p : x ≡ y)
   → P x y p
J′ P prefl {x} p = transport (λ i → P x (p i) λ j → p (i ∧ j)) (prefl x)

··≡twice∙
  : ∀ {ℓ} {A : Type ℓ}
  → {x y z w : A}
  → (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
  → p ·· q ·· r ≡ p ∙ q ∙ r
··≡twice∙ p q r i j =
  hcomp (λ k → λ { (i = i1) → ∙-filler' p (q ∙ r) k j
                 ; (j = i0) → p (~ k)
                 ; (j = i1) → r (i ∨ k)})
        (∙-filler q r i j)

invert-sides : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : x ≡ z)
             → Square q p (sym q) (sym p)
invert-sides {x = x} p q i j =
  hcomp (λ k → λ { (i = i0) → p (k ∧ j)
                 ; (i = i1) → q (~ j ∧ k)
                 ; (j = i0) → q (i ∧ k)
                 ; (j = i1) → p (~ i ∧ k)})
        x

sym-∙-filler : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) → I → I → I → A
sym-∙-filler {A = A} {z = z} p q i j k =
  hfill (λ k → λ { (i = i0) → q (k ∨ j)
                 ; (i = i1) → p (~ k ∧ j) })
       (inS (invert-sides q (sym p) i j))
       k

sym-∙ : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) → sym (p ∙ q) ≡ sym q ∙ sym p
sym-∙ p q i j = sym-∙-filler p q j i i1

```
-->
