```agda
open import 1Lab.Type

module 1Lab.Path where
```

# The Interval

In HoTT, the inductively-defined propositional equality type gets a new
semantics: continuous _paths_. The "key idea" of cubical type theory -
and thus, Cubical Agda --- is that we can take this as a new _definition_
of the equality type, where we interpret a `Path`{.Agda} in a type by a
function where the domain is the _interval type_.

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

Path : ∀ {ℓ} (A : Type ℓ) → A → A → Type ℓ
Path A = PathP (λ i → A)
```

The type `I`{.Agda} is meant to represent the unit interval $[0,1]$, the
same unit interval used in the definition of path. Since all functions
definable in type theory are automatically continuous, we can take a
path to be a _function_ `I → A`. More practically, it's useful to
write out the endpoints of the path --- that is, the values the function
takes when applied to `i0` and to `i1`. This we call a `Path`{.Agda}.

```agda
private
  toPath : ∀ {ℓ} {A : Type ℓ} → (f : I → A) → Path A (f i0) (f i1)
  toPath f i = f i

refl : ∀ {ℓ} {A : Type ℓ} {x : A} → x ≡ x
refl {x = x} = toPath (λ i → x)
```

The type `Path A x y` is also written `x ≡ y`, when `A` is not important
- i.e. when it can be inferred from `x` and `y`. The proof that equality
is reflexive is given by a `Path`{.Agda} which yields the same element
everywhere on `I`: The constant function.

The endpoints of a path --- even a path we do not know the definition of -
are equal, by computation, to the ones specified in its type.

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
`Type`{.Agda}.

- $x \land \mathrm{i0} = \mathrm{i0}$, $x \land \mathrm{i1} = x$
- $x \lor \mathrm{i0} = x$, $x \lor \mathrm{i1} = \mathrm{i1}$
- $\neg(x \land y) = \neg x \lor \neg y$
- $\neg\mathrm{i0} = \mathrm{i1}$, $\neg\mathrm{i0} = \mathrm{i1}$, $\neg\neg{}x = x$
- $\land$ and $\lor$ are both commutative, and distribute over eachother.

Note that, in the formalisation, $\neg x$ is written `~ x`. As a more
familiar description, a De Morgan algebra is a Boolean algebra that does
not (necessarily) satisfy the law of excluded middle. This is necessary
to maintain type safety.

## Raising Dimension

To wit: In cubical type theory, a term in a context with $n$ interval
variables expresses a way of mapping an $n$-cube into that type. One
very important class of these maps are the $1$-cubes, lines, or
[_paths_], which represent equalities between terms of that type.

Iterating this construction, a term in a context with 2 interval
variables represents a square in the type, which can be read as saying
that some _paths_ (specialising one of the variables to $i0$ or $i1$) in
that space are equal: An equality between equalities.

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

These squares can be drawn as below:

<div class="mathpar">

~~~{.quiver}
\[\begin{tikzcd}
  a && b \\
  \\
  a && b
  \arrow["p", from=1-1, to=1-3]
  \arrow["p"', from=3-1, to=3-3]
  \arrow["{\mathrm{refl}}"{description}, from=1-1, to=3-1]
  \arrow["{\mathrm{refl}}"{description}, from=1-3, to=3-3]
\end{tikzcd}\]
~~~

~~~{.quiver}
\[\begin{tikzcd}
  a && a \\
  \\
  b && b
  \arrow["{\mathrm{refl}}", from=1-1, to=1-3]
  \arrow["{\mathrm{refl}}"', from=3-1, to=3-3]
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
  \arrow["{\mathrm{refl}}", from=1-1, to=1-3]
  \arrow["p"', from=3-1, to=3-3]
  \arrow["{\mathrm{refl}}"{description}, from=1-1, to=3-1]
  \arrow["{p}"{description}, from=1-3, to=3-3]
\end{tikzcd}\]
~~~

~~~{.quiver}
\[\begin{tikzcd}
  a && b \\
  \\
  b && b
  \arrow["{p}", from=1-1, to=1-3]
  \arrow["{\mathrm{refl}}"', from=3-1, to=3-3]
  \arrow["p"{description}, from=1-1, to=3-1]
  \arrow["{\mathrm{refl}}"{description}, from=1-3, to=3-3]
\end{tikzcd}\]
~~~

</div>

## Symmetry

The involution `~_`{.Agda} on the interval type gives a way of
inverting paths --- a proof that equality is symmetric.

```agda
sym : ∀ {ℓ₁} {A : Type ℓ₁} {x y : A}
    → x ≡ y → y ≡ x
sym p i = p (~ i)
```

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
as functions out of an internal De Morgan algebra, the _equality_
structure induced by paths is more complicated. For starters, let's see
how paths correspond to equality in that they witness the logical
principle of "indiscernibility of identicals".

## Transport

A basic principle of equality is that _equals may be substituted for
equals_: if $x = y$ and $P(x)$ holds, then $P(y)$ also holds, for any
choice of predicate $P$. In type theory, this is generalised, as $P$ can
be not only a predicate, but any type family.

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

[see here]: agda://Data.Bool#AutBool≡2

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
`transport`{.Agda}: `transport p x` and `x` _are_ equal, but they're
equal _over_ the given path:

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
transport-fillerExt : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B)
                    → PathP (λ i → A → p i) (λ x → x) (transport p)
transport-fillerExt p i x = transport-filler p x i

transport¯-fillerExt : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B)
                     → PathP (λ i → p i → A) (λ x → x) (transport (sym p))
transport¯-fillerExt p i x = transp (λ j → p (i ∧ ~ j)) (~ i) x

transport¯Transport : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) (a : A)
                    → transport (sym p) (transport p a) ≡ a
transport¯Transport p a i = 
  transport¯-fillerExt p (~ i) (transport-fillerExt p (~ i) a)
```
</details>

The path is constant when `i = i1` because `(λ j → p (i1 ∧ j))` is
`(λ j → p i1)` (by the reduction rules for `_∧_`{.Agda}). It has the
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
→ A (~ i)`, compute `f x' : B i0 x`, then transport along `(λ i → B i x')` to g- Wait.

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
of A of the elements equal to x":

```agda
Singleton : ∀ {ℓ} {A : Type ℓ} → A → Type _
Singleton x = Σ[ y ∈ _ ] (x ≡ y)
```

There is a canonical inhabitant of `Singleton x`, namely `(x, refl)`. To
say that `singletons`{.Agda ident=singleton} are contractible is to say
that every other inhabitant has a path to `(x, refl)`:

```agda
isContr-Singleton : ∀ {ℓ} {A : Type ℓ} {x : A} (y : Singleton x)
                  → Path (Singleton x) (x , refl) y
isContr-Singleton {x = x} (y , path) i = p i , square i where
  p : x ≡ y
  p = path

  square : PathP (λ i → x ≡ p i) refl p
  square i j = p (i ∧ j)
```

Thus, the definition of `J`{.Agda}: `transport`{.Agda} +
`isContr-Singleton`{.Agda}.

```agda
J : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {x : A}
    (P : (y : A) → x ≡ y → Type ℓ₂)
  → P x refl
  → {y : A} (p : x ≡ y)
  → P y p
J {x = x} P prefl {y} p = transport (λ i → P (path i .fst) (path i .snd)) prefl where
  path : (x , refl) ≡ (y , p)
  path = isContr-Singleton (y , p)
```

This eliminator _doesn't_ definitionally compute to `prefl` when `p` is
`refl`, again since `transport (λ i → A)` isn't definitionally the
identity.  However, since it _is_ a transport, we can use the
`transport-filler`{.Agda} to get a path expressing the computation rule.

```agda
JRefl : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {x : A}
        (P : (y : A) → x ≡ y → Type ℓ₂)
      → (pxr : P x refl)
      → J P pxr refl ≡ pxr
JRefl {x = x} P prefl i = transport-filler (λ i → P _ (λ j → x)) prefl (~ i)
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
paths as equality, this is a proof that all functions preserve equality.

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

This operation satisfies many equalities definitionally that are only
propositional when `ap`{.Agda} is defined in terms of `J`{.Agda}. For instance:

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

[a different module]: agda://1Lab.Path.Groupoid#ap-comp-path

# Composition

In "Book HoTT", the primitive operation from which the
higher-dimensional structure of types is derived is the `J`{.Agda}
eliminator, with `JRefl`{.Agda} as a _definitional_ computation rule.
This has the benefit of being very elegant: This one elimination rule
generates an infinite amount of coherent data. However, it's very hard
to make compute in the presence of higher inductive types and
univalence, so much so that, in the book, univalence and HITs only
compute up to paths.

In Cubical Agda, types are interpreted as objects called _cubical Kan
complexes_[^1], which are a _geometric_ description description of
spaces as "sets we can probe by cubes". In Agda, this "probing" is
reflected by mapping the interval into a type: A "probe" of $A$ by an
$n$-cube is a term of type $A$ in a context with $n$ variables of type
`I`{.Agda} --- points, lines, squares, cubes, etc. This structure lets
us “explore” the higher dimensional structure of a type, but it does not
specify how this structure behaves.

[^1]: I (Amélia) wrote [a blog post] explaining the semantics of them in
a lot of depth.

[a blog post]: https://amelia.how/posts/cubical-sets.html

That's where the "Kan" part of "cubical Kan complex" comes in:
Semantically, _every open box extends to a cube_. The concept of "open
box" might make even less sense than the concept of "cube in a type"
initially, so it helps to picture them! Suppose we have three paths $p :
w ≡ x$, $q : x ≡ y$, and $r : y ≡ z$. We can pictorially them into an
open box like in the diagram below, by joining the paths by their common
endpoints:

<figure>
~~~{.quiver}
\[\begin{tikzcd}
  x && y \\
  \\
  w && z
  \arrow["{\mathrm{sym}\ p}"', from=1-1, to=3-1]
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
is a face missing - the line $w ≡ z$. The interpretation of types as
_Kan_ cubical sets guarantees that the open box above extends to a
complete square, and thus the line $w ≡ z$ exists.

## Partial Elements

The definition of Kan cubical sets as those having fillers for all open
boxes is all well and good, but to use this from within type theory we
need a way of reflecting the idea of "open box" as syntax. This is done
is by using the `Partial`{.Agda} type former.

The `Partial`{.Agda} type former takes two arguments: A _formula_
$\phi$, and a _type_ $A$. The idea is that a term of type
$\mathrm{Partial}\ \phi\ A$ in a context with $n$ `I`{.Agda}-typed
variables is a $n$-cube that is only defined when $\phi$ "is true". In
Agda, formulas are represented using the De Morgan structure of the
interval, and they are "true" when they are equal to 1. The predicate
`IsOne`{.Agda} represents truth of a formula, and there is a canonical
inhabitant `1=1`{.Agda} which says `i1`{.Agda} is `i1`{.Agda}.

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

More concretely, an element of `Partial`{.Agda} can be understood as a
function where the domain is the predicate `IsOne`{.Agda}, which has an
inhabitant `1=1`{.Agda}, stating that one is one. Indeed, we can _apply_
a `Partial`{.Agda} to an argument of type `IsOne`{.Agda} to get a value
of the underlying type.

```agda
  _ : notAPath i0 1=1 ≡ true
  _ = refl
```

## Extensibility

A partial element in a context with $n$-variables gives us a way of
mapping some subobject of the $n$-cube into a type. A natural question
to ask, then, is: Given a partial element $e$ of $A$, can we extend that
to a honest-to-god _element_ of $A$, which agrees with $e$ where it is
defined?

Specifically, when this is the case, we say that $x : A$ _extends_ $e :
\mathrm{Partial}\ \phi\ A$. We can depict the situation by drawing a
commutative triangle like the one below, with $\phi$ representing the
subobject of the $n$-cube of shape $\phi$.

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

In Agda, extensions are represented by the type former `Sub`{.Agda},
which we abbreviate by `_[_↦_]`{.Agda}. Fully applied, that operator
looks like `A [ φ → u ]`.

```agda
_[_↦_] : ∀ {ℓ} (A : Type ℓ) (φ : I) (u : Partial φ A) → _
A [ φ ↦ u ] = Sub A φ u
```

For instance, we can define a partial element of `Bool` - `true`{.Agda}
on the left endpoint of the interval, and undefined elsewhere, and prove
that the path `refl`{.Agda} _extends_ this to a line in `Bool`{.Agda}.

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

The notion of partial elements and extensibility captures the specific
interface of the Kan operations, which can be summed up in the following
sentence: _If a partial path is extensible at `i0`{.Agda}, then it is
extensible at `i1`{.Agda}_. Let's draw some more diagrams to connect
this with the previous concept of open box, and to see how this lets us
define path composition.

~~~{.quiver}
\[\begin{tikzcd}
  x && y \\
  \\
  w && z
  \arrow["{\mathrm{sym}\ p}"', from=1-1, to=3-1]
  \arrow["r", from=1-3, to=3-3]
\end{tikzcd}\]
~~~

The diagram above - a tube - is a partial path in $A$, which is
$\mathrm{sym} p$ on `i0`{.Agda} and $r$ on `i1`{.Agda}. We can make this
explicit by giving a construction of this as a `Partial`{.Agda} element:

```
module _ {A : Type} {w x y z : A} {p : w ≡ x} {q : x ≡ y} {r : y ≡ z} where private
  double-comp-tube : (i : I) → I → Partial (~ i ∨ i) A
  double-comp-tube i j (i = i0) = sym p j
  double-comp-tube i j (i = i1) = r j
```
This element has type `(i : I) → I → Partial (~ i ∨ i) A` rather than
`(i : I) → Partial (~ i ∨ i) (I → A)` because of a universe restriction
in Agda: The second argument to `Partial`{.Agda} must be a
`Type`{.Agda}, but `I`{.Agda} is not a `Type`{.Agda}.

When given `i0`{.Agda} as `j`, `double-comp-tube`{.Agda} has boundary
`p\ \mathrm{i1} \to r\ \mathrm{i0}`, which computes to $x \to y$. This
means that for this path to be extensible at `i0`{.Agda}, we need a path
with that boundary. By assumption, `q` extends `double-comp-tube`{.Agda}
at `i0`{.Agda}.

```
  extensible-at-i0 : (i : I) → A [ (i ∨ ~ i) ↦ double-comp-tube i i0 ]
  extensible-at-i0 i = inS (q i)
```

The Kan condition says that this path is then extensible at `i1`, i.e.
there is some inhabitant of `A [ (i ∨ ~ i) ↦ double-comp-tube i i1 ]`.
This element is written using the operator `hcomp`{.Agda}:

```
  extensible-at-i1 : (i : I) → A [ (i ∨ ~ i) ↦ double-comp-tube i i1 ]
  extensible-at-i1 i =
    inS (hcomp {φ = ~ i ∨ i} (λ k is1 → double-comp-tube i k is1) (q i))
```

Unwinding what it means for this element to exist, we see that the
`hcomp`{.Agda} operation guarantees the existence of a path $w \to z$.

```
  double-comp : w ≡ z
  double-comp i = outS (extensible-at-i1 i)
```

Note that `hcomp`{.Agda} gives us the missing face of the open box, but
the semantics guarantees the existence of the box itself, as a $n$-cube.
From the De Morgan structure on the interval, we can derive the
existence of the boxes (called **fillers**) from the existence of the
missing faces:

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

<!--
```
ghcomp : ∀ {ℓ} {A : Type ℓ} {φ : I}
       → (u : I → Partial φ A)
       → (u0 : A [ φ ↦ u i0 ])
       → A [ φ ↦ u i1 ]
ghcomp {φ = φ} u u0 =
  inS (hcomp (λ { j (φ = i1) → u j 1=1
                ; j (φ = i0) → outS u0
                })
        (outS u0))

fill : ∀ {ℓ} (A : ∀ i → Type ℓ)
       {φ : I}
       (u : ∀ i → Partial φ (A i))
       (u0 : A i0 [ φ ↦ u i0 ])
       (i : I) → A i
fill A {φ = φ} u u0 i =
  comp (λ j → A (i ∧ j))
       (λ j → λ { (φ = i1) → u (i ∧ j) 1=1
                ; (i = i0) → outS u0 })
       (outS u0)
```
-->

Given the inputs to a composition --- a family of partial paths `u` and a
base `u0` --- `hfill`{.Agda} connects the input of the composition (`u0`)
and the output. The cubical shape of iterated equalities lead to a
slight oddity: The only unbiased definition of path composition we can
give is _double composition_, which corresponds to the missing face for
the [the square] at the start of this section.

[the square]: 1Lab.Path.html#composition

```agda
_··_··_ : ∀ {ℓ} {A : Type ℓ} {w x y z : A}
        → w ≡ x → x ≡ y → y ≡ z
        → w ≡ z
(p ·· q ·· r) i =
  hcomp (λ j → λ { (i = i0) → p (~ j)
                 ; (i = i1) → r j })
        (q i)
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
  \arrow["{\mathrm{refl}}"', from=1-1, to=3-1]
  \arrow["{q}", from=1-3, to=3-3]
  \arrow["{p \bullet q}"', from=3-1, to=3-3, dashed]
\end{tikzcd}\]
~~~

```
_∙_ : ∀ {ℓ} {A : Type ℓ} {x y z : A}
    → x ≡ y → y ≡ z → x ≡ z
p ∙ q = refl ·· p ·· q
```

The composition is the missing face (the dashed line in the diagram),
but the associated box also has a filler, which turns out to be very
useful.

```agda
∙-filler : ∀ {ℓ} {A : Type ℓ} {x y z : A}
         → (p : x ≡ y) (q : y ≡ z)
         → PathP (λ i → x ≡ q i) p (p ∙ q)
∙-filler {x = x} {y} {z} p q j i =
  hfill (λ k → λ { (i = i0) → x
                 ; (i = i1) → q k })
        (inS (p i))
        j
```

The composition has a filler in the other direction, too, connecting `q`
and `p ∙ q` over `p`.

```agda
∙-filler' : ∀ {ℓ} {A : Type ℓ} {x y z : A}
          → (p : x ≡ y) (q : y ≡ z)
          → PathP (λ i → p (~ i) ≡ z) q (p ∙ q)
∙-filler' {x = x} {y} {z} p q j i =
  hcomp (λ k → λ { (i = i0) → p (~ j)
                 ; (i = i1) → q k
                 ; (j = i0) → q (i ∧ k) })
        (p (i ∨ ~ j))
```

## Equational Reasoning

When constructing long chains of equalities, it's rather helpful to be
able to visualise _what_ is being equated with more "priority" than
_how_ it is being equated. For this, a handful of combinators with weird
names are defined:

```agda
_≡⟨_⟩_ : ∀ {ℓ} {A : Type ℓ} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = p ∙ q

_≡⟨⟩_ : ∀ {ℓ} {A : Type ℓ} (x : A) {y : A} → x ≡ y → x ≡ y
x ≡⟨⟩ x≡y = x≡y

_∎ : ∀ {ℓ} {A : Type ℓ} (x : A) → x ≡ x
x ∎ = refl

infixr 30 _∙_
infixr 2 _≡⟨⟩_ _≡⟨_⟩_
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
  {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} (a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁)
  {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} (a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁)
  (a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀) (a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁)
  → Type ℓ
SquareP A a₀₋ a₁₋ a₋₀ a₋₁ = PathP (λ i → PathP (λ j → A i j) (a₋₀ i) (a₋₁ i)) a₀₋ a₁₋
```
-->

# Dependent Paths

Often, it is desirable to compare elements of types which are not
definitionally equal, but are connected by a path. We call these
"dependent paths", or "paths over paths". In the same way that a
`Path`{.Agda} can be understood as a function `I → A` with specified
endpoints, a `PathP`{.Agda} (*path* over *p*ath) can be understood as a
_dependent_ function `(i : I) → A i`.

In the Book, paths over paths are implemented in terms of the
`transport`{.Agda} operation: A path `x ≡ y` over `p` is a path
`transport p x ≡ y`, thus deriving dependent equality from the
non-dependent version. Fortunately, a cubical argument shows us that
these notions coincide:

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

There is a helper function which combines `PathP≡Path`{.Agda} and
`transport`{.Agda} to let us concisely write Book-style proofs.

```agda
transp→PathP : ∀ {ℓ} (P : I → Type ℓ) (p : P i0) (q : P i1)
             → transport (λ i → P i) p ≡ q
             → PathP P p q
transp→PathP P p q a = transport (sym (PathP≡Path P p q)) a
```

Note that, due to limitations with unification, the parameters `P`, `p`,
and `q` cannot usually be inferred from context. Thus, they are explicit arguments.

# Path Spaces

A large part of the study of HoTT is the _characterisation of path
spaces_. Given a type `A`, what does `Path A x y` look like? [Hedberg's
theorem] says that for types with decidable equality, it's boring. For
[the circle], we can prove its loop space is the integers - we have
`Path S¹ base base ≡ Int`.

[Hedberg's theorem]: 1Lab.HLevel.Sets.html
[the circle]: 1Lab.HIT.S1.html

Most of these characterisations need machinery that is not in this
module to be properly stated. Even then, we can begin to outline a few
simple cases:

## Σ Types

For `Σ`{.Agda} types, an equality between `(a , b) ≡ (x , y)` is a
non-dependent equality `p : a ≡ x`, and a path between `b` and `y`
laying over `p`.

```agda
Σ-PathP : ∀ {a b} {A : Type a} {B : A → Type b}
        → {x y : Σ B}
        → (p : x .fst ≡ y .fst)
        → PathP (λ i → B (p i)) (x .snd) (y .snd)
        → x ≡ y
Σ-PathP p q i = p i , q i
```

We can also use the book characterisation of dependent paths, which is
simpler in the case where the `Σ`{.Agda} represents a subset --- i.e.,
`B` is a family of propositions.

```agda
Σ-Path : ∀ {a b} {A : Type a} {B : A → Type b}
       → {x y : Σ B}
       → (p : x .fst ≡ y .fst)
       → subst B p (x .snd) ≡ (y .snd)
       → x ≡ y
Σ-Path {A = A} {B} {x} {y} p q =
  Σ-PathP p (transport (λ i → PathP≡Path (λ i → B (p i)) (x .snd) (y .snd) (~ i)) q)
```

## Π types

For dependent functions, the paths are _homotopies_, in the topological
sense: `Path ((x : A) → B x) f g` is the same thing as a function `I →
(x : A) → B x` - which we could turn into a product if we really wanted
to.

```agda
happly : ∀ {a b} {A : Type a} {B : A → Type b}
         {f g : (x : A) → B x}
       → f ≡ g → (x : A) → f x ≡ g x
happly p x i = p i x
```

With this, we have made definitional yet another principle which is
propositional in the HoTT book: _function extensionality_. Functions are
equal precisely if they assign the same outputs to every input.

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
right endpoint constant, in which case we get something provably equal
to composing with the inverse of the adjustment:

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

# Cartesian coercion

In Cubical Agda, the interval is given the structure of a De Morgan
algebra. This is not the only choice of structure on the interval that
gives a model of univalent type theory: We could also subject the
interval to _no_ additional structure other than what comes from the
structural rules of type theory (introducing variables, ignoring
variables, swapping variables, etc). This is a different cubical type
theory, called _Cartesian cubical type theory_.

In Cartesian cubical type theory, instead of having a `transp`{.Agda}
operation which takes $A(\mathrm{i0}) \to A(\mathrm{i1})$, there is a
“more powerful” $\mathrm{coe}^{i \to j}$ operation which takes, as the
superscript implies, $A(i) \to A(j)$. First, we introduce alternative
names for several uses of `transp`{.Agda}.

```agda
coe0→1 : ∀ {ℓ} (A : I → Type ℓ) → A i0 → A i1
coe0→1 A a = transp (λ i → A i) i0 a
-- ^ This is another name for transport

coe1→0 : ∀ {ℓ} (A : I → Type ℓ) → A i1 → A i0
coe1→0 A a = transp (λ i → A (~ i)) i0 a
-- ^ This is equivalent to transport ∘ sym
```

There are also “more exciting” operations which transport from one of
the endpoints, to a path which can vary over the interval. In a sense,
these are generalised transport fillers.

```agda
coe0→i : ∀ {ℓ} (A : I → Type ℓ) (i : I) → A i0 → A i
coe0→i A i a = transp (λ j → A (i ∧ j)) (~ i) a

coe1→i : ∀ {ℓ} (A : I → Type ℓ) (i : I) → A i1 → A i
coe1→i A i a = transp (λ j → A (i ∨ ~ j)) i a

coei→0 : ∀ {ℓ} (A : I → Type ℓ) (i : I) → A i → A i0
coei→0 A i a = transp (λ j → A (i ∧ ~ j)) (~ i) a
```

Using a filler, we can put together the `0→i` and `1→i` coercions to get
the "master coercion" operation.

```agda
coei→j : ∀ {ℓ} (A : I → Type ℓ) (i j : I) → A i → A j
coei→j A i j a =
  fill A (λ j → λ { (i = i0) → coe0→i A j a
                  ; (i = i1) → coe1→i A j a
                  })
    (inS (coei→0 A i a)) j

coei→1 : ∀ {ℓ} (A : I → Type ℓ) (i : I) → A i → A i1
coei→1 A i a = coei→j A i i1 a
```

This operation satisfies, _definitionally_, a whole host of equations:

```agda
coei0→1 : ∀ {ℓ} (A : I → Type ℓ) (a : A i0) → coei→1 A i0 a ≡ coe0→1 A a
coei0→1 A a = refl

coei1→1 : ∀ {ℓ} (A : I → Type ℓ) (a : A i1) → coei→1 A i1 a ≡ a
coei1→1 A a = refl

coei→i0 : ∀ {ℓ} (A : I → Type ℓ) (i : I) (a : A i) → coei→j A i i0 a ≡ coei→0 A i a
coei→i0 A i a = refl

coei0→i : ∀ {ℓ} (A : I → Type ℓ) (i : I) (a : A i0) → coei→j A i0 i a ≡ coe0→i A i a
coei0→i A i a = refl

coei→i1 : ∀ {ℓ} (A : I → Type ℓ) (i : I) (a : A i) → coei→j A i i1 a ≡ coei→1 A i a
coei→i1 A i a = refl

coei1→i : ∀ {ℓ} (A : I → Type ℓ) (i : I) (a : A i1) → coei→j A i1 i a ≡ coe1→i A i a
coei1→i A i a = refl
```

It is not definitional, however, that _not_ changing the endpoint is the
identity function.

```agda
coei→i : ∀ {ℓ} (A : I → Type ℓ) (i : I) (a : A i) → coei→j A i i a ≡ a
coei→i A i = coe0→i (λ i → (a : A i) → coei→j A i i a ≡ a) i (λ _ → refl)
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
```
-->
