```agda
open import 1Lab.Type

module 1Lab.Path where
```

# Paths

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

Path : {ℓ : _} (A : Type ℓ) → A → A → Type ℓ
Path A = PathP (λ i → A)
```

The type `I`{.Agda} is meant to represent the unit interval $[0,1]$, the
same unit interval used in the definition of path. Since all functions
definable in type theory are automatically continuous, we can take a
path to simply be a function `I → A`. More practically, it's useful to
write out the endpoints of the path --- that is, the values the function
takes when applied to `i0` and to `i1`. This we call a `Path`{.Agda}.

```agda
private
  toPath : {ℓ : _} {A : Type ℓ} → (f : I → A) → Path A (f i0) (f i1)
  toPath f i = f i

refl : {ℓ : _} {A : Type ℓ} {x : A} → x ≡ x
refl {x = x} = toPath (λ i → x)
```

The type `Path A x y` is also written `x ≡ y`, when `A` is not important
- i.e. when it can be inferred from `x` and `y`. The proof that equality
is reflexive is given by a `Path`{.Agda} which yields the same element
everywhere on `I`: The constant function.

The endpoints of a path --- even a path we do not know the definition of -
are equal, by computation, to the ones specified in its type.

```agda
module _ {ℓ : _} {A : Type ℓ} {x y : A} {p : x ≡ y} where
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
[_paths_], which represent simple equalities between terms of that type.

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
module _ {ℓ : _} {A : Type ℓ} {a b : A} {p : Path A a b} where
```

The first thing we can do is introduce another interval variable, and
just ignore it, varying the path over the non-ignored variable. These
give us squares where either the top/bottom or left/right faces are the
path `p`, and the other two are refl.

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
sym : {ℓ₁ : _} {A : Type ℓ₁} {x y : A}
    → x ≡ y → y ≡ x
sym p i = p (~ i)
```

As a minor improvement over "Book HoTT", this operation is
_definitionally_ involutive:

```agda
module _ {ℓ : _} {A : Type ℓ} {x y : A} {p : x ≡ y} where
  private
    sym-invol : sym (sym p) ≡ p
    sym-invol i = p
```

## Substitution

A basic principle of equality is that, if `x ≡ y`, then any predicate
that is true of `x` is true of `y`. In type theory, this is extended:
Any _construction_ done to an element `x` can be transported to a
construction done on `y`.

```agda
subst : {ℓ₁ ℓ₂ : _} {A : Type ℓ₁} (P : A → Type ℓ₂) {x y : A}
      → x ≡ y → P x → P y
subst P p x = transp (λ i → P (p i)) i0 x
```

Furthermore, this operation is "_uniform_": There is always a path
connecting `x` and `subst P p x`. However, these terms have different
types! One's an inhabitant of the left endpoint --- that's `P (p i0)`,
which computes to `P x` --- and the other's in `P y`. That's why we
have, rather than a `Path`{.Agda}, a `PathP`{.Agda}: A **Path** over a
**P**ath.

```agda
subst-filler : {ℓ₁ ℓ₂ : _} {A : Type ℓ₁} (P : A → Type ℓ₂) {x y : A}
             → (p : x ≡ y) (x : P x)
             → PathP (λ i → P (p i)) x (subst P p x)
subst-filler P p x i = transp (λ j → P (p (i ∧ j))) (~ i) x
```

It's called a filler because it's the _inside_ --- the space that fills -
a cube. Specifically, it can be pictured as in this diagram:

~~~{.quiver .short-1}
\[\begin{tikzcd}
  x &&& {\text{subst}(P,p,x)}
  \arrow["{\text{subst-filler}(P,p,x)}", from=1-1, to=1-4]
\end{tikzcd}\]
~~~

```agda
transport : {ℓ : _} {A B : Type ℓ} → A ≡ B → A → B
transport = subst (λ x → x)

transport-filler : {ℓ : _} {A B : Type ℓ}
                 → (p : A ≡ B) (x : A)
                 → PathP (λ i → p i) x (transport p x)
transport-filler = subst-filler (λ x → x)

transport-refl : {ℓ : _} {A : Type ℓ} (x : A)
               → transport (λ i → A) x ≡ x
transport-refl {A = A} x i = transp (λ _ → A) i x
```

Substitution where `P` is taken to be the identity function is called
`transport`{.Agda}, since it's very common. In that case, we're
_transporting_ inhabitants between provably equal types.

## Transitivity

In Cubical Agda, types are interpreted as objects called _cubical Kan
complexes_. I wrote a blog post explaining them [here]. The gist of it
is that, just like we did above and drew a path as a _line_, we can draw
iterated paths as _squares_. In a type, any _open box_ we can draw has a
_lid_, that is, the dashed path in the diagram below.

[here]: https://abby.how/posts/cubical-sets.html

<figure>
<div class=mathpar>

~~~{.quiver}
\[\begin{tikzcd}
  x & y \\
  w & z
  \arrow[from=1-1, to=2-1]
  \arrow[""{name=1, anchor=center, inner sep=0}, from=1-1, to=1-2]
  \arrow[from=1-2, to=2-2]
\end{tikzcd}\]
~~~

~~~{.quiver}
\[\begin{tikzcd}
  x & y \\
  w & z
  \arrow[""{name=0, anchor=center, inner sep=0}, dashed, from=2-1, to=2-2]
  \arrow[from=1-1, to=2-1]
  \arrow[""{name=1, anchor=center, inner sep=0}, from=1-1, to=1-2]
  \arrow[from=1-2, to=2-2]
  \arrow[shorten <=4pt, shorten >=4pt, Rightarrow, from=1, to=0]
\end{tikzcd}\]
~~~

</div>
<figcaption style="text-align: center;">
Please don't mind how the _lid_ of the box is drawn on the bottom.
</figcaption>
</figure>

Because of the De Morgan algebra structure on the interval type, we can
extend any lid to a _`filler`{.Agda ident=hfill}_ for the open box --- an
inside. This is the `hfill`{.Agda} operation, defined below. The
definition is not enlightening, so pay attention mainly to the type:

```agda
_[_↦_] : ∀ {ℓ} (A : Type ℓ) (φ : I) (u : Partial φ A) → _
A [ φ ↦ u ] = Sub A φ u

hfill : {ℓ : _} {A : Type ℓ} {φ : I}
        (u : I → Partial φ A)
        (u0 : A [ φ ↦ u i0 ])
      → Path A (outS u0) (hcomp u (outS u0))
hfill {φ = φ} u u0 i =
  hcomp (λ j → λ { (φ = i1) → u (i ∧ j) 1=1
                 ; (i = i0) → outS u0 })
        (outS u0)
```

Given the inputs to a composition --- a family of partial paths `u` and a
base `u0` --- `hfill`{.Agda} connects the input of the composition (`u0`)
and the output.

The cubical shape of iterated equalities lead to a slight oddity: The
only unbiased definition of path composition we can give is _double
composition_, which corresponds to the lid for the [the square] at the
start of this section.

[the square]: 1Lab.Path.html#transitivity

```agda
_··_··_ : {ℓ : _} {A : Type ℓ} {w x y z : A}
        → w ≡ x → x ≡ y → y ≡ z
        → w ≡ z
(p ·· q ·· r) i =
  hcomp (λ j → λ { (i = i0) → p (~ j)
                 ; (i = i1) → r j })
        (q i)
```

We can define the ordinary, single composition by taking `p = refl`, as
is done below. The figure in <span style="background-color: #eee">`#eee`
background</span> is a diagram illustrating the composition. A big part
of understanding cubical type theory is being able to make diagrams like
this, so don't skip over it!

<div class=mathpar>

<div>
```
_∙_ : {ℓ : _} {A : Type ℓ} {x y z : A}
    → x ≡ y → y ≡ z → x ≡ z
p ∙ q = refl ·· p ·· q
```

The composition is the lid, but the associated box also has a filler:

```agda
∙-filler : {ℓ : _} {A : Type ℓ} {x y z : A}
         → (p : x ≡ y) (q : y ≡ z)
         → PathP (λ i → x ≡ q i) p (p ∙ q)
∙-filler {x = x} {y} {z} p q j i =
  hfill (λ k → λ { (i = i0) → x
                 ; (i = i1) → q k })
        (inS (p i))
        j
```
</div>

<figure>
~~~{.quiver}
\[\begin{tikzcd}[background color=eee]
  x & y \\
  x & z
  \arrow[""{name=0, anchor=center, inner sep=0}, "{p \bullet q}"', dashed, from=2-1, to=2-2]
  \arrow["{\mathrm{refl}}"', from=1-1, to=2-1]
  \arrow[""{name=1, anchor=center, inner sep=0}, "p", from=1-1, to=1-2]
  \arrow["q", from=1-2, to=2-2]
  \arrow[shorten <=4pt, shorten >=4pt, Rightarrow, from=1, to=0]
\end{tikzcd}\]
~~~
<figcaption>

In the diagram, the faces represent the paths involved. The double arrow
represents the `filler`{.Agda ident="∙-filler"} of the square, that is,
the path connecting `p` and `p ∙ q`.

</figcaption>
</figure>

</div>

The composition has a filler in the other direction, too, connecting `q`
and `p ∙ q` over `p`.

```agda
∙-filler' : {ℓ : _} {A : Type ℓ} {x y z : A}
          → (p : x ≡ y) (q : y ≡ z)
          → PathP (λ i → p (~ i) ≡ z) q (p ∙ q)
∙-filler' {x = x} {y} {z} p q j i =
  hcomp (λ k → λ { (i = i0) → p (~ j)
                 ; (i = i1) → q k
                 ; (j = i0) → q (i ∧ k) })
        (p (i ∨ ~ j))
```

## Path Elimination

Using the decomposition of J as transport + contractibility of
singletons, we can show that the Path types satisfy the same eliminator
as the equality type in "Book HoTT".

```agda
J : {ℓ₁ ℓ₂ : _} {A : Type ℓ₁} {x : A}
    (P : (y : A) → x ≡ y → Type ℓ₂)
  → P x refl
  → {y : A} (p : x ≡ y)
  → P y p
J P prefl p = transport (λ i → P (p i) (λ j → p (i ∧ j))) prefl
```

This eliminator _doesn't_ definitionally compute to `prefl` when `p` is
`refl`, due to a "problem" in cubical type theory called _regularity_.
However, since it _is_ a transport, we can use the
`transport-filler`{.Agda} to get a path expressing the computation rule.

```agda
JRefl : {ℓ₁ ℓ₂ : _} {A : Type ℓ₁} {x : A}
        (P : (y : A) → x ≡ y → Type ℓ₂)
      → (pxr : P x refl)
      → J P pxr refl ≡ pxr
JRefl {x = x} P prefl i = transport-filler (λ i → P _ (λ j → x)) prefl (~ i)
```

Another way of stating J is as the fact that _singletons are contractible_:

```agda
Singleton : {ℓ : _} {A : Type ℓ} → A → Type _
Singleton x = Σ[ y ∈ _ ] (x ≡ y)

isContr-Singleton : {ℓ : _} {A : Type ℓ} {x : A} (y : Singleton x)
                  → Path (Singleton x) (x , refl) y
isContr-Singleton (_ , p) i = p i , λ j → p (i ∧ j)
```


## The Action on Paths

In HoTT, every function behaves like a funct**or**, in that it has an
action on objects (the actual computational content of the function) and
an action on _morphisms_ --- how that function acts on paths. Reading
paths as equality, this is a proof that all functions preserve equality.

```agda
ap : {a b : _} {A : Type a} {B : A → Type b} (f : (x : A) → B x) {x y : A}
   → (p : x ≡ y) → PathP (λ i → B (p i)) (f x) (f y)
ap f p i = f (p i)

ap₂ : {a b c : _} {A : Type a} {B : A → Type b} {C : (x : A) → B x → Type c}
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

# Dependent Paths

In the HoTT book, we characterise paths over paths using

`transport`{.Agda}: A "path from x to y over P" is a path `transport P x
≡ y`. In cubical type theory, we have the primitive `PathP`. These
notions, fortunately, coincide!

```agda
PathP≡Path : {ℓ : _} → (P : I → Type ℓ) (p : P i0) (q : P i1) →
             PathP P p q ≡ Path (P i1) (transport (λ i → P i) p) q
PathP≡Path P p q i = PathP (λ j → P (i ∨ j)) (transport-filler (λ j → P j) p i) q
```

We can see this by substituting either `i0` or `i1` for the variable `i`.

* When `i = i0`, we have `PathP (λ j → P j) p q`, by the endpoint rule
for `transport-filler`{.Agda}.

* When `i = i1`, we have `PathP (λ j → P i1) (transport P p) q`, again
by the endpoint rule for `transport-filler`{.Agda}.

# Equational Reasoning

When constructing long chains of equalities, it's rather helpful to be
able to visualise _what_ is being equated with more "priority" than
_how_ they are being equated. For this, a handful of combinators with
weird names are defined:

```agda
_≡⟨_⟩_ : {ℓ : _} {A : Type ℓ} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = p ∙ q

_≡⟨⟩_ : {ℓ : _} {A : Type ℓ} (x : A) {y : A} → x ≡ y → x ≡ y
x ≡⟨⟩ x≡y = x≡y

_∎ : {ℓ : _} {A : Type ℓ} (x : A) → x ≡ x
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
`⟨ ⟩`) hidden; There is a button to display them, either on the sidebar
or on the top bar depending on how narrow your screen is. For your
convenience, it's here too:

<div style="display: flex; flex-direction: column; align-items: center;">
<button type="button" class="equations">
  Toggle equations
</button>
</div>

Try pressing it!

<!--
```
SquareP : {ℓ : _}
  (A : I → I → Type ℓ)
  {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} (a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁)
  {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} (a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁)
  (a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀) (a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁)
  → Type ℓ
SquareP A a₀₋ a₁₋ a₋₀ a₋₁ = PathP (λ i → PathP (λ j → A i j) (a₋₀ i) (a₋₁ i)) a₀₋ a₁₋
```
-->

# Characterisations of equality

Here we make explicit the structure of equality of some type formers.

## Dependent sums

For sigma types, an equality between `(a , b) ≡ (x , y)` is a
non-dependent equality `p : a ≡ x`, and a path between `b` and `y`
laying over `p`.

```agda
Σ-PathP : {a b : _} {A : Type a} {B : A → Type b}
        → {x y : Σ B}
        → (p : x .fst ≡ y .fst)
        → PathP (λ i → B (p i)) (x .snd) (y .snd)
        → x ≡ y
Σ-PathP p q i = p i , q i
```

We can also use the book characterisation of dependent paths, which is
simpler in the case where the `Σ`{.Agda} represents a subset --- i.e., `B`
is a family of propositions.

```agda
Σ-Path : {a b : _} {A : Type a} {B : A → Type b}
       → {x y : Σ B}
       → (p : x .fst ≡ y .fst)
       → subst B p (x .snd) ≡ (y .snd)
       → x ≡ y
Σ-Path {A = A} {B} {x} {y} p q =
  Σ-PathP p (transport (λ i → PathP≡Path (λ i → B (p i)) (x .snd) (y .snd) (~ i)) q)
```

## Dependent functions

For dependent functions, the paths are _homotopies_, in the topological
sense: `Path ((x : A) → B x) f g` is the same thing as a function `I →
(x : A) → B x` - which we could turn into a product if we really wanted
to.

```agda
happly : {a b : _} {A : Type a} {B : A → Type b}
         {f g : (x : A) → B x}
       → f ≡ g → (x : A) → f x ≡ g x
happly p x i = p i x
```

With this, we have made definitional yet another principle which is
propositional in the HoTT book: _function extensionality_. Functions are
equal precisely if they assign the same outputs to every input.

```agda
funext : {a b : _} {A : Type a} {B : A → Type b}
         {f g : (x : A) → B x}
       → ((x : A) → f x ≡ g x) → f ≡ g
funext p i x = p x i
```

Furthermore, we know (since types are groupoids, and functions are
functors) that, by analogy with 1-category theory, paths in a function
type should behave like natural transformations (because they are arrows
in a functor category). This is indeed the case:

```agda
homotopy-natural : {a b : _} {A : Type a} {B : Type b}
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
subst-path-both : {ℓ : _} {A : Type ℓ} {x y : A}
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
becomes a simple application of the [groupoid laws for types].

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
subst-path-left : {ℓ : _} {A : Type ℓ} {x y z : A}
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
we just get a respelling of composition:

```agda
subst-path-right : {ℓ : _} {A : Type ℓ} {x y z : A}
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
