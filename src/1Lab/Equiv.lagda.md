```agda
open import 1Lab.Path.Groupoid
open import 1Lab.HLevel
open import 1Lab.Path
open import 1Lab.Type

open is-contr

module 1Lab.Equiv where
```

# Equivalences

The big idea of homotopy type theory is that isomorphic types can be
identified: the [univalence axiom]. However, the notion of
`isomorphism`{.Agda ident=is-iso}, is, in a sense, not "coherent" enough
to be used in the definition. For that, we need a coherent definition of
_equivalence_, where "being an equivalence" is [a
proposition](agda://1Lab.HLevel#is-prop).

[univalence axiom]: 1Lab.Univalence.html

To be more specific, what we need for a notion of equivalence
$\id{is-equiv}(f)$ to be "coherent" is:

- Being an `isomorphism`{.Agda ident=is-iso} implies being an
`equivalence`{.Agda ident=is-equiv} ($\id{is-iso}(f) \to
\id{is-equiv}(f)$)

- Being an equivalence implies being an isomorphism ($\id{is-equiv}(f)
\to \id{is-iso}(f)$); Taken together with the first point we may
summarise: "Being an equivalence and being an isomorphism are logically
equivalent."

- Most importantly, being an equivalence _must_ be a proposition.

The notion we adopt is due to Voevodsky: An equivalence is one that has
`contractible`{.Agda ident=is-contr} `fibres`{.Agda ident=fibre}. Other
definitions are possible (e.g.: [bi-invertible maps]) --- but
contractible fibres are "privileged" in Cubical Agda because for
[glueing] to work, we need a proof that `equivalences have contractible
fibres`{.Agda ident=is-eqv'} anyway.

[bi-invertible maps]: 1Lab.Equiv.Biinv.html
[glueing]: 1Lab.Univalence.html#glue

```agda
private
  variable
    ℓ₁ ℓ₂ : Level
    A B : Type ℓ₁
```

A _homotopy fibre_, _fibre_ or _preimage_ of a function `f` at a point
`y : B` is the collection of all elements of `A` that `f` maps to `y`.
Since many choices of name are possible, we settle on the one that is
shortest and most aesthetic: `fibre`{.Agda}.

```agda
fibre : (A → B) → B → Type _
fibre f y = Σ _ λ x → f x ≡ y
```

A function `f` is an equivalence if every one of its fibres is
[contractible](agda://1Lab.HLevel#is-contr) - that is, for any element
`y` in the range, there is exactly one element in the domain which `f`
maps to `y`. Using set-theoretic language, `f` is an equivalence if the
preimage of every element of the codomain is a singleton.

```agda
record is-equiv (f : A → B) : Type (level-of A ⊔ level-of B) where
  no-eta-equality
  field
    is-eqv : (y : B) → is-contr (fibre f y)

open is-equiv public

_≃_ : ∀ {ℓ₁ ℓ₂} → Type ℓ₁ → Type ℓ₂ → Type _
_≃_ A B = Σ (A → B) is-equiv

id-equiv : is-equiv {A = A} (λ x → x)
id-equiv .is-eqv y =
  contr (y , λ i → y)
    λ { (y' , p) i → p (~ i) , λ j → p (~ i ∨ j) }
```

<!--
```
-- This helper is for functions f, g that cancel eachother, up to
-- definitional equality, without any case analysis on the argument:

strict-fibres : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f : A → B} (g : B → A) (b : B)
  → Σ[ t ∈ fibre f (f (g b)) ]
    ((t' : fibre f b) → Path (fibre f (f (g b))) t
                          (g (f (t' .fst)) , ap (f ∘ g) (t' .snd)))
strict-fibres {f = f} g b .fst = (g b , refl)
strict-fibres {f = f} g b .snd (a , p) i = (g (p (~ i)) , λ j → f (g (p (~ i ∨ j))))

-- This is more efficient than using Iso→Equiv. When f (g x) is definitionally x,
-- the type reduces to essentially is-contr (fibre f b).
```
-->

For Cubical Agda, the type of equivalences is distinguished, so we have
to make a small wrapper to match the interface Agda expects. This is the
geometric definition of contractibility, in terms of [partial elements]
and extensibility.

[partial elements]: 1Lab.Path.html#extensibility

```agda
{-# BUILTIN EQUIV _≃_ #-}
{-# BUILTIN EQUIVFUN fst #-}

is-eqv' : ∀ {a b} (A : Type a) (B : Type b)
        → (w : A ≃ B) (a : B)
        → (ψ : I)
        → (p : Partial ψ (fibre (w .fst) a))
        → fibre (w .fst) a [ ψ ↦ p ]
is-eqv' A B (f , is-equiv) a ψ u0 = inS (
  hcomp (∂ ψ) λ where
    i (ψ = i0) → c .centre
    i (ψ = i1) → c .paths (u0 1=1) i
    i (i = i0) → c .centre)
  where c = is-equiv .is-eqv a

{-# BUILTIN EQUIVPROOF is-eqv' #-}
```

<!--
```
equiv-centre : (e : A ≃ B) (y : B) → fibre (e .fst) y
equiv-centre e y = e .snd .is-eqv y .centre

equiv-path : (e : A ≃ B) (y : B) →
  (v : fibre (e .fst) y) → Path _ (equiv-centre e y) v
equiv-path e y = e .snd .is-eqv y .paths
```
-->

## is-equiv is propositional

A function can be an equivalence in at most one way. This follows from
propositions being closed under dependent products, and `is-contr`{.Agda}
being a proposition.

```agda
module _ where private
  is-equiv-is-prop : (f : A → B) → is-prop (is-equiv f)
  is-equiv-is-prop f x y i .is-eqv p = is-contr-is-prop (x .is-eqv p) (y .is-eqv p) i
```

<details>
<summary>
Even though the proof above works, we use the direct cubical proof in
this `<details>` tag (lifted from the Cubical Agda library) in the rest
of the development for efficiency concerns.
</summary>

```agda
is-equiv-is-prop : (f : A → B) → is-prop (is-equiv f)
is-equiv-is-prop f p q i .is-eqv y =
  let p2 = p .is-eqv y .paths
      q2 = q .is-eqv y .paths
  in contr (p2 (q .is-eqv y .centre) i) λ w j → hcomp (∂ i ∨ ∂ j) λ where
     k (i = i0) → p2 w j
     k (i = i1) → q2 w (j ∨ ~ k)
     k (j = i0) → p2 (q2 w (~ k)) i
     k (j = i1) → w
     k (k = i0) → p2 w (i ∨ j)
```
</details>

# Isomorphisms from equivalences

For this section, we need a definition of _isomorphism_. This is the
same as ever! An isomorphism is a function that has a two-sided inverse.
We first define what it means for a function to invert another on the
left and on the right:

```agda
is-left-inverse : (B → A) → (A → B) → Type _
is-left-inverse g f = (x : _) → g (f x) ≡ x

is-right-inverse : (B → A) → (A → B) → Type _
is-right-inverse g f = (x : _) → f (g x) ≡ x
```

A proof that a function $f$ is an isomorphism consists of a function $g$
in the other direction, together with homotopies exhibiting $g$ as a
left- and right- inverse to $f$.

```agda
record is-iso (f : A → B) : Type (level-of A ⊔ level-of B) where
  no-eta-equality
  constructor iso
  field
    inv : B → A
    rinv : is-right-inverse inv f
    linv : is-left-inverse inv f

  inverse : is-iso inv
  inv inverse = f
  rinv inverse = linv
  linv inverse = rinv

Iso : ∀ {ℓ₁ ℓ₂} → Type ℓ₁ → Type ℓ₂ → Type _
Iso A B = Σ (A → B) is-iso
```

Any function that is an equivalence is an isomorphism:

```agda
equiv→inverse : {f : A → B} → is-equiv f → B → A
equiv→inverse eqv y = eqv .is-eqv y .centre .fst

equiv→counit
  : ∀ {f : A → B} (eqv : is-equiv f) x → f (equiv→inverse eqv x) ≡ x
equiv→counit eqv y = eqv .is-eqv y .centre .snd

equiv→unit
  : ∀ {f : A → B} (eqv : is-equiv f) x → equiv→inverse eqv (f x) ≡ x
equiv→unit {f = f} eqv x i = eqv .is-eqv (f x) .paths (x , refl) i .fst

equiv→zig
  : ∀ {f : A → B} (eqv : is-equiv f) x
  → ap f (equiv→unit eqv x) ≡ equiv→counit eqv (f x)
equiv→zig {f = f} eqv x i j = hcomp (∂ i ∨ ∂ j) λ where
   k (i = i0) → f (equiv→unit eqv x j)
   k (i = i1) → equiv→counit eqv (f x) (j ∨ ~ k)
   k (j = i0) → equiv→counit eqv (f x) (i ∧ ~ k)
   k (j = i1) → f x
   k (k = i0) → eqv .is-eqv (f x) .paths (x , refl) j .snd i

equiv→zag
  : ∀ {f : A → B} (eqv : is-equiv f) x
  → ap (equiv→inverse eqv) (equiv→counit eqv x)
  ≡ equiv→unit eqv (equiv→inverse eqv x)
equiv→zag {f = f} eqv b =
  subst (λ b → ap g (ε b) ≡ η (g b)) (ε b) (helper (g b)) where
  g = equiv→inverse eqv
  ε = equiv→counit eqv
  η = equiv→unit eqv

  helper : ∀ a → ap g (ε (f a)) ≡ η (g (f a))
  helper a i j = hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → g (ε (f a) (j ∨ ~ k))
    k (i = i1) → η (η a (~ k)) j
    k (j = i0) → g (equiv→zig eqv a (~ i) (~ k))
    k (j = i1) → η a (i ∧ ~ k)
    k (k = i0) → η a (i ∧ j)

is-equiv→is-iso : {f : A → B} → is-equiv f → is-iso f
is-iso.inv (is-equiv→is-iso eqv) = equiv→inverse eqv
```

We can get an element of `x` from the proof that `f` is an equivalence -
it's the point of `A` mapped to `y`, which we get from centre of
contraction for the fibres of `f` over `y`.

```agda
is-iso.rinv (is-equiv→is-iso eqv) y =
  eqv .is-eqv y .centre .snd
```

Similarly, that one fibre gives us a proof that the function above is a
right inverse to `f`.

```agda
is-iso.linv (is-equiv→is-iso {f = f} eqv) x i =
  eqv .is-eqv (f x) .paths (x , refl) i .fst
```

The proof that the function is a _left_ inverse comes from the fibres of
`f` over `y` being contractible. Since we have a fibre - namely, `f`
maps `x` to `f x` by `refl`{.Agda} - we can get any other we want!

# Equivalences from isomorphisms

Any isomorphism can be upgraded into an equivalence, in a way that
preserves the function $f$, its inverse $g$, _and_ the proof $s$ that
$g$ is a right inverse to $f$. We can not preserve _everything_, though,
as is usual when making something "more coherent". Furthermore, if
everything was preserved, `is-iso`{.Agda} would be a proposition, and
this is [provably not the case].

[provably not the case]: 1Lab.Counterexamples.IsIso.html

The argument presented here is done directly in cubical style, but a
less direct proof is also available, by showing that every isomorphism
is a [half-adjoint equivalence], and that half-adjoint equivalences have
contractible fibres.

[half-adjoint equivalence]: 1Lab.Equiv.HalfAdjoint.html

```agda
module _ {f : A → B} (i : is-iso f) where

  open is-iso i renaming ( inv to g
                         ; rinv to s
                         ; linv to t
                         )
```

Suppose, then, that $f : A \to B$ and $g : B \to A$, and we're given
witnesses $s : f (g\ x) = x$ and $t : g (f\ x) = x$ (named for
**s**ection and re**t**raction) that $f$ and $g$ are inverses. We want
to show that, for any $y$, the `fibre`{.Agda} of $f$ over $y$ is
contractible. It suffices to show that the fibre is propositional, and
that it is inhabited.

<!--
```agda
  _ = PathP
```
-->

We begin with showing that the fibre over $y$ is propositional, since
that's the harder of the two arguments. Suppose that we have $y$, $x_0$,
$x_1$, $p_0$ and $p_1$ as below; Note that $(x_0, p_0)$ and $(x_1, p_1)$
are fibres of $f$ over $y$. What we need to show is that we have some
$\pi : x_0 ≡ x_1$ and $p_0 ≡ p_1$ _`over`{.Agda ident=PathP}_ $\pi$.

```agda
  private module _ (y : B) (x0 x1 : A) (p0 : f x0 ≡ y) (p1 : f x1 ≡ y) where
```

As an intermediate step in proving that $p_0 ≡ p_1$, we _must_ show that
$x_0 ≡ x_1$ - without this, we can't even _state_ that $p_0$ and $p_1$
are identified, since they live in different types!  To this end, we
will build $\pi : p_0 ≡ p_1$, parts of which will be required to
assemble the overall proof that $p_0 ≡ p_1$.

We'll detail the construction of $\pi_0$; for $\pi_1$, the same method
is used. We want to construct a _line_, which we can do by exhibiting
that line as the missing face in a _square_. We have equations $g\ y ≡
g\ y$ (`refl`{.Agda}), $g\ (f\ x_0) ≡ g\ y$ (the action of `g` on `p0`),
and $g\ (f\ x_0) = x_0$ by the assumption that $g$ is a right inverse to
$f$.  Diagramatically, these fit together into a square:

~~~{.quiver}
\[\begin{tikzcd}
  {g\ y} && {g\ (f\ x_0)} \\
  \\
  {g\ y} && {x_0}
  \arrow["{g\ y}"', from=1-1, to=3-1]
  \arrow["{t\ x_0\ k}", from=1-3, to=3-3]
  \arrow[""{name=0, anchor=center, inner sep=0}, "{g\ (p_0\ \neg i)}", from=1-1, to=1-3]
  \arrow[""{name=1, anchor=center, inner sep=0}, "{\pi_0}"', dashed, from=3-1, to=3-3]
  \arrow["{\theta_0}"{description}, Rightarrow, draw=none, from=0, to=1]
\end{tikzcd}\]
~~~

The missing line in this square is $\pi_0$. Since the _inside_ (the
`filler`{.Agda ident=hfill}) will be useful to us later, we also give it
a name: $\theta$.

```agda
    π₀ : g y ≡ x0
    π₀ i = hcomp (∂ i) λ where
      k (i = i0) → g y
      k (i = i1) → t x0 k
      k (k = i0) → g (p0 (~ i))

    θ₀ : Square (ap g (sym p0)) refl (t x0) π₀
    θ₀ i j = hfill (∂ i) j λ where
      k (i = i0) → g y
      k (i = i1) → t x0 k
      k (k = i0) → g (p0 (~ i))
```

Since the construction of $\pi_1$ is analogous, I'll simply present the
square. We correspondingly name the missing face $\pi_1$ and the filler
$\theta_1$.

<div class=mathpar>

~~~{.quiver}
\[\begin{tikzcd}
  {g\ y} && {g\ (f\ x_1)} \\
  \\
  {g\ y} && {x_1}
  \arrow["{g\ y}"', from=1-1, to=3-1]
  \arrow["{t\ x_1\ k}", from=1-3, to=3-3]
  \arrow[""{name=0, anchor=center, inner sep=0}, "{g\ (p_1\ \neg i)}", from=1-1, to=1-3]
  \arrow[""{name=1, anchor=center, inner sep=0}, "{\pi_1}"', dashed, from=3-1, to=3-3]
  \arrow["{\theta_1}"{description}, Rightarrow, draw=none, from=0, to=1]
\end{tikzcd}\]
~~~

```agda
    π₁ : g y ≡ x1
    π₁ i = hcomp (∂ i) λ where
      j (i = i0) → g y
      j (i = i1) → t x1 j
      j (j = i0) → g (p1 (~ i))

    θ₁ : Square (ap g (sym p1)) refl (t x1) π₁
    θ₁ i j = hfill (∂ i) j λ where
      j (i = i0) → g y
      j (i = i1) → t x1 j
      j (j = i0) → g (p1 (~ i))
```
</div>

Joining these paths by their common $g\ y$ face, we obtain $\pi : x_0 ≡
x_1$. This square _also_ has a filler, connecting $\pi_0$ and $\pi_1$
over the line $g\ y ≡ \pi\ i$.

<div class=mathpar>
~~~{.quiver}
\[\begin{tikzcd}
  {g\ y} && {g\ y} \\
  \\
  {x_0} && {x_1}
  \arrow[""{name=0, anchor=center, inner sep=0}, "{g\ y}", from=1-1, to=1-3]
  \arrow["{\pi_0}\ k"', from=1-1, to=3-1]
  \arrow[""{name=1, anchor=center, inner sep=0}, "\pi"', dashed, from=3-1, to=3-3]
  \arrow["{\pi_1}\ k", from=1-3, to=3-3]
  \arrow["\theta"{description}, Rightarrow, draw=none, from=0, to=1]
\end{tikzcd}\]
~~~

```agda
    π : x0 ≡ x1
    π i = hcomp (∂ i) λ where
      j (j = i0) → g y
      j (i = i0) → π₀ j
      j (i = i1) → π₁ j
```
</div>

This concludes the construction of $\pi$, and thus, the 2D part of the
proof. Now, we want to show that $p_0 ≡ p_1$ over a path induced by
$\pi$. This is a _square_ with a specific boundary, which can be built
by constructing an appropriate _open cube_, where the missing face is
that square. As an intermediate step, we define $\theta$ to be the
filler for the square above.

```agda
    θ : Square refl π₀ π₁ π
    θ i j = hfill (∂ i) j λ where
      k (i = i1) → π₁ k
      k (i = i0) → π₀ k
      k (k = i0) → g y
```

Observe that we can coherently alter $\theta$ to get $\iota$ below,
which expresses that $\id{ap}\ g\ p_0$ and $\id{ap}\ g\ p_1$ are
identified.

```agda
    ι : Square (ap (g ∘ f) π) (ap g p0) (ap g p1) refl
    ι i j = hcomp (∂ i ∨ ∂ j) λ where
      k (k = i0) → θ i (~ j)
      k (i = i0) → θ₀ (~ j) (~ k)
      k (i = i1) → θ₁ (~ j) (~ k)
      k (j = i0) → t (π i) (~ k)
      k (j = i1) → g y
```

This composition can be visualised as the _red_ (front) face in the
diagram below. The back face is $\theta\ i\ (\neg\ j)$, i.e. `(θ i (~
j))` in the code. Similarly, the $j = \id{i1}$ (bottom) face is `g y`,
the $j = \id{i0}$ (top) face is `t (π i) (~ k)`, and similarly for $i =
\id{i0}$ (left) and $i = \id{i1}$ (right).

~~~{.quiver .tall-2}
\[\begin{tikzcd}
  \textcolor{rgb,255:red,214;green,92;blue,92}{g\ (f\ (g\ x_0))} &&&& \textcolor{rgb,255:red,214;green,92;blue,92}{g\ (f\ (g\ x_1))} \\
  & \textcolor{rgb,255:red,92;green,92;blue,214}{x_0} && \textcolor{rgb,255:red,92;green,92;blue,214}{x_1} \\
  \\
  & \textcolor{rgb,255:red,92;green,92;blue,214}{g\ y} && \textcolor{rgb,255:red,92;green,92;blue,214}{g\ y} \\
  \textcolor{rgb,255:red,214;green,92;blue,92}{g\ y} &&&& \textcolor{rgb,255:red,214;green,92;blue,92}{g\ y}
  \arrow[""{name=0, anchor=center, inner sep=0}, "\pi"', color={rgb,255:red,92;green,92;blue,214}, from=2-2, to=2-4]
  \arrow[""{name=1, anchor=center, inner sep=0}, "{g\ y}", color={rgb,255:red,92;green,92;blue,214}, from=4-2, to=4-4]
  \arrow[""{name=2, anchor=center, inner sep=0}, "{\pi_0}", color={rgb,255:red,92;green,92;blue,214}, from=2-2, to=4-2]
  \arrow[""{name=3, anchor=center, inner sep=0}, "{\pi_1}"', color={rgb,255:red,92;green,92;blue,214}, from=2-4, to=4-4]
  \arrow[from=4-4, to=5-5]
  \arrow[""{name=4, anchor=center, inner sep=0}, "{\id{ap}\ (g \circ f)\ \pi}", color={rgb,255:red,214;green,92;blue,92}, from=1-1, to=1-5]
  \arrow[""{name=5, anchor=center, inner sep=0}, "{g\ y}"', color={rgb,255:red,214;green,92;blue,92}, from=5-1, to=5-5]
  \arrow[from=2-4, to=1-5]
  \arrow[""{name=6, anchor=center, inner sep=0}, "{\id{ap}\ g\ p_1}", color={rgb,255:red,214;green,92;blue,92}, from=1-5, to=5-5]
  \arrow[""{name=7, anchor=center, inner sep=0}, "{\id{ap}\ g\ p_0}"', color={rgb,255:red,214;green,92;blue,92}, from=1-1, to=5-1]
  \arrow[from=2-2, to=1-1]
  \arrow[from=4-2, to=5-1]
  \arrow["{\theta\ i\ (\neg\ j)}"{description}, color={rgb,255:red,92;green,92;blue,214}, Rightarrow, draw=none, from=1, to=0]
  \arrow["{t\ (\pi\ i)\ (\neg\ k)}"{description}, Rightarrow, draw=none, from=0, to=4]
  \arrow["{\theta_0(\neg j)(\neg k)}"{description}, Rightarrow, draw=none, from=2, to=7]
  \arrow["{g\ y}"{description}, Rightarrow, draw=none, from=1, to=5]
  \arrow["{\theta_1(\neg j)(\neg k)}"{description}, Rightarrow, draw=none, from=3, to=6]
\end{tikzcd}\]
~~~

The fact that $j$ only appears as $\neg j$ can be understood as the
diagram above being _upside-down_. Indeed, $\pi_0$ and $\pi_1$ in the
boundary of $\theta$ (the inner, blue face) are inverted when their
types are considered. We're in the home stretch: Using our assumption $s
: f (g\ x) = x$, we can cancel all of the $f \circ g$s in the diagram
above to get what we wanted: $p_0 ≡ p_1$.

```agda
    sq1 : Square (ap f π) p0 p1 refl
    sq1 i j = hcomp (∂ i ∨ ∂ j) λ where
       k (i = i0) → s (p0 j) k
       k (i = i1) → s (p1 j) k
       k (j = i0) → s (f (π i)) k
       k (j = i1) → s y k
       k (k = i0) → f (ι i j)
```

The composition above can be visualised as the front (red) face in the
cubical diagram below. Once more, left is $i = \id{i0}$, right is $i =
\id{i1}$, up is $j = \id{i0}$, and down is $j = \id{i1}$.

~~~{.quiver .tall-2}
\small
\[\begin{tikzcd}
  \textcolor{rgb,255:red,214;green,92;blue,92}{f(x_0)} &&&& \textcolor{rgb,255:red,214;green,92;blue,92}{f(x_1)} \\
  & \textcolor{rgb,255:red,92;green,92;blue,214}{f(g(f(g\ x_0)))} && \textcolor{rgb,255:red,92;green,92;blue,214}{f(g(f(g\ x_1)))} \\
  && \textcolor{rgb,255:red,92;green,92;blue,214}{f\ (\iota\ i\ j)} \\
  & \textcolor{rgb,255:red,92;green,92;blue,214}{f\ (g\ y)} && \textcolor{rgb,255:red,92;green,92;blue,214}{f\ (g\ y)} \\
  \textcolor{rgb,255:red,214;green,92;blue,92}{y} &&&& \textcolor{rgb,255:red,214;green,92;blue,92}{y}
  \arrow[""{name=0, anchor=center, inner sep=0}, "{p_1}", from=1-5, to=5-5]
  \arrow[""{name=1, anchor=center, inner sep=0}, "{\id{ap}\ f\ \pi}", color={rgb,255:red,214;green,92;blue,92}, from=1-1, to=1-5]
  \arrow[""{name=2, anchor=center, inner sep=0}, "{p_0}"', color={rgb,255:red,214;green,92;blue,92}, from=1-1, to=5-1]
  \arrow[""{name=3, anchor=center, inner sep=0}, "y"', color={rgb,255:red,214;green,92;blue,92}, from=5-1, to=5-5]
  \arrow[""{name=4, anchor=center, inner sep=0}, "{\id{ap}\ (f \circ g\circ f)\ \pi}"', color={rgb,255:red,92;green,92;blue,214}, from=2-2, to=2-4]
  \arrow[""{name=5, anchor=center, inner sep=0}, "{f(g\ y)}", color={rgb,255:red,92;green,92;blue,214}, from=4-2, to=4-4]
  \arrow[""{name=6, anchor=center, inner sep=0}, "{\id{ap}\ f\ p_1}"', color={rgb,255:red,92;green,92;blue,214}, from=2-4, to=4-4]
  \arrow[""{name=7, anchor=center, inner sep=0}, "{\id{ap}\ f\ p_0}", color={rgb,255:red,92;green,92;blue,214}, from=2-2, to=4-2]
  \arrow[from=2-2, to=1-1]
  \arrow[from=2-4, to=1-5]
  \arrow[from=4-4, to=5-5]
  \arrow[from=4-2, to=5-1]
  \arrow["{s\ y\ k}"{description}, Rightarrow, draw=none, from=5, to=3]
  \arrow["{s\ (f\ (\pi\ i))\ k}"{description}, Rightarrow, draw=none, from=4, to=1]
  \arrow["{s\ (p1\ j)\ k}"{description}, Rightarrow, draw=none, from=6, to=0]
  \arrow["{s\ (p0\ j)\ k}"{description}, Rightarrow, draw=none, from=7, to=2]
\end{tikzcd}\]
~~~

Putting all of this together, we get that $(x_0, p_0) ≡ (x_1, p_1)$.
Since there were no assumptions on any of the variables under
consideration, this indeed says that the fibre over $y$ is a proposition
for any choice of $y$.

```agda
    is-iso→fibre-is-prop : (x0 , p0) ≡ (x1 , p1)
    is-iso→fibre-is-prop i .fst = π i
    is-iso→fibre-is-prop i .snd = sq1 i
```

Since the fibre over $y$ is inhabited by $(g\ y, s\ y)$, we get that any
isomorphism has contractible fibres:

```agda
  is-iso→is-equiv : is-equiv f
  is-iso→is-equiv .is-eqv y .centre .fst = g y
  is-iso→is-equiv .is-eqv y .centre .snd = s y
  is-iso→is-equiv .is-eqv y .paths z =
    is-iso→fibre-is-prop y (g y) (fst z) (s y) (snd z)
```

Applying this to the `Iso`{.Agda} and `_≃_`{.Agda} pairs, we can turn
any isomorphism into a coherent equivalence.

```agda
Iso→Equiv : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂}
          → Iso A B
          → A ≃ B
Iso→Equiv (f , is-iso) = f , is-iso→is-equiv is-iso
```

A helpful lemma: Any function between contractible types is an equivalence:

```agda
is-contr→is-equiv : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂}
                  → is-contr A → is-contr B → {f : A → B}
                  → is-equiv f
is-contr→is-equiv cA cB = is-iso→is-equiv f-is-iso where
  f-is-iso : is-iso _
  is-iso.inv f-is-iso _ = cA .centre
  is-iso.rinv f-is-iso _ = is-contr→is-prop cB _ _
  is-iso.linv f-is-iso _ = is-contr→is-prop cA _ _

is-contr→≃ : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂}
           → is-contr A → is-contr B → A ≃ B
is-contr→≃ cA cB = (λ _ → cB .centre) , is-iso→is-equiv f-is-iso where
  f-is-iso : is-iso _
  is-iso.inv f-is-iso _ = cA .centre
  is-iso.rinv f-is-iso _ = is-contr→is-prop cB _ _
  is-iso.linv f-is-iso _ = is-contr→is-prop cA _ _
```

# Equivalence Reasoning

To make composing equivalences more intuitive, we implement operators to
do equivalence reasoning in the same style as equational reasoning.

```agda
_∙e_ : ∀ {ℓ ℓ₁ ℓ₂} {A : Type ℓ} {B : Type ℓ₁} {C : Type ℓ₂}
     → A ≃ B → B ≃ C → A ≃ C

_e⁻¹ : ∀ {ℓ ℓ₁} {A : Type ℓ} {B : Type ℓ₁}
     → A ≃ B → B ≃ A
_e⁻¹ eqv = Iso→Equiv ( equiv→inverse (eqv .snd)
                     , record { inv  = eqv .fst
                              ; rinv = equiv→unit (eqv .snd)
                              ; linv = equiv→counit (eqv .snd)
                              })
```
<!--
```
_∙e_ (f , e) (g , e') = (λ x → g (f x)) , eqv where
  g⁻¹ : is-iso g
  g⁻¹ = is-equiv→is-iso e'

  f⁻¹ : is-iso f
  f⁻¹ = is-equiv→is-iso e

  inv : _ → _
  inv x = f⁻¹ .is-iso.inv (g⁻¹ .is-iso.inv x)

  abstract
    right : is-right-inverse inv (λ x → g (f x))
    right z =
      g (f (f⁻¹ .is-iso.inv (g⁻¹ .is-iso.inv z))) ≡⟨ ap g (f⁻¹ .is-iso.rinv _) ⟩
      g (g⁻¹ .is-iso.inv z)                       ≡⟨ g⁻¹ .is-iso.rinv _ ⟩
      z                                           ∎

    left : is-left-inverse inv (λ x → g (f x))
    left z =
      f⁻¹ .is-iso.inv (g⁻¹ .is-iso.inv (g (f z))) ≡⟨ ap (f⁻¹ .is-iso.inv) (g⁻¹ .is-iso.linv _) ⟩
      f⁻¹ .is-iso.inv (f z)                       ≡⟨ f⁻¹ .is-iso.linv _ ⟩
      z                                           ∎
  eqv : is-equiv (λ x → g (f x))
  eqv = is-iso→is-equiv (iso (λ x → f⁻¹ .is-iso.inv (g⁻¹ .is-iso.inv x)) right left)

∙-is-equiv : ∀ {ℓ ℓ₁ ℓ₂} {A : Type ℓ} {B : Type ℓ₁} {C : Type ℓ₂}
           → {f : A → B} {g : B → C}
           → is-equiv f
           → is-equiv g
           → is-equiv (λ x → g (f x))
∙-is-equiv {f = f} {g = g} e e' = ((f , e) ∙e (g , e')) .snd

module Equiv {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′} (f : A ≃ B) where
  to = f .fst
  from = equiv→inverse (f .snd)
  η = equiv→unit (f .snd)
  ε = equiv→counit (f .snd)
  zig = equiv→zig (f .snd)
  zag = equiv→zag (f .snd)

  injective : ∀ {x y} → to x ≡ to y → x ≡ y
  injective p = ap fst $ is-contr→is-prop (f .snd .is-eqv _) (_ , refl) (_ , sym p)

  injective₂ : ∀ {x y z} → to x ≡ z → to y ≡ z → x ≡ y
  injective₂ p q = ap fst $ is-contr→is-prop (f .snd .is-eqv _)
    (_ , p) (_ , q)
```
-->

The proofs that equivalences are closed under composition assemble
nicely into transitivity operators resembling equational reasoning:

```agda
_≃⟨_⟩_ : ∀ {ℓ ℓ₁ ℓ₂} (A : Type ℓ) {B : Type ℓ₁} {C : Type ℓ₂}
       → A ≃ B → B ≃ C → A ≃ C
A ≃⟨ f ⟩ g = f ∙e g

_≃⟨⟩_ : ∀ {ℓ ℓ₁} (A : Type ℓ) {B : Type ℓ₁} → A ≃ B → A ≃ B
x ≃⟨⟩ x≡y = x≡y

_≃∎ : ∀ {ℓ} (A : Type ℓ) → A ≃ A
x ≃∎ = _ , id-equiv

infixr 30 _∙e_
infixr 2 _≃⟨⟩_ _≃⟨_⟩_
infix  3 _≃∎
```

# Propositional Extensionality

The following observation is not very complex, but it is incredibly
useful: Equivalence of propositions is the same as biimplication.

```agda
prop-ext : ∀ {ℓ ℓ'} {P : Type ℓ} {Q : Type ℓ'}
         → is-prop P → is-prop Q
         → (P → Q) → (Q → P)
         → P ≃ Q
prop-ext pprop qprop p→q q→p .fst = p→q
prop-ext pprop qprop p→q q→p .snd .is-eqv y .centre = q→p y , qprop _ _
prop-ext pprop qprop p→q q→p .snd .is-eqv y .paths (p' , path) =
  Σ-path (pprop _ _) (is-prop→is-set qprop _ _ _ _)
```

<!--
```agda
sym-equiv : ∀ {ℓ} {A : Type ℓ} {x y : A} → (x ≡ y) ≃ (y ≡ x)
sym-equiv = sym , is-iso→is-equiv (iso sym (λ _ → refl) (λ _ → refl))
```
-->
