```agda
open import 1Lab.HLevel
open import 1Lab.Path
open import 1Lab.Type

open isContr

module 1Lab.Equiv where
```

# Equivalences

The big idea of homotopy type theory is that isomorphic types can be
identified: the [univalence axiom]. However, the notion of
`isomorphism`{.Agda ident=isIso}, is, in a sense, not "coherent" enough
to be used in the definition. For that, we need a coherent definition of
_equivalence_, where "being an equivalence" is [a
proposition](agda://1Lab.HLevel#isProp).

[univalence axiom]: 1Lab.Univalence.html

To be more specific, what we need for a notion of equivalence
$\mathrm{isEquiv}(f)$ to be "coherent" is:

- Being an `isomorphism`{.Agda ident=isIso} implies being an
`equivalence`{.Agda ident=isEquiv} ($\mathrm{isIso}(f) \to
\mathrm{isEquiv}(f)$)

- Being an equivalence implies being an isomorphism
($\mathrm{isEquiv}(f) \to \mathrm{isIso}(f)$); Taken together with the
first point we may summarise: "Being an equivalence and being an
isomorphism are logically equivalent."

- Most importantly, being an equivalence _must_ be a proposition.

The notion we adopt is due to Voevodsky: An equivalence is one that has
`contractible`{.Agda ident=isContr} `fibres`{.Agda ident=fibre}. Other
definitions are possible (e.g.: [bi-inverible maps]) --- but
contractible fibres are "privileged" in Cubical Agda because for
[glueing] to work, we need a proof that `equivalences have contractible
fibres`{.Agda ident=isEqv'} anyway.

[bi-inverible maps]: 1Lab.Equiv.Biinv.html
[glueing]: 1Lab.Univalence.html#Glue

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
fibre f y = Σ λ x → f x ≡ y
```

A function `f` is an equivalence if every one of its fibres is
[contractible](agda://1Lab.HLevel#isContr) - that is, for any element
`y` in the range, there is exactly one element in the domain which `f`
maps to `y`. Using set-theoretic language, `f` is an equivalence if the
preimage of every element of the codomain is a singleton.

```agda
record isEquiv (f : A → B) : Type (level-of A ⊔ level-of B) where
  no-eta-equality
  field
    isEqv : (y : B) → isContr (fibre f y)

open isEquiv public

_≃_ : ∀ {ℓ₁ ℓ₂} → Type ℓ₁ → Type ℓ₂ → Type _
_≃_ A B = Σ (isEquiv {A = A} {B = B})

idEquiv : isEquiv {A = A} (λ x → x)
idEquiv .isEqv y = contr (y , λ i → y) λ { (y' , p) i → p (~ i) , λ j → p (~ i ∨ j) } 
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
-- the type reduces to essentially isContr (fibre f b).
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

isEqv' : ∀ {a b} (A : Type a) (B : Type b)
       → (w : A ≃ B) (a : B)
       → (ψ : I)
       → Partial ψ (fibre (w .fst) a)
       → fibre (w .fst) a
isEqv' A B (f , isEquiv) a ψ u0 =
  hcomp (λ i → λ { (ψ = i0) → c .centre
                 ; (ψ = i1) → c .paths (u0 1=1) i
                 })
        (c .centre)
  where c = isEquiv .isEqv a

{-# BUILTIN EQUIVPROOF isEqv' #-}
```

<!--
```
equiv-centre : (e : A ≃ B) (y : B) → fibre (e .fst) y
equiv-centre e y = e .snd .isEqv y .centre

equiv-path : (e : A ≃ B) (y : B) →
  (v : fibre (e .fst) y) → Path _ (equiv-centre e y) v
equiv-path e y = e .snd .isEqv y .paths
```
-->

## isEquiv is propositional

A function can be an equivalence in at most one way. This follows from
propositions being closed under dependent products, and `isContr`{.Agda}
being a proposition.

```agda
isProp-isEquiv : (f : A → B) → isProp (isEquiv f)
isProp-isEquiv f x y i .isEqv p = isProp-isContr (x .isEqv p) (y .isEqv p) i
```

# Isomorphisms from equivalences

For this section, we need a definition of _isomorphism_. This is the
same as ever! An isomorphism is a function that has a two-sided inverse.
We first define what it means for a function to invert another on the
left and on the right:

```agda
isLeftInverse : (B → A) → (A → B) → Type _
isLeftInverse g f = (x : _) → g (f x) ≡ x

isRightInverse : (B → A) → (A → B) → Type _
isRightInverse g f = (x : _) → f (g x) ≡ x
```

A proof that a function $f$ is an isomorphism consists of a function $g$
in the other direction, together with homotopies exhibiting $g$ as a
left- and right- inverse to $f$.

```agda
record isIso (f : A → B) : Type (level-of A ⊔ level-of B) where
  no-eta-equality
  constructor iso
  field
    inv : B → A
    rinv : isRightInverse inv f
    linv : isLeftInverse inv f

  inverse : isIso inv
  inv inverse = f
  rinv inverse = linv
  linv inverse = rinv

Iso : ∀ {ℓ₁ ℓ₂} → Type ℓ₁ → Type ℓ₂ → Type _
Iso A B = Σ (isIso {A = A} {B = B})
```

Any function that is an equivalence is an isomorphism:

```agda
equiv→inverse : {f : A → B} → isEquiv f → B → A
equiv→inverse eqv y = eqv .isEqv y .centre .fst

equiv→section : {f : A → B} (eqv : isEquiv f) → isRightInverse (equiv→inverse eqv) f
equiv→section eqv y = eqv .isEqv y .centre .snd

equiv→retraction : {f : A → B} (eqv : isEquiv f) → isLeftInverse (equiv→inverse eqv) f
equiv→retraction {f = f} eqv x i = eqv .isEqv (f x) .paths (x , refl) i .fst

isEquiv→isIso : {f : A → B} → isEquiv f → isIso f
isIso.inv (isEquiv→isIso eqv) = equiv→inverse eqv
```

We can get an element of `x` from the proof that `f` is an equivalence -
it's the point of `A` mapped to `y`, which we get from centre of
contraction for the fibres of `f` over `y`.

```agda
isIso.rinv (isEquiv→isIso eqv) y =
  eqv .isEqv y .centre .snd
```

Similarly, that one fibre gives us a proof that the function above is a
right inverse to `f`.

```agda
isIso.linv (isEquiv→isIso {f = f} eqv) x i =
  eqv .isEqv (f x) .paths (x , refl) i .fst
```

The proof that the function is a _left_ inverse comes from the fibres of
`f` over `y` being contractible. Since we have a fibre - namely, `f`
maps `x` to `f x` by `refl`{.Agda} - we can get any other we want!

# Equivalences from isomorphisms

Any isomorphism can be upgraded into an equivalence, in a way that
preserves the function $f$, its inverse $g$, _and_ the proof $s$ that
$g$ is a right inverse to $f$. We can not preserve _everything_, though,
as is usual when making something "more coherent". Furthermore, if
everything was preserved, `isIso`{.Agda} would be a proposition, and
this is [provably not the case].

[provably not the case]: 1Lab.Counterexamples.IsIso.html

The argument presented here is done directly in cubical style, but a
less direct proof is also available, by showing that every isomorphism
is a [half-adjoint equivalence], and that half-adjoint equivalences have
contractible fibres.

[half-adjoint equivalence]: 1Lab.Equiv.HalfAdjoint.html

```agda
module _ {f : A → B} (i : isIso f) where

  open isIso i renaming ( inv to g
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
are equal, since they live in different types!  To this end, we will
build $\pi : p_0 ≡ p_1$, parts of which will be required to assemble the
overall proof that $p_0 ≡ p_1$.

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
    π₀ i = hcomp (λ k → λ { (i = i0) → g y
                          ; (i = i1) → t x0 k
                          })
                    (g (p0 (~ i)))

    θ₀ : PathP (λ i → g (p0 (~ i)) ≡ π₀ i) refl (t x0)
    θ₀ i j = hfill (λ k → λ { (i = i0) → g y
                            ; (i = i1) → t x0 k
                            })
                   (inS (g (p0 (~ i)))) j
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
    π₁ i = hcomp (λ k → λ { (i = i0) → g y
                          ; (i = i1) → t x1 k
                          })
                    (g (p1 (~ i)))

    θ₁ : PathP (λ i → g (p1 (~ i)) ≡ π₁ i) refl (t x1)
    θ₁ i j = hfill (λ k → λ { (i = i0) → g y
                            ; (i = i1) → t x1 k
                            })
                      (inS (g (p1 (~ i)))) j
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
    π i = hcomp (λ k → λ { (i = i0) → π₀ k
                         ; (i = i1) → π₁ k
                         })
                (g y)
```
</div>

This concludes the construction of $\pi$, and thus, the 2D part of the
proof. Now, we want to show that $p_0 ≡ p_1$ over a path induced by
$\pi$. This is a _square_ with a specific boundary, which can be built
by constructing an appropriate _open cube_, where the missing face is
that square. As an intermediate step, we define $\theta$ to be the
filler for the square above.

```
    θ : PathP (λ i → g y ≡ π i) π₀ π₁
    θ i j = hfill (λ k → λ { (i = i1) → π₁ k
                           ; (i = i0) → π₀ k
                           })
                      (inS (g y)) j
```

Observe that we can coherently alter $\theta$ to get $\iota$ below,
which expresses that $\mathrm{ap}\ g\ p_0$ and $\mathrm{ap}\ g\ p_1$ are
equal.

```agda
    ι : PathP (λ i → g (f (π i)) ≡ g y)
              (ap g p0)
              (ap g p1)
    ι i j = hcomp (λ k → λ { (i = i0) → θ₀ (~ j) (~ k)
                           ; (i = i1) → θ₁ (~ j) (~ k)
                           ; (j = i0) → t (π i) (~ k)
                           ; (j = i1) → g y
                           })
                  (θ i (~ j))
```

This composition can be visualised as the _red_ (front) face in the
diagram below. The back face is $\theta\ i\ (\neg\ j)$, i.e. `(θ i (~
j))` in the code. Similarly, the $j = \mathrm{i1}$ (bottom) face is `g
y`, the $j = \mathrm{i0}$ (top) face is `t (π i) (~ k)`, and similarly
for $i = \mathrm{i0}$ (left) and $i = \mathrm{i1}$ (right).

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
  \arrow[""{name=4, anchor=center, inner sep=0}, "{\mathrm{ap}\ (g \circ f)\ \pi}", color={rgb,255:red,214;green,92;blue,92}, from=1-1, to=1-5]
  \arrow[""{name=5, anchor=center, inner sep=0}, "{g\ y}"', color={rgb,255:red,214;green,92;blue,92}, from=5-1, to=5-5]
  \arrow[from=2-4, to=1-5]
  \arrow[""{name=6, anchor=center, inner sep=0}, "{\mathrm{ap}\ g\ p_1}", color={rgb,255:red,214;green,92;blue,92}, from=1-5, to=5-5]
  \arrow[""{name=7, anchor=center, inner sep=0}, "{\mathrm{ap}\ g\ p_0}"', color={rgb,255:red,214;green,92;blue,92}, from=1-1, to=5-1]
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
    sq1 : PathP (λ i → f (π i) ≡ y)
                p0 p1
    sq1 i j = hcomp (λ k → λ { (i = i0) → s (p0 j) k
                             ; (i = i1) → s (p1 j) k
                             ; (j = i0) → s (f (π i)) k
                             ; (j = i1) → s y k
                             })
                    (f (ι i j))
```

The composition above can be visualised as the front (red) face in the
cubical diagram below. Once more, left is $i = \mathrm{i0}$, right is $i
= \mathrm{i1}$, up is $j = \mathrm{i0}$, and down is $j = \mathrm{i1}$.

~~~{.quiver .tall-2}
\small
\[\begin{tikzcd}
  \textcolor{rgb,255:red,214;green,92;blue,92}{f(x_0)} &&&& \textcolor{rgb,255:red,214;green,92;blue,92}{f(x_1)} \\
  & \textcolor{rgb,255:red,92;green,92;blue,214}{f(g(f(g\ x_0)))} && \textcolor{rgb,255:red,92;green,92;blue,214}{f(g(f(g\ x_1)))} \\
  && \textcolor{rgb,255:red,92;green,92;blue,214}{f\ (\iota\ i\ j)} \\
  & \textcolor{rgb,255:red,92;green,92;blue,214}{f\ (g\ y)} && \textcolor{rgb,255:red,92;green,92;blue,214}{f\ (g\ y)} \\
  \textcolor{rgb,255:red,214;green,92;blue,92}{y} &&&& \textcolor{rgb,255:red,214;green,92;blue,92}{y}
  \arrow[""{name=0, anchor=center, inner sep=0}, "{p_1}", from=1-5, to=5-5]
  \arrow[""{name=1, anchor=center, inner sep=0}, "{\mathrm{ap}\ f\ \pi}", color={rgb,255:red,214;green,92;blue,92}, from=1-1, to=1-5]
  \arrow[""{name=2, anchor=center, inner sep=0}, "{p_0}"', color={rgb,255:red,214;green,92;blue,92}, from=1-1, to=5-1]
  \arrow[""{name=3, anchor=center, inner sep=0}, "y"', color={rgb,255:red,214;green,92;blue,92}, from=5-1, to=5-5]
  \arrow[""{name=4, anchor=center, inner sep=0}, "{\mathrm{ap}\ (f \circ g\circ f)\ \pi}"', color={rgb,255:red,92;green,92;blue,214}, from=2-2, to=2-4]
  \arrow[""{name=5, anchor=center, inner sep=0}, "{f(g\ y)}", color={rgb,255:red,92;green,92;blue,214}, from=4-2, to=4-4]
  \arrow[""{name=6, anchor=center, inner sep=0}, "{\mathrm{ap}\ f\ p_1}"', color={rgb,255:red,92;green,92;blue,214}, from=2-4, to=4-4]
  \arrow[""{name=7, anchor=center, inner sep=0}, "{\mathrm{ap}\ f\ p_0}", color={rgb,255:red,92;green,92;blue,214}, from=2-2, to=4-2]
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
    isIso→propFibre : (x0 , p0) ≡ (x1 , p1)
    isIso→propFibre i .fst = π i
    isIso→propFibre i .snd = sq1 i
```

Since the fibre over $y$ is inhabited by $(g\ y, s\ y)$, we get that any
isomorphism has contractible fibres:

```agda
  isIso→isEquiv : isEquiv f
  isIso→isEquiv .isEqv y .centre .fst = g y
  isIso→isEquiv .isEqv y .centre .snd = s y
  isIso→isEquiv .isEqv y .paths z = isIso→propFibre y (g y) (fst z) (s y) (snd z)
```

Applying this to the `Iso`{.Agda} and `_≃_`{.Agda} pairs, we can turn
any isomorphism into a coherent equivalence.

```agda
Iso→Equiv : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂}
          → Iso A B
          → A ≃ B
Iso→Equiv (f , is-iso) = f , isIso→isEquiv is-iso
```

A helpful lemma: Any function between contractible types is an equivalence:

```agda
isContr→isEquiv : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂}
                → isContr A → isContr B → {f : A → B}
                → isEquiv f
isContr→isEquiv cA cB = isIso→isEquiv f-is-iso where
  f-is-iso : isIso _
  isIso.inv f-is-iso _ = cA .centre
  isIso.rinv f-is-iso _ = isContr→isProp cB _ _
  isIso.linv f-is-iso _ = isContr→isProp cA _ _

isContr→≃ : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂}
          → isContr A → isContr B → A ≃ B
isContr→≃ cA cB = (λ _ → cB .centre) , isIso→isEquiv f-is-iso where
  f-is-iso : isIso _
  isIso.inv f-is-iso _ = cA .centre
  isIso.rinv f-is-iso _ = isContr→isProp cB _ _
  isIso.linv f-is-iso _ = isContr→isProp cA _ _
```

# Equivalence Reasoning

To make composing equivalences more intuitive, we implement operators to
do equivalence reasoning in the same style as equational reasoning.

```agda
_∙e_ : ∀ {ℓ ℓ₁ ℓ₂} {A : Type ℓ} {B : Type ℓ₁} {C : Type ℓ₂}
     → A ≃ B → B ≃ C → A ≃ C

_e¯¹ : ∀ {ℓ ℓ₁} {A : Type ℓ} {B : Type ℓ₁}
    → A ≃ B → B ≃ A
_e¯¹ eqv = Iso→Equiv ( equiv→inverse (eqv .snd)
                     , record { inv  = eqv .fst
                              ; rinv = equiv→retraction (eqv .snd)
                              ; linv = equiv→section (eqv .snd)
                              })
```
<!--
```
_∙e_ (f , e) (g , e') = (λ x → g (f x)) , eqv where
  g¯¹ : isIso g
  g¯¹ = isEquiv→isIso e'

  f¯¹ : isIso f
  f¯¹ = isEquiv→isIso e

  inv : _ → _
  inv x = f¯¹ .isIso.inv (g¯¹ .isIso.inv x)

  abstract
    right : isRightInverse inv (λ x → g (f x))
    right z =
      g (f (f¯¹ .isIso.inv (g¯¹ .isIso.inv z))) ≡⟨ ap g (f¯¹ .isIso.rinv _) ⟩
      g (g¯¹ .isIso.inv z)                      ≡⟨ g¯¹ .isIso.rinv _ ⟩
      z                                         ∎

    left : isLeftInverse inv (λ x → g (f x))
    left z =
      f¯¹ .isIso.inv (g¯¹ .isIso.inv (g (f z))) ≡⟨ ap (f¯¹ .isIso.inv) (g¯¹ .isIso.linv _) ⟩
      f¯¹ .isIso.inv (f z)                      ≡⟨ f¯¹ .isIso.linv _ ⟩
      z                                         ∎
    eqv : isEquiv (λ x → g (f x))
    eqv = isIso→isEquiv (iso (λ x → f¯¹ .isIso.inv (g¯¹ .isIso.inv x)) right left)

∙-isEquiv : ∀ {ℓ ℓ₁ ℓ₂} {A : Type ℓ} {B : Type ℓ₁} {C : Type ℓ₂}
          → {f : A → B} {g : B → C}
          → isEquiv f
          → isEquiv g
          → isEquiv (λ x → g (f x))
∙-isEquiv {f = f} {g = g} e e' = ((f , e) ∙e (g , e')) .snd
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
x ≃∎ = _ , idEquiv

infixr 30 _∙e_
infixr 2 _≃⟨⟩_ _≃⟨_⟩_
infix  3 _≃∎
```

# Propositional Extensionality

The following observation is not very complex, but it is incredibly
useful: Equivalence of propositions is the same as biimplication.

```agda
propExt : ∀ {ℓ ℓ'} {P : Type ℓ} {Q : Type ℓ'}
        → isProp P → isProp Q
        → (P → Q) → (Q → P)
        → P ≃ Q
propExt pprop qprop p→q q→p .fst = p→q
propExt pprop qprop p→q q→p .snd .isEqv y .centre = q→p y , qprop _ _
propExt pprop qprop p→q q→p .snd .isEqv y .paths (p' , path) =
  Σ-Path (pprop _ _) (isProp→isSet qprop _ _ _ _)
```
