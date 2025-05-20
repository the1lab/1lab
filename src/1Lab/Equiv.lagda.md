<!--
```agda
open import 1Lab.Path.Reasoning
open import 1Lab.Path.Groupoid
open import 1Lab.HLevel
open import 1Lab.Path
open import 1Lab.Type

open is-contr
```
-->

```agda
module 1Lab.Equiv where
```

# Equivalences

The key principle that distinguishes HoTT from other type theories is
the [[univalence]] principle: *isomorphic* types can be
[[*identified*|path]]. In cubical type theory, this turns out to be a
theorem; but from a neutral point of view, it should be read as the
*definition* of the identity types of [[universes]] --- which are
otherwise left unspecified by MLTT. However, the notion of isomorphism
is not well-behaved when higher dimensional types are involved, so we
can't actually use it to formulate univalence.

The key issue is that any [[identity system]] is equipped with a [[path
induction]] principle, which, if extended to the type of isomorphisms,
would let us conclude that *being an isomorphism* is a [[proposition]]:
but this is [provably not the case]. The result of formulating
univalence using isomorphisms is sometimes called [[isovalence]] ---
that page has a formalisation of its failure.

[provably not the case]: 1Lab.Counterexamples.IsIso.html

We must therefore define a property of functions which refines being an
isomorphism but *is* an isomorphism: functions satisfying this property
will be called equivalences. More specifically, we're looking for a
family $\isequiv(f)$ which

- is implied by $\isiso(f)$, so that any function with a two-sided
  inverse is an equivalence. Apart from preserving the connection with
  the intuitive motivation behind univalence, exhibiting a two-sided
  inverse to a given map is simply *easier* than proving that it's a
  coherent equivalence.

- implies $\isiso(f)$, so that knowing that a map is an equivalence also
  lets you extract a two-sided inverse. Most notions of equivalence will
  also tell you additional properties about the connection between $f$
  and its inverse map.

- and finally, is an actual [[proposition]].

Put concisely, we're looking to define a [[propositional truncation]] of
$\isiso(f)$ --- one which allows us to conveniently project out the
underlying data. Since propositional truncations are unique, this means
that all type families satisfying the three bullet points above are
*themselves* equivalent; so any choice made must be meta-mathematical,
driven by concerns like ease of use, and efficiency of the
formalisation.

Here in the 1Lab, we formalise three acceptable notions of equivalence:

* [[biinvertible maps]], which store *two* inverses to the given function;
* [[half-adjoint equivalences]], which, in addition to the inverse map
  and the witnesses of invertibility, have an extra *coherence datum*; and
* the notion defined in this file, **contractible maps**, which
  repackage the notion of equivalence in a homotopically-inspired way.

<!--
```agda
private variable
  ℓ ℓ₁ ℓ₂ : Level
  A B C : Type ℓ₁
  P : A → Type ℓ
```
-->

## Isomorphisms {defines="quasi-inverse"}

Before we set about defining and working with equivalences, we'll warm
up by defining, and proving basic things about, isomorphisms. First, we
define what it means for functions to be inverses of eachother, on both
the left and the right.

```agda
is-left-inverse : (B → A) → (A → B) → Type _
is-left-inverse g f = (x : _) → g (f x) ≡ x

is-right-inverse : (B → A) → (A → B) → Type _
is-right-inverse g f = (x : _) → f (g x) ≡ x
```

A function $g$ which is both a left- and right inverse to $f$ is called
a **two-sided inverse** (to $f$). To say that a function is an
isomorphism is to equip it with a two-sided inverse.

::: warning
Despite the name `is-iso`{.Agda}, a two-sided inverse is actual *data*
we can equip a function with: it's not, in general, valued in
[[propositions]].
:::

```agda
record is-iso (f : A → B) : Type (level-of A ⊔ level-of B) where
  no-eta-equality
  constructor iso
  field
    from : B → A
    rinv : is-right-inverse from f
    linv : is-left-inverse from f
```

It's immediate from the symmetry of the definition that if $g$ is a
two-sided inverse to $f$, then $f$ also inverts $g$: an isomorphism's
inverse is again an isomorphism.

```agda
  inverse : is-iso from
  inverse .from = f
  inverse .rinv = linv
  inverse .linv = rinv
```

<!--
```agda
Iso : ∀ {ℓ₁ ℓ₂} → Type ℓ₁ → Type ℓ₂ → Type _
Iso A B = Σ (A → B) is-iso

module _ where
  open is-iso
```
-->

Second, a composite of isomorphisms is an isomorphism: if we can undo
$f$ and $g$ individually, we can undo them sequentially, by first
undoing $g$, then undoing $f$. The observation that the inverse is in
the opposite order is sometimes humorously referred to as the
*socks-and-shoes principle*.

```agda
  ∘-is-iso : {f : B → C} {g : A → B} → is-iso f → is-iso g → is-iso (f ∘ g)
  ∘-is-iso f-im g-im .from x = g-im .from (f-im .from x)
  ∘-is-iso {f = f} {g = g} f-im g-im .rinv x =
    f (g (g-im .from (f-im .from x))) ≡⟨ ap f (g-im .rinv _) ⟩
    f (f-im .from x)                  ≡⟨ f-im .rinv _ ⟩
    x                                 ∎
  ∘-is-iso {g = g} f-im g-im .linv x =
    ap (g-im .from) (f-im .linv (g x)) ∙ g-im .linv x
```

Finally, the identity map is its own two-sided inverse, so it is an
isomorphism. Keep in mind that, again, there are multiple ways for a map
to _be an isomorphism_. It would be more correct to say that there is a
parametric way to make the identity map into an isomorphism: if we know
more about the specific type, there might be other ways.

```agda
  private
    id-iso : is-iso {A = A} id
    id-iso .from   = id
    id-iso .rinv x = refl
    id-iso .linv x = refl
```

## Equivalences proper {defines=equivalence}

With that out of the way, we can actually define the property of
functions that we'll adopt under the name _equivalence_. The notion of
contractible maps is due to Voevodsky, and it very elegantly packages
the data of an inverse in a way that is immediately seen to be coherent.
However, it turns out to have a very simple motivating explanation at
the level of [[sets]]:

Recall that the **preimage** of a function $f : A \to B$ over a point $y
: B$, written $f^*(y)$, is the set $\{ x : A\ |\ f(x) = y \}$. The
properties of $f$ being injective and surjective can be profitably
rephrased in terms of its preimages:

* a function is injective if each of its preimages has *at most one*
  element. For if we have $x, y : A$ and $p : f(x) = f(y)$, then we can
  look at the set $f^*(f(x))$: it has elements given by $(x, \refl)$,
  and $(y, p)$. For these to be the same, we must have $x = y$, so $f$
  is injective.

* a function is surjective if each of its preimages has *at least one*
  element, in the sense of [[propositional truncations]]. This is the
  actual definition: for the preimage $f^*(y)$ to be inhabited means
  that there exists $x : A$ with $f(x) = y$.

Putting these together, a function is a bijection if each of its fibres
has exactly one element. Phrased as above, we've actually arrived
exactly at the definition of equivalence proposed by Voevodsky: we just
have to rephrase a few things.

::: {.definition #fibre}
Rather than talking about preimages, in the context of homotopy type
theory, we refer to them as **(homotopy) fibres** over a given point.
Not only is this an objectively more aesthetic name, but it reminds us
that the path $f(x) = y$ is actual *structure* we are equipping the
point with, rather than being a property of points.

```agda
fibre : (A → B) → B → Type _
fibre {A = A} f y = Σ[ x ∈ A ] f x ≡ y
```
:::

Finally, rather than talking of types with *exactly one element*, we
already have a rephrasing which works at the level of homotopy type
theory: [[contractibility|contractible]]. This is exactly the
conjunction of the assertions above, just packaged in a way that does
not require us to first define [[propositional truncations]]. A function
is an **equivalence** if all of its fibres are contractible:

```agda
record is-equiv (f : A → B) : Type (level-of A ⊔ level-of B) where
  no-eta-equality
  field
    is-eqv : (y : B) → is-contr (fibre f y)
```

<!--
```agda
{-# INLINE is-equiv.constructor #-}
open is-equiv public

_≃_ : ∀ {ℓ₁ ℓ₂} → Type ℓ₁ → Type ℓ₂ → Type _
_≃_ A B = Σ (A → B) is-equiv
```
-->

To warm up, let's show that the identity map is an equivalence, working
with the definition directly. First, we have to show that the fibre over
$y$ has an element, for which we can take $(y, \refl)$, since what we're
looking for boils down to an element $y : A$ which is mapped to $y$ by
the identity function.

```agda
id-equiv : is-equiv {A = A} id
id-equiv .is-eqv y .centre = y , refl
```

Then, given any pair $(x, p)$ with $x : A$ and $p : x = y$, we must show
that we have $(y, \refl) = (x, p)$. But this is exactly what [[path
induction]] promises us! Rather than an appeal to transport, we can
directly use a *connection*:

```agda
id-equiv .is-eqv y .paths (x , p) i = p (~ i) , λ j → p (~ i ∨ j)
```

<!--
```agda
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

Since Cubical Agda has primitives that refer to equivalences, we have to
take some time to teach the system about the type we just defined above.
In addition to teaching it how to project the underlying function of an
equivalence, we must prove that an equivalence has contractible fibres
--- but what the system asks of us is that each [[partial fibre|partial
cube]] be *extensible*: the cubical phrasing of contractibility.

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
```agda
equiv-centre : (e : A ≃ B) (y : B) → fibre (e .fst) y
equiv-centre e y = e .snd .is-eqv y .centre

equiv-path : (e : A ≃ B) (y : B) →
  (v : fibre (e .fst) y) → Path _ (equiv-centre e y) v
equiv-path e y = e .snd .is-eqv y .paths
```
-->

### is-equiv is a proposition

Since being contractible is a proposition, and being an equivalence
simply quantifies contractibility over each fibre, we can directly
conclude that being an equivalence is a proposition.

```agda
is-equiv-is-prop : (f : A → B) → is-prop (is-equiv f)
is-equiv-is-prop f x y i .is-eqv p = is-contr-is-prop (x .is-eqv p) (y .is-eqv p) i
```

### Equivalences are invertible

We can now show that equivalences are invertible. This will amount to
taking apart the proof that each fibre is contractible. If we have $y :
B$, then the centre of contraction of $f^*(y)$ gives us a distinguished
$x : A$ and a path $f(x) = y$:

```agda
equiv→inverse : {f : A → B} → is-equiv f → B → A
equiv→inverse eqv y = eqv .is-eqv y .centre .fst

equiv→counit
  : ∀ {f : A → B} (eqv : is-equiv f) (y : B) → f (equiv→inverse eqv y) ≡ y
equiv→counit eqv y = eqv .is-eqv y .centre .snd
```

Now we have to show that applying the inverse to $f(x)$ gives us back
$x$. But note that $f^*(fx)$ has two inhabitants: the centre of
contraction, which is projected by the inverse, but also the simpler
$(x, \refl)$. Since the fibre is contractible, we have a path
$f\inv(fx) = x$.

```agda
equiv→unit
  : ∀ {f : A → B} (eqv : is-equiv f) x → equiv→inverse eqv (f x) ≡ x
equiv→unit {f = f} eqv x i = eqv .is-eqv (f x) .paths (x , refl) i .fst
```

Contractibility gives us, in addition to a path between the *points*
$f\inv(fx) = x$, a particular higher-dimensional *square*. Note that we
have two ways of proving that $ff\inv fx = fx$, corresponding to either
cancelling the outer $ff\inv$ or the inner $f\inv f$: $f(\eta x)$ and
$\eps fx$. The square we obtain tells us that these are actually the
same:

~~~{.quiver}
\[\begin{tikzcd}[ampersand replacement=\&]
  {ff\inv fx} \&\& fx \\
  \\
  fx \&\& fx
  \arrow["{f(\eta x)}", from=1-1, to=1-3]
  \arrow["{\eps (fx)}"', from=1-1, to=3-1]
  \arrow["\refl"', from=3-1, to=3-3]
  \arrow["\refl", from=1-3, to=3-3]
\end{tikzcd}\]
~~~

```agda
equiv→square
  : ∀ {f : A → B} (eqv : is-equiv f) (x : A)
  → Square (ap f (equiv→unit eqv x)) (equiv→counit eqv (f x)) refl refl
equiv→square {f = f} eqv x i j = eqv .is-eqv (f x) .paths (x , refl) i .snd j
```

However, the square above is slightly skewed: we would have preferred
for the two non-trivial paths to be in opposite sides, so that it would
correspond to a `Path`{.Agda} between the paths. We can use
`hcomp`{.Agda} to slide one of the faces around to get us the more
useful direct proof that $f(\eta x) = \eps fx$.

```agda
equiv→zig
  : ∀ {f : A → B} (eqv : is-equiv f) x
  → ap f (equiv→unit eqv x) ≡ equiv→counit eqv (f x)
equiv→zig {f = f} eqv x i j = hcomp (∂ i ∨ ∂ j) λ where
  k (k = i0) → equiv→square eqv x j i
  k (i = i0) → f (equiv→unit eqv x j)
  k (i = i1) → equiv→counit eqv (f x) (j ∨ ~ k)
  k (j = i0) → equiv→counit eqv (f x) (i ∧ ~ k)
  k (j = i1) → f x
```

<details>
<summary>Note that the law established above has a symmetric
counterpart, showing that $f\inv(\eps x) = \eta f\inv(x)$. However, we
can prove that this follows from the law above, using another cubical
argument. Since the extent of the proof is another lifting problem, we
won't expand on the details.
</summary>

```agda
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
```

</details>

Finally, it'll be convenient for us to package some of the theorems
above into a proof that every equivalence is an isomorphism:

```agda
is-equiv→is-iso : {f : A → B} → is-equiv f → is-iso f
is-equiv→is-iso eqv .is-iso.from = equiv→inverse eqv
is-equiv→is-iso eqv .is-iso.rinv = equiv→counit eqv
is-equiv→is-iso eqv .is-iso.linv = equiv→unit eqv
```

## Improving isomorphisms

Having shown that being an equivalence is a proposition and *implies*
being an isomorphism, we're left with the trickiest part: showing that
it's *implied by* being an isomorphism. The argument presented here is
*natively cubical*; we do everything in terms of lifting properties.
There is a more "algebraic" version, factoring through the intermediate
notion of [[half-adjoint equivalence]], available on that page.

We'll write $(f, g, s, t)$ for the the function $f : A \to B$, its
inverse $g : B \to A$, and the two homotopies. Our construction
*definitionally* preserves $f$, $g$ and the homotopy $s : fg \sim \id$.
However, it can *not* preserve the proof $t : gf \sim \id$, since that
would imply that `is-iso`{.Agda} is a proposition, which, again, is
[provably not the case].

[provably not the case]: 1Lab.Counterexamples.IsIso.html

```agda
module _ {f : A → B} (i : is-iso f) where
  open is-iso i renaming (from to g ; rinv to s ; linv to t)
```

We want to show that, for any $y$, the `fibre`{.Agda} of $f$ over $y$ is
contractible. According to our decomposition above, it will suffice to
show that the fibre is propositional, and that it is inhabited.
Inhabitation is easy --- $(gy,sy)$ belongs to the fibre $f^*(y)$. Let's
focus on propositionality.

<!--
```agda
  _ = PathP
```
-->

Suppose that we have $y$, $x_0$, $x_1$, $p_0$ and $p_1$ as below; Note
that $(x_0, p_0)$ and $(x_1, p_1)$ are fibres of $f$ over $y$. What we
need to show is that we have some $\pi : x_0 ≡ x_1$ and $p_0 ≡ p_1$
_`over`{.Agda ident=PathP}_ $\pi$.

```agda
  private module _ (y : B) (x0 x1 : A) (p0 : f x0 ≡ y) (p1 : f x1 ≡ y) where
```

As an intermediate step in proving that $p_0 ≡ p_1$, we _must_ show that
$x_0 ≡ x_1$ --- without this, we can't even _state_ that $p_0$ and $p_1$
are identified, since they live in different types! To this end, we will
build $\pi : x_0 ≡ x_1$, parts of which will be required to assemble the
overall proof that $p_0 ≡ p_1$.

We'll detail the construction of $\pi_0$; for $\pi_1$, the same method
is used. We want to construct a _line_, which we can do by exhibiting
that line as the missing face in a _square_. We have equations $g\ y ≡
g\ y$ (`refl`{.Agda}), $g\ (f\ x_0) ≡ g\ y$ (the action of `g` on `p0`),
and $g\ (f\ x_0) = x_0$ by the assumption that $g$ is a right inverse to
$f$.  Diagrammatically, these fit together into a square:

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
which expresses that $\ap{g}{p_0}$ and $\ap{g}{p_1}$ are identified.

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
j))` in the code. Similarly, the $j = \rm{i1}$ (bottom) face is `g y`,
the $j = \rm{i0}$ (top) face is `t (π i) (~ k)`, and similarly for $i =
\rm{i0}$ (left) and $i = \rm{i1}$ (right).

~~~{.quiver}
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
  \arrow[""{name=4, anchor=center, inner sep=0}, "{\ap{(g \circ f)}{\pi}}", color={rgb,255:red,214;green,92;blue,92}, from=1-1, to=1-5]
  \arrow[""{name=5, anchor=center, inner sep=0}, "{g\ y}"', color={rgb,255:red,214;green,92;blue,92}, from=5-1, to=5-5]
  \arrow[from=2-4, to=1-5]
  \arrow[""{name=6, anchor=center, inner sep=0}, "{\ap{g}{p_1}}", color={rgb,255:red,214;green,92;blue,92}, from=1-5, to=5-5]
  \arrow[""{name=7, anchor=center, inner sep=0}, "{\ap{g}{p_0}}"', color={rgb,255:red,214;green,92;blue,92}, from=1-1, to=5-1]
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
cubical diagram below. Once more, left is $i = \rm{i0}$, right is $i =
\rm{i1}$, up is $j = \rm{i0}$, and down is $j = \rm{i1}$.

~~~{.quiver}
\small
\[\begin{tikzcd}
  \textcolor{rgb,255:red,214;green,92;blue,92}{f(x_0)} &&&& \textcolor{rgb,255:red,214;green,92;blue,92}{f(x_1)} \\
  & \textcolor{rgb,255:red,92;green,92;blue,214}{f(g(f(g\ x_0)))} && \textcolor{rgb,255:red,92;green,92;blue,214}{f(g(f(g\ x_1)))} \\
  && \textcolor{rgb,255:red,92;green,92;blue,214}{f\ (\iota\ i\ j)} \\
  & \textcolor{rgb,255:red,92;green,92;blue,214}{f\ (g\ y)} && \textcolor{rgb,255:red,92;green,92;blue,214}{f\ (g\ y)} \\
  \textcolor{rgb,255:red,214;green,92;blue,92}{y} &&&& \textcolor{rgb,255:red,214;green,92;blue,92}{y}
  \arrow[""{name=0, anchor=center, inner sep=0}, "{p_1}", from=1-5, to=5-5]
  \arrow[""{name=1, anchor=center, inner sep=0}, "{\ap{f}{\pi}}", color={rgb,255:red,214;green,92;blue,92}, from=1-1, to=1-5]
  \arrow[""{name=2, anchor=center, inner sep=0}, "{p_0}"', color={rgb,255:red,214;green,92;blue,92}, from=1-1, to=5-1]
  \arrow[""{name=3, anchor=center, inner sep=0}, "y"', color={rgb,255:red,214;green,92;blue,92}, from=5-1, to=5-5]
  \arrow[""{name=4, anchor=center, inner sep=0}, "{\ap{(f \circ g\circ f)}{\pi}}"', color={rgb,255:red,92;green,92;blue,214}, from=2-2, to=2-4]
  \arrow[""{name=5, anchor=center, inner sep=0}, "{f(g\ y)}", color={rgb,255:red,92;green,92;blue,214}, from=4-2, to=4-4]
  \arrow[""{name=6, anchor=center, inner sep=0}, "{\ap{f}{p_1}}"', color={rgb,255:red,92;green,92;blue,214}, from=2-4, to=4-4]
  \arrow[""{name=7, anchor=center, inner sep=0}, "{\ap{f}{p_0}}", color={rgb,255:red,92;green,92;blue,214}, from=2-2, to=4-2]
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
  {-# INLINE is-iso→is-equiv #-}
  is-iso→is-equiv = record
    { is-eqv = λ y → record
      { centre = g y , s y
      ; paths = λ z → is-iso→fibre-is-prop y (g y) (z .fst) (s y) (z .snd) } }
```

If we package this differently, then we can present it as a map between
the types of isomorphisms $A \to B$ and equivalences $A \simeq B$.

```agda
Iso→Equiv : Iso A B → A ≃ B
{-# INLINE Iso→Equiv #-}
Iso→Equiv (f , is-iso) = record { fst = f ; snd = is-iso→is-equiv is-iso }
```

<!--
```agda
inverse-is-equiv : {f : A → B} (eqv : is-equiv f) → is-equiv (equiv→inverse eqv)
inverse-is-equiv {f = f} eqv .is-eqv x .centre = record
  { fst = f x ; snd = equiv→unit eqv x }
inverse-is-equiv {A = A} {B = B} {f = f} eqv .is-eqv x .paths (y , p) = q where
  g = equiv→inverse eqv
  η = equiv→unit eqv
  ε = equiv→counit eqv
  zag = equiv→zag eqv

  q : (f x , η x) ≡ (y , p)
  q i .fst = (ap f (sym p) ∙ ε y) i
  q i .snd j = hcomp (∂ i ∨ ∂ j) λ where
    k (k = i0) → zag y j i
    k (i = i0) → η (p k) (j ∧ k)
    k (i = i1) → p (k ∧ j)
    k (j = i0) → g (∙-filler' (ap f (sym p)) (ε y) k i)
    k (j = i1) → η (p k) (i ∨ k)

module Equiv {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A ≃ B) where
  to   = f .fst
  from = equiv→inverse (f .snd)
  η    = equiv→unit (f .snd)
  ε    = equiv→counit (f .snd)
  zig  = equiv→zig (f .snd)
  zag  = equiv→zag (f .snd)

  injective : ∀ {x y} → to x ≡ to y → x ≡ y
  injective p = ap fst $ is-contr→is-prop (f .snd .is-eqv _) (_ , refl) (_ , sym p)

  injective₂ : ∀ {x y z} → to x ≡ z → to y ≡ z → x ≡ y
  injective₂ p q = ap fst $ is-contr→is-prop (f .snd .is-eqv _)
    (_ , p) (_ , q)

  inverse : B ≃ A
  inverse = from , inverse-is-equiv (f .snd)

  adjunctl : ∀ {x y} → to x ≡ y → x ≡ from y
  adjunctl p = sym (η _) ∙ ap from p

  adjunctr : ∀ {x y} → x ≡ from y → to x ≡ y
  adjunctr p = ap to p ∙ ε _

  adjunct : ∀ {x y} → (to x ≡ y) ≃ (x ≡ from y)
  adjunct {x} {y} .fst = adjunctl
  adjunct {x} {y} .snd = is-iso→is-equiv record
    { from = adjunctr
    ; rinv = λ p → J (λ _ p → sym (η _) ∙ ap from (ap to (sym p) ∙ ε _) ≡ sym p)
      (sym (∙-swapl (∙-idr _ ∙ sym (zag _) ∙ sym (∙-idl _) ∙ sym (ap-∙ from _ _))))
      (sym p)
    ; linv = J (λ _ p → ap to (sym (η _) ∙ ap from p) ∙ ε _ ≡ p)
      (sym (∙-swapr (∙-idl _ ∙ ap sym (sym (zig _)) ∙ sym (∙-idr _) ∙ sym (ap-∙ to _ _))))
    }

module Iso {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} ((f , f-iso) : Iso A B) where
  open is-iso f-iso renaming (inverse to inverse-iso) public

  injective : ∀ {x y} → f x ≡ f y → x ≡ y
  injective p = sym (linv _) ∙∙ ap from p ∙∙ linv _

  inverse : Iso B A
  inverse = from , inverse-iso

injectiveP
  : ∀ {ℓ ℓ'} {A : I → Type ℓ} {B : I → Type ℓ'} (f : ∀ i → Iso (A i) (B i)) {x y}
  → PathP (λ i → B i) (f i0 .fst x) (f i1 .fst y)
  → PathP (λ i → A i) x y
injectiveP f {x} {y} p =
  sym (Iso.linv (f i0) x) ◁ apd (λ i → Iso.from (f i)) p ▷ Iso.linv (f i1) y
```
-->

## Simple constructions

Having established the three desiderata for a notion of equivalence, we
will spend the rest of this module constructing readily-available
equivalences, and establishing basic facts about them.

### Contractible types

If $A$ and $B$ are contractible types, then any function $f : A \to B$
must be homotopic to the function which sends everything in $A$ to the
centre of $B$; This function is invertible by sending everything *in
$B$* to the centre of $A$. Therefore, any function between contractible
types is an equivalence.

```agda
is-contr→is-equiv : is-contr A → is-contr B → {f : A → B} → is-equiv f
is-contr→is-equiv cA cB = is-iso→is-equiv λ where
  .is-iso.from _ → cA .centre
  .is-iso.linv _ → is-contr→is-prop cA _ _
  .is-iso.rinv _ → is-contr→is-prop cB _ _
```

Pairing this with the "canonical" function, we obtain an equivalence
between any contractible types. Since the unit type is contractible, any
contractible type is equivalent to the unit.

```agda
is-contr→≃ : is-contr A → is-contr B → A ≃ B
is-contr→≃ cA cB = (λ _ → cB .centre) , is-contr→is-equiv cA cB

is-contr→≃⊤ : is-contr A → A ≃ ⊤
is-contr→≃⊤ c = is-contr→≃ c ⊤-is-contr
```

### Strictness of the empty type

We say that an [[initial object]] is *strict* if every map into it is an
equivalence. This holds of the empty type, and moreover, the proof is
delightfully simple! Since showing that $f : A \to \bot$ is an
equivalence boils down to showing something about $f$ *given a point $y
: \bot$*, it's immediate that any map into the empty type is an
equivalence.

```agda
¬-is-equiv : (f : A → ⊥) → is-equiv f
¬-is-equiv f .is-eqv ()

is-empty→≃⊥ : ¬ A → A ≃ ⊥
is-empty→≃⊥ ¬a = _ , ¬-is-equiv ¬a
```

### Propositional extensionality (redux)

<!--
```agda
module _ {ℓ ℓ'} {P : Type ℓ} {Q : Type ℓ'} (pprop : is-prop P) (qprop : is-prop Q) where
```
-->

Following the trend set by contractible types, above, another h-level
for which constructing equivalences is easy are the [[propositions]]. If
$P$ and $Q$ are propositions, then any map $P \to P$ (resp. $Q \to Q$)
must be homotopic to the identity, and consequently any pair of
functions $P \to Q$ and $Q \to P$ is a pair of inverses. Put another
way, any biimplication between propositions is an equivalence.

```agda
  biimp-is-equiv : (f : P → Q) → (Q → P) → is-equiv f
  biimp-is-equiv f g = is-iso→is-equiv λ where
    .is-iso.from x → g x
    .is-iso.linv x → pprop (g (f x)) x
    .is-iso.rinv x → qprop (f (g x)) x

  prop-ext : (P → Q) → (Q → P) → P ≃ Q
  prop-ext p→q q→p .fst = p→q
  prop-ext p→q q→p .snd = biimp-is-equiv p→q q→p
```

### Groupoid operations

Since [[types are higher groupoids]], we have certain algebraic laws
regarding the behaviour of path operations which can be expressed as
saying that they form equivalences. First, the *inverse path* operation
is definitionally involutive, so it's its own two-sided inverse:

```agda
sym-equiv : ∀ {ℓ} {A : Type ℓ} {x y : A} → (x ≡ y) ≃ (y ≡ x)
sym-equiv .fst = sym
sym-equiv .snd = is-iso→is-equiv (iso sym (λ _ → refl) (λ _ → refl))
```

If we have a path $p : x = y$, then $p\inv pq = q$, and $pp\inv r = r$.
Viewing this as a function of $q$, it says that the operation
*precompose with $p$* is inverted on both sides by
precomposition with $p\inv$.

```agda
∙-pre-equiv : ∀ {ℓ} {A : Type ℓ} {x y z : A} → x ≡ y → (y ≡ z) ≃ (x ≡ z)
∙-pre-equiv p .fst q = p ∙ q
∙-pre-equiv p .snd = is-iso→is-equiv λ where
  .is-iso.from q → sym p ∙ q
  .is-iso.rinv q → ∙-assoc p _ _       ∙∙ ap (_∙ q) (∙-invr p) ∙∙ ∙-idl q
  .is-iso.linv q → ∙-assoc (sym p) _ _ ∙∙ ap (_∙ q) (∙-invl p) ∙∙ ∙-idl q
```

Similarly, *post*composition with $p$ is inverted on both sides by
postcomposition with $p\inv$, so it too is an equivalence.

```agda
∙-post-equiv : ∀ {ℓ} {A : Type ℓ} {x y z : A} → y ≡ z → (x ≡ y) ≃ (x ≡ z)
∙-post-equiv p .fst q = q ∙ p
∙-post-equiv p .snd = is-iso→is-equiv λ where
  .is-iso.from q → q ∙ sym p
  .is-iso.rinv q → sym (∙-assoc q _ _) ∙∙ ap (q ∙_) (∙-invl p) ∙∙ ∙-idr q
  .is-iso.linv q → sym (∙-assoc q _ _) ∙∙ ap (q ∙_) (∙-invr p) ∙∙ ∙-idr q
```

### The Lift type

Because Agda's universes are not *cumulative*, we can not freely move a
type $A : \ty_0$ to conclude that $A : \ty_1$, or to higher universes.
To work around this, we have a `Lift`{.Agda} type, which, given a small
type $A : \ty_i$ and some universe $j \gt i$, gives us a _name_ for $A$
in $\ty_j$. To know that this operation is coherent, we can prove that
the lifting map

$$
A \to \operatorname{Lift}_j A
$$

is an equivalence: the name of $A$ in $\ty_j$ really is equivalent to
the type we started with. Because `Lift`{.Agda} is a very well-behaved
record type, the proof that this is an equivalence looks very similar to
the proof that the identity function is an equivalence:

```agda
Lift-≃ : ∀ {a ℓ} {A : Type a} → Lift ℓ A ≃ A
Lift-≃ .fst (lift a) = a
Lift-≃ .snd .is-eqv a .centre = lift a , refl
Lift-≃ .snd .is-eqv a .paths (x , p) i .fst = lift (p (~ i))
Lift-≃ .snd .is-eqv a .paths (x , p) i .snd j = p (~ i ∨ j)
```

Finally, while we're here, we can easily prove that the `Lift`{.Agda}
type *respects equivalences*, in that if we have small $A \simeq B$,
then their liftings $\operatorname{Lift}_j A$ and $\operatorname{Lift}_j
B$ will still be equivalent.

```agda
Lift-ap
  : ∀ {a b ℓ ℓ'} {A : Type a} {B : Type b}
  → A ≃ B → Lift ℓ A ≃ Lift ℓ' B
Lift-ap (f , eqv) .fst (lift x) = lift (f x)
Lift-ap f .snd .is-eqv (lift y) .centre = lift (Equiv.from f y) , ap lift (Equiv.ε f y)
Lift-ap f .snd .is-eqv (lift y) .paths (lift x , q) i = lift (p i .fst) , λ j → lift (p i .snd j)
  where p = f .snd .is-eqv y .paths (x , ap lower q)
```

### Involutions

Finally, we can show here that any *involution* --- a function $A \to
A$, which inverts *itself* --- is an equivalence.

```agda
is-involutive→is-equiv : {f : A → A} → (∀ a → f (f a) ≡ a) → is-equiv f
is-involutive→is-equiv inv = is-iso→is-equiv (iso _ inv inv)
```

## Closure properties

:::{.definition #two-out-of-three}
We will now show a rather fundamental property of equivalences: they are
closed under *two-out-of-three*. This means that, considering $f : A \to
B$, $g : B \to C$, and $(g \circ f) : A \to C$ as a set of three things,
if any two are an equivalence, then so is the third:
:::

<!--
```agda
module _ {ℓ ℓ₁ ℓ₂} {A : Type ℓ} {B : Type ℓ₁} {C : Type ℓ₂} {f : A → B} {g : B → C} where
```
-->

```agda
  ∘-is-equiv    : is-equiv f → is-equiv g → is-equiv (g ∘ f)
  equiv-cancell : is-equiv g → is-equiv (g ∘ f) → is-equiv f
  equiv-cancelr : is-equiv f → is-equiv (g ∘ f) → is-equiv g
```

We have already shown the first of these, when the individual functions
are equivalences, since being an equivalence is logically equivalent to
being an isomorphism. Supposing that $g$ and $g \circ f$ are, then we
can show that

$$
B \xto{g} C \xto{(gf)\inv} A
$$

is an inverse to $f$; the other case is symmetric. Since both of the
proofs are just calculations, we will not comment on them.

<details>
<summary>However, we will render them for the curious reader. It's an
instructive exercise to work these out for yourself!</summary>

```agda
  ∘-is-equiv ef eg = is-iso→is-equiv (∘-is-iso (is-equiv→is-iso eg) (is-equiv→is-iso ef))

  equiv-cancell eg egf = is-iso→is-equiv (iso inv right left) where
    inv : B → A
    inv x = equiv→inverse egf (g x)
    opaque
      right : is-right-inverse inv f
      right x =
        f (equiv→inverse egf (g x))                        ≡˘⟨ equiv→unit eg _ ⟩
        equiv→inverse eg (g (f (equiv→inverse egf (g x)))) ≡⟨ ap (equiv→inverse eg) (equiv→counit egf _) ⟩
        equiv→inverse eg (g x)                             ≡⟨ equiv→unit eg _ ⟩
        x                                                  ∎
      left : is-left-inverse inv f
      left x = equiv→unit egf x

  equiv-cancelr ef egf = is-iso→is-equiv (iso inv right left) where
    inv : C → B
    inv x = f (equiv→inverse egf x)
    right : is-right-inverse inv g
    right x = equiv→counit egf x
    left : is-left-inverse inv g
    left x =
      f (equiv→inverse egf (g x))                        ≡˘⟨ ap (f ∘ equiv→inverse egf ∘ g) (equiv→counit ef _) ⟩
      f (equiv→inverse egf (g (f (equiv→inverse ef x)))) ≡⟨ ap f (equiv→unit egf _) ⟩
      f (equiv→inverse ef x)                             ≡⟨ equiv→counit ef _ ⟩
      x                                                  ∎
```

</details>

Specialising these, any left- or right- inverse of an equivalence must
be homotopic to the specified one, so that *it too* is an equivalence.

```agda
left-inverse→equiv
  : {f : A → B} {g : B → A}
  → is-left-inverse g f → is-equiv f → is-equiv g
left-inverse→equiv linv ef = equiv-cancelr ef
  (subst is-equiv (sym (funext linv)) id-equiv)

right-inverse→equiv
  : {f : A → B} {g : B → A}
  → is-right-inverse g f → is-equiv f → is-equiv g
right-inverse→equiv rinv ef = equiv-cancell ef
  (subst is-equiv (sym (funext rinv)) id-equiv)
```

### Equivalence reasoning

To simplify working with chains of equivalences, we can re-package their
closure operations as mixfix operators, so that we have a shorthand
notation for working with composites of pairs of equivalences *and* long
chains of equivalences, where making the intermediate steps explicit is
more important.

```agda
id≃ : ∀ {ℓ} {A : Type ℓ} → A ≃ A
id≃ = id , id-equiv

_∙e_ : A ≃ B → B ≃ C → A ≃ C
_∙e_ (f , ef) (g , eg) = g ∘ f , ∘-is-equiv ef eg

_e⁻¹ : A ≃ B → B ≃ A
((f , ef) e⁻¹) = equiv→inverse ef , inverse-is-equiv ef

≃⟨⟩-syntax : ∀ {ℓ ℓ₁ ℓ₂} (A : Type ℓ) {B : Type ℓ₁} {C : Type ℓ₂}
           → B ≃ C → A ≃ B → A ≃ C
≃⟨⟩-syntax A g f = f ∙e g

_≃˘⟨_⟩_ : ∀ {ℓ ℓ₁ ℓ₂} (A : Type ℓ) {B : Type ℓ₁} {C : Type ℓ₂}
        → B ≃ A → B ≃ C → A ≃ C
A ≃˘⟨ f ⟩ g = f e⁻¹ ∙e g

_≃⟨⟩_ : ∀ {ℓ ℓ₁} (A : Type ℓ) {B : Type ℓ₁} → A ≃ B → A ≃ B
x ≃⟨⟩ x≡y = x≡y

_≃∎ : ∀ {ℓ} (A : Type ℓ) → A ≃ A
x ≃∎ = id≃
```

<!--
```agda
infixr 30 _∙e_
infix 31 _e⁻¹

infixr 2 ≃⟨⟩-syntax _≃⟨⟩_ _≃˘⟨_⟩_
infix  3 _≃∎
infix 21 _≃_

syntax ≃⟨⟩-syntax x q p = x ≃⟨ p ⟩ q
```
-->

## Some useful equivalences

We can extend `subst`{.Agda} to an equivalence between `Σ[ y ∈ A ] (y ≡ x × P y)`
and `P x` for every `x : A` and `P : A → Type`.

```agda
subst≃
  : (x : A) → (Σ[ y ∈ A ] (y ≡ x × P y)) ≃ P x
subst≃ {A = A} {P = P} x = Iso→Equiv (to , iso from invr invl)
  where
    to : Σ[ y ∈ A ] (y ≡ x × P y) → P x
    to (y , y=x , py) = subst P y=x py

    from : P x → Σ[ y ∈ A ] (y ≡ x × P y)
    from px = x , refl , px

    invr : is-right-inverse from to
    invr = transport-refl

    invl : is-left-inverse from to
    invl (y , y=x , py) i =
      (y=x (~ i)) ,
      (λ j → y=x (~ i ∨ j)) ,
      transp (λ j → P (y=x (~ i ∧ j))) i py
```

<!--
```agda
is-equiv≃fibre-is-contr
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → {f : A → B}
  → is-equiv f ≃ (∀ x → is-contr (fibre f x))
is-equiv≃fibre-is-contr {f = f} =
  prop-ext
    (is-equiv-is-prop f)
    (λ f g i x → is-contr-is-prop (f x) (g x) i)
    is-eqv
    (λ fib-contr → record { is-eqv = fib-contr })

-- This ideally would go in 1Lab.HLevel, but we don't have equivalences
-- defined that early in the bootrapping process.
is-prop→is-contr-iff-inhabited
  : ∀ {ℓ} {A : Type ℓ}
  → is-prop A
  → is-contr A ≃ A
is-prop→is-contr-iff-inhabited A-prop =
  prop-ext is-contr-is-prop A-prop centre (is-prop∙→is-contr A-prop)

lift-inj
  : ∀ {ℓ ℓ'} {A : Type ℓ} {a b : A}
  → lift {ℓ = ℓ'} a ≡ lift {ℓ = ℓ'} b → a ≡ b
lift-inj p = ap lower p

-- Fibres of composites are given by pairs of fibres.
fibre-∘-≃
  : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
  → {f : B → C} {g : A → B}
  → ∀ c → fibre (f ∘ g) c ≃ (Σ[ (b , _) ∈ fibre f c ] fibre g b)
fibre-∘-≃ {f = f} {g = g} c = Iso→Equiv (fwd , iso bwd invl invr)
    where
      fwd : fibre (f ∘ g) c → Σ[ (b , _) ∈ fibre f c ] fibre g b
      fwd (a , p) = ((g a) , p) , (a , refl)

      bwd : Σ[ (b , _) ∈ fibre f c ] fibre g b → fibre (f ∘ g) c
      bwd ((b , p) , (a , q)) = a , ap f q ∙ p

      invl : ∀ x → fwd (bwd x) ≡ x
      invl ((b , p) , (a , q)) i .fst .fst = q i
      invl ((b , p) , (a , q)) i .fst .snd j =
        hcomp (∂ i ∨ ∂ j) λ where
          k (i = i0) → ∙-filler (ap f q) p k j
          k (i = i1) → p (j ∧ k)
          k (j = i0) → f (q i)
          k (j = i1) → p k
          k (k = i0) → f (q (i ∨ j))
      invl ((b , p) , a , q) i .snd .fst = a
      invl ((b , p) , a , q) i .snd .snd j = q (i ∧ j)

      invr : ∀ x → bwd (fwd x) ≡ x
      invr (a , p) i .fst = a
      invr (a , p) i .snd = ∙-idl p i

is-empty→≃ : ¬ A → ¬ B → A ≃ B
is-empty→≃ ¬a ¬b = is-empty→≃⊥ ¬a ∙e is-empty→≃⊥ ¬b e⁻¹
```
-->
