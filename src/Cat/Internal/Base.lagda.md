<!--
```agda
open import Cat.Diagram.Pullback
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Internal.Base {o ℓ} (C : Precategory o ℓ) where
```

<!--
```agda
open Cat.Reasoning C
```
-->

# Internal categories

We often think of categories as _places where we can do mathematics_.
This is done by translating definitions into the internal language of
some suitably structured class of categories, and then working within
that internal language to prove theorems.

This is all fine and good, but there is an obvious question: what
happens if we internalize the definition of a category? Such categories
are (unsurprisingly) called **internal categories**, and are quite
well-studied. The traditional definition goes as follows: Suppose $\cC$
is a category with [[pullbacks]], fix a pair of objects $\bC_0, \bC_1$
be a pair of objects, and parallel maps $\src, \tgt : \bC_1 \to \bC_0$.

[pullbacks]: Cat.Diagram.Pullback.html

The idea is that $\bC_0$ and $\bC_1$ are meant to be the "object of
objects" and "object of morphisms", respectively, while the maps
$\src$ and $\tgt$ assign each morphism to its domain and
codomain. A diagram $(\bC_0, \bC_1, \src, \tgt)$ is a _category
internal to $\cC$_ if it has an _identity-assigning morphism_ $i : \bC_0
\to \bC_1$ a _composition morphism_ $c : \bC_1 \times_{C_0} \bC_1 \to
\bC_1$, where the pullback --- given by the square below --- is the
_object of composable pairs_.

~~~{.quiver}
\begin{tikzcd}
  {C_1 \times_{C_0} C_1} && {C_1} \\
  \\
  {C_1} && {C_0}
  \arrow[from=1-1, to=1-3]
  \arrow[from=1-1, to=3-1]
  \arrow["tgt", from=1-3, to=3-3]
  \arrow["src"', from=3-1, to=3-3]
  \arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=1-1, to=3-3]
\end{tikzcd}
~~~

These must also satisfy left/right identity and associativity. The
associativity condition is given by the square below, and we trust that
the reader will understand why will not attempt to draw the identity
constraints.

~~~{.quiver .tall-15}
\begin{tikzcd}
  {C_1 \times_{C_0} (C_1 \times_{C_0} C_1)} &&& {C_1 \times_{C_0} C_1} \\
  \\
  \\
  {C_1 \times_{C_0} C_1} &&& {C_1}
  \arrow["{id \times c}"', from=1-1, to=4-1]
  \arrow["c"', from=4-1, to=4-4]
  \arrow["{\langle c \circ \langle \pi_1, \pi_1 \circ \pi_2 \rangle , \pi_2 \circ \pi_2\rangle}", from=1-1, to=1-4]
  \arrow["c", from=1-4, to=4-4]
\end{tikzcd}
~~~

Encoding this diagram in a proof assistant is a *nightmare*. Even
constructing the maps into $C_1 \times_{C_0} C_1$ we must speak about is
a pile of painful proof obligations, and these scale atrociously when
talking about iterated pullbacks.^[To be clear, we did not draw the
identity constraints because they are trivial. Rather, speaking
euphemistically, they are *highly nontrivial*.]

To solve the problem, we look to a simpler case: [internal monoids] in
$\cC$. These are straightforward to define in diagrammatic language, but
can also be defined [in terms of representability]! The core idea is
that we can define internal structure in the category of presheaves on
$\cC$, rather than directly in $\cC$, letting us us use the structure of
the meta-language to our advantage. To ensure that the structure defined
in presheaves can be internalized to $\cC$, we restrict ourselves to
working with [representable] presheaves --- which is equivalent to $\cC$
by the [Yoneda lemma].

[internal monoids]: Cat.Monoidal.Diagram.Monoid.html
[in terms of representability]: Cat.Monoidal.Diagram.Monoid.Representable.html
[representable]: Cat.Functor.Hom.Representable.html
[Yoneda lemma]: Cat.Functor.Hom.html

From a type theoretic point of view, this is akin to defining structure
relative to an arbitrary context $\Gamma$, rather than in the smallest
context possible. This relativisation introduces a new proof obligation:
stability under *substitution*. We have to ensure that we have defined
the same structure in every context, which translates to a naturality
condition.

## Representing internal morphisms

Let $\cC$ be a category, and $(\bC_0, \bC_1, \src, \tgt)$ be a diagram
as before. We will define **internal morphisms** between _generalised
objects_ $x, y : \Gamma \to \bC_0$ to be morphisms $f : \Gamma \to C_1$
making the following diagram commute.

~~~{.quiver .tall-15}
\begin{tikzcd}
  & \Gamma \\
  \\
  & {C_1} \\
  {C_0} && {C_0}
  \arrow["hom"{description}, from=1-2, to=3-2]
  \arrow["x"', curve={height=6pt}, from=1-2, to=4-1]
  \arrow["y", curve={height=-6pt}, from=1-2, to=4-3]
  \arrow["src"{description}, from=3-2, to=4-1]
  \arrow["tgt"{description}, from=3-2, to=4-3]
\end{tikzcd}
~~~

```agda
record Internal-hom
  {C₀ C₁ Γ : Ob}
  (src tgt : Hom C₁ C₀) (x y : Hom Γ C₀)
  : Type ℓ where
  no-eta-equality
  field
    ihom : Hom Γ C₁
    has-src : src ∘ ihom ≡ x
    has-tgt : tgt ∘ ihom ≡ y

open Internal-hom
```

This definition may seem somewhat odd, but we again stress that we are
working in the internal language of $\cC$, where it reads as the
following typing rule:

$$
\frac{
  \Gamma \vdash x : C_0\quad
  \Gamma \vdash y : C_0\quad
  \Gamma \vdash f : C_1\quad
  \src f \equiv x\quad
  \tgt f \equiv y\quad
}{
  \Gamma \vdash f : \hom\ x\ y
}
$$


<!--
```agda
Internal-hom-pathp
  : ∀ {C₀ C₁ Γ} {src tgt : Hom C₁ C₀} {x x' y y' : Hom Γ C₀}
  → {f : Internal-hom src tgt x y} {g : Internal-hom src tgt x' y'}
  → (p : x ≡ x') (q : y ≡ y')
  → f .ihom ≡ g .ihom
  → PathP (λ i → Internal-hom src tgt (p i) (q i)) f g
Internal-hom-pathp p q r i .ihom = r i
Internal-hom-pathp {src = src} {f = f} {g = g} p q r i .has-src =
  is-prop→pathp (λ i → Hom-set _ _ (src ∘ r i) (p i)) (f .has-src) (g .has-src) i
Internal-hom-pathp {tgt = tgt} {f = f} {g = g} p q r i .has-tgt =
  is-prop→pathp (λ i → Hom-set _ _ (tgt ∘ r i) (q i)) (f .has-tgt) (g .has-tgt) i

Internal-hom-path
  : ∀ {C₀ C₁ Γ} {src tgt : Hom C₁ C₀} {x y : Hom Γ C₀}
  → {f g : Internal-hom src tgt x y}
  → f .ihom ≡ g .ihom
  → f ≡ g
Internal-hom-path p = Internal-hom-pathp refl refl p

private unquoteDecl eqv = declare-record-iso eqv (quote Internal-hom)

Internal-hom-set
  : ∀ {Γ C₀ C₁} {src tgt : Hom C₁ C₀} {x y : Hom Γ C₀}
  → is-set (Internal-hom src tgt x y)
Internal-hom-set = Iso→is-hlevel 2 eqv hlevel!

instance
  H-Level-Internal-hom
    : ∀ {Γ C₀ C₁} {src tgt : Hom C₁ C₀} {x y : Hom Γ C₀} {n}
    → H-Level (Internal-hom src tgt x y) (2 + n)
  H-Level-Internal-hom = basic-instance 2 Internal-hom-set

_ihomₚ
  : ∀ {C₀ C₁ Γ} {src tgt : Hom C₁ C₀} {x y : Hom Γ C₀}
  → {f g : Internal-hom src tgt x y}
  → f ≡ g
  → f .ihom ≡ g .ihom
_ihomₚ = ap ihom

infix -1 _ihomₚ

adjusti
    : ∀ {Γ C₀ C₁} {src tgt : Hom C₁ C₀} {x x' y y' : Hom Γ C₀}
  → x ≡ x' → y ≡ y' → Internal-hom src tgt x y → Internal-hom src tgt x' y'
adjusti p q f .ihom = f .ihom
adjusti p q f .has-src = f .has-src ∙ p
adjusti p q f .has-tgt = f .has-tgt ∙ q
```
-->

We also must define the action of substitutions $\Delta \to \Gamma$ on
internal morphisms. Zooming out to look at $\cC$, substitutions are
morphisms $\cC(\Gamma, \Delta)$, and act on internal morphisms by
precomposition.

```agda
_[_] : ∀ {C₀ C₁ Γ Δ} {src tgt : Hom C₁ C₀} {x y : Hom Δ C₀}
     → Internal-hom src tgt x y
     → (σ : Hom Γ Δ)
     → Internal-hom src tgt (x ∘ σ) (y ∘ σ)
(f [ σ ]) .ihom = f .ihom ∘ σ
(f [ σ ]) .has-src = pulll (f .has-src)
(f [ σ ]) .has-tgt = pulll (f .has-tgt)

infix 50 _[_]
```

That out of the way, we can define internal categories _in terms of_
their internal morphisms.

```agda
record Internal-cat-on {C₀ C₁} (src tgt : Hom C₁ C₀) : Type (o ⊔ ℓ) where
  no-eta-equality
  field
    idi : ∀ {Γ} → (x : Hom Γ C₀) → Internal-hom src tgt x x
    _∘i_ : ∀ {Γ} {x y z : Hom Γ C₀}
         → Internal-hom src tgt y z → Internal-hom src tgt x y
         → Internal-hom src tgt x z

  infixr 40 _∘i_
```

Having rewritten the pullbacks from before --- where the previous
attempt at a definition ended --- in terms of dependency in the
meta-language, we can state the laws of an internal category completely
analogously to their external counterparts!

```agda
  field
    idli : ∀ {Γ} {x y : Hom Γ C₀} (f : Internal-hom src tgt x y)
         → idi y ∘i f ≡ f
    idri : ∀ {Γ} {x y : Hom Γ C₀} (f : Internal-hom src tgt x y)
         → f ∘i idi x ≡ f
    associ : ∀ {Γ} {w x y z : Hom Γ C₀}
           → (f : Internal-hom src tgt y z)
           → (g : Internal-hom src tgt x y)
           → (h : Internal-hom src tgt w x)
           → f ∘i g ∘i h ≡ (f ∘i g) ∘i h
```

However, we do need to add the stability conditions, ensuring that we
have _the same_ internal category structure, even when moving between
contexts.

```agda
    idi-nat : ∀ {Γ Δ} {x : Hom Δ C₀} (σ : Hom Γ Δ)
            → idi x [ σ ] ≡ idi (x ∘ σ)
    ∘i-nat : ∀ {Γ Δ} {x y z : Hom Δ C₀}
           → (f : Internal-hom src tgt y z) (g : Internal-hom src tgt x y)
           → (σ : Hom Γ Δ) → (f ∘i g) [ σ ] ≡ (f [ σ ] ∘i g [ σ ])
```

We also provide a _bundled_ definition, letting us talk about arbitrary
categories internal to $\cC$.

```agda
record Internal-cat : Type (o ⊔ ℓ) where
  field
    C₀ C₁ : Ob
    src tgt : Hom C₁ C₀
    has-internal-cat : Internal-cat-on src tgt

  open Internal-cat-on has-internal-cat public

  Homi : ∀ {Γ} (x y : Hom Γ C₀) → Type ℓ
  Homi x y = Internal-hom src tgt x y
```

<!--
```agda
  homi : ∀ {Γ} (f : Hom Γ C₁) → Homi (src ∘ f) (tgt ∘ f)
  homi f .ihom = f
  homi f .has-src = refl
  homi f .has-tgt = refl

  homi-nat : ∀ {Γ Δ} (f : Hom Δ C₁) → (σ : Hom Γ Δ)
    → homi f [ σ ] ≡ adjusti (assoc _ _ _) (assoc _ _ _) (homi (f ∘ σ))
  homi-nat f σ = Internal-hom-path refl

-- Some of the naturality conditions required for later definitions will
-- require the use of `PathP`{.agda}, which messes up our equational
-- reasoning machinery. To work around this, we define some custom
-- equational reasoning combinators for working with internal homs.

  casti : ∀ {Γ} {x x' y y' : Hom Γ C₀} {f : Homi x y} {g : Homi x' y'}
        → {p p' : x ≡ x'} {q q' : y ≡ y'}
        → PathP (λ i → Homi (p i) (q i)) f g
        → PathP (λ i → Homi (p' i) (q' i)) f g
  casti {Γ = Γ} {x} {x'} {y} {y'} {f} {g} {p} {p'} {q} {q'} r =
    transport (λ i →
      PathP
        (λ j → Homi (Hom-set Γ C₀ x x' p p' i j) ( Hom-set Γ C₀ y y' q q' i j))
        f g) r

  begini_ : ∀ {Γ} {x x' y y' : Hom Γ C₀} {f : Homi x y} {g : Homi x' y'}
        → {p p' : x ≡ x'} {q q' : y ≡ y'}
        → PathP (λ i → Homi (p i) (q i)) f g
        → PathP (λ i → Homi (p' i) (q' i)) f g
  begini_ = casti

  _∙i_
    : ∀ {Γ} {x x' x'' y y' y'' : Hom Γ C₀}
    → {f : Homi x y} {g : Homi x' y'} {h : Homi x'' y''}
    → {p : x ≡ x'} {q : y ≡ y'} {p' : x' ≡ x''} {q' : y' ≡ y''}
    → PathP (λ i → Homi (p i) (q i)) f g
    → PathP (λ i → Homi (p' i) (q' i)) g h
    → PathP (λ i → Homi ((p ∙ p') i) ((q ∙ q') i)) f h
  _∙i_ {x = x} {x'} {x''} {y} {y'} {y''} {f} {g} {h} {p} {q} {p'} {q'} r r' i =
    comp (λ j → Homi (∙-filler p p' j i) (∙-filler q q' j i)) (∂ i) λ where
      j (i = i0) → f
      j (i = i1) → r' j
      j (j = i0) → r i

  ≡i⟨⟩-syntax
    : ∀ {Γ} {x x' x'' y y' y'' : Hom Γ C₀}
    → (f : Homi x y) {g : Homi x' y'} {h : Homi x'' y''}
    → {p : x ≡ x'} {q : y ≡ y'} {p' : x' ≡ x''} {q' : y' ≡ y''}
    → PathP (λ i → Homi (p' i) (q' i)) g h
    → PathP (λ i → Homi (p i) (q i)) f g
    → PathP (λ i → Homi ((p ∙ p') i) ((q ∙ q') i)) f h
  ≡i⟨⟩-syntax f r' r = r ∙i r'

  _≡i˘⟨_⟩_
    : ∀ {Γ} {x x' x'' y y' y'' : Hom Γ C₀}
    → (f : Homi x y) {g : Homi x' y'} {h : Homi x'' y''}
    → {p : x' ≡ x} {q : y' ≡ y} {p' : x' ≡ x''} {q' : y' ≡ y''}
    → PathP (λ i → Homi (p i) (q i)) g f
    → PathP (λ i → Homi (p' i) (q' i)) g h
    → PathP (λ i → Homi ((sym p ∙ p') i) ((sym q ∙ q') i)) f h
  _≡i˘⟨_⟩_ f r r'  = symP r ∙i r'

  syntax ≡i⟨⟩-syntax f r' r = f ≡i⟨ r ⟩ r'

  infixr 30 _∙i_
  infix 1 begini_
  infixr 2 ≡i⟨⟩-syntax _≡i˘⟨_⟩_
```
-->

### Where did the pullbacks go?

After seeing the definition above, the reader may be slightly concerned:
we make no reference to pullbacks, or to limits in $\cC$, at all! How in
the world can this be the same as the textbook definition?

The pullbacks in $\cC$ enter the stage when we want to move our internal
category structure, which is relative to arbitrary contexts $\Gamma$, to
the _smallest possible context_. To start, we note that internalizing
the identity morphism can be done by looking instantiating `idi`{.Agda}
at the identity morphism.

```agda
private module _ (pbs : has-pullbacks C) (ℂ : Internal-cat) where
  open Internal-cat ℂ
  open Pullbacks C pbs
  open pullback

  internal-id : Hom C₀ C₁
  internal-id = idi id .ihom
```

Now let's see composition: enter, stage rights, the pullbacks. we define
$\bC_2$ to be the _object of composable pairs_ --- the first pullback
square we gave, intersecting on compatible source and target. By
translating the (internal) pullback square to (external) indexing, we
have a pair of internal morphisms that can be composed.

```agda
  C₂ : Ob
  C₂ = Pb src tgt

  internal-comp : Hom C₂ C₁
  internal-comp = (f ∘i g) .ihom where
    f : Homi (src ∘ p₁ src tgt) (tgt ∘ p₁ src tgt)
    f .ihom = p₁ src tgt
    f .has-src = refl
    f .has-tgt = refl

    g : Homi (src ∘ p₂ src tgt) (src ∘ p₁ src tgt)
    g .ihom = p₂ src tgt
    g .has-src = refl
    g .has-tgt = sym $ square src tgt
```

## Internal functors

We will now start our project of relativisng category theory to
arbitrary bases. Suppose $\ica{C}, \ica{D}$ are internal categories:
what are the maps between them? Reasoning diagrammatically, they are the
morphisms between object-objects and morphism-objects that preserve
source, target, commute with identity, and commute with composition.


<!--
```agda
record Internal-functor (ℂ 𝔻 : Internal-cat) : Type (o ⊔ ℓ) where
  no-eta-equality
  private
    module ℂ = Internal-cat ℂ
    module 𝔻 = Internal-cat 𝔻
```
-->

Now thinking outside $\cC$, an **internal functor** $\ica{C} \to
\ica{D}$ consists of a family of maps between internal objects, together
with a dependent function between internal morphisms --- exactly as in
the external case! With that indexing, the functoriality constraints
_also_ look identical.

```agda
  field
    Fi₀ : ∀ {Γ} → Hom Γ ℂ.C₀ → Hom Γ 𝔻.C₀
    Fi₁ : ∀ {Γ} {x y : Hom Γ ℂ.C₀} → ℂ.Homi x y → 𝔻.Homi (Fi₀ x) (Fi₀ y)

    Fi-id : ∀ {Γ} {x : Hom Γ ℂ.C₀}
          → Fi₁ (ℂ.idi x) ≡ 𝔻.idi (Fi₀ x)
    Fi-∘  : ∀ {Γ} {x y z : Hom Γ ℂ.C₀}
          → (f : ℂ.Homi y z) (g : ℂ.Homi x y)
          → Fi₁ (f ℂ.∘i g) ≡ Fi₁ f 𝔻.∘i Fi₁ g
```

However, do not forget the naturality conditions. Since we now have a
"dependent function" between internal morphism spaces, _its_
substitution stability depends on stability for the mapping between
objects.

```agda
    Fi₀-nat : ∀ {Γ Δ} (x : Hom Δ ℂ.C₀)
            → (σ : Hom Γ Δ)
            → Fi₀ x ∘ σ ≡ Fi₀ (x ∘ σ)
    Fi₁-nat : ∀ {Γ Δ} {x y : Hom Δ ℂ.C₀}
            → (f : ℂ.Homi x y)
            → (σ : Hom Γ Δ)
            → PathP (λ i → 𝔻.Homi (Fi₀-nat x σ i) (Fi₀-nat y σ i))
                (Fi₁ f [ σ ]) (Fi₁ (f [ σ ]))

open Internal-functor
```

### Internal functor composition

<!--
```agda
module _ {ℂ 𝔻 𝔼 : Internal-cat} where
  private
    module ℂ = Internal-cat ℂ
    module 𝔻 = Internal-cat 𝔻
    module 𝔼 = Internal-cat 𝔼
```
-->

As a demonstration of the power of these definitions, we can define
composition of internal functors, which --- at the risk of sounding like
a broken record --- mirrors the external definition exactly.

```agda
  _Fi∘_ : Internal-functor 𝔻 𝔼 → Internal-functor ℂ 𝔻 → Internal-functor ℂ 𝔼
  (F Fi∘ G) .Fi₀ x = F .Fi₀ (G .Fi₀ x)
  (F Fi∘ G) .Fi₁ f = F .Fi₁ (G .Fi₁ f)
  (F Fi∘ G) .Fi-id = ap (F .Fi₁) (G .Fi-id) ∙ F .Fi-id
  (F Fi∘ G) .Fi-∘ f g = ap (F .Fi₁) (G .Fi-∘ f g) ∙ F .Fi-∘ _ _
  (F Fi∘ G) .Fi₀-nat x σ = F .Fi₀-nat (G .Fi₀ x) σ ∙ ap (F .Fi₀) (G .Fi₀-nat x σ)
  (F Fi∘ G) .Fi₁-nat f σ =
    F .Fi₁-nat (G .Fi₁ f) σ 𝔼.∙i (λ i → F .Fi₁ (G .Fi₁-nat f σ i))

  infixr 30 _Fi∘_
```

There is also an internal version of the identity functor.

```agda
Idi : ∀ {ℂ : Internal-cat} → Internal-functor ℂ ℂ
Idi .Fi₀ x = x
Idi .Fi₁ f = f
Idi .Fi-id = refl
Idi .Fi-∘ _ _ = refl
Idi .Fi₀-nat _ _ = refl
Idi .Fi₁-nat _ _ = refl
```

## Internal natural transformations

Internal natural transformations follow the same pattern: we replace
objects with generalized objects, morphisms with internal morphisms, and
attach a condition encoding stability under substitution. Here again we
must state stability _over_ another stability condition.

<!--
```agda
record _=>i_
  {ℂ 𝔻 : Internal-cat}
  (F G : Internal-functor ℂ 𝔻)
  : Type (o ⊔ ℓ) where
  no-eta-equality
  private
    module ℂ = Internal-cat ℂ
    module 𝔻 = Internal-cat 𝔻
```
-->

```agda
  field
    ηi : ∀ {Γ} (x : Hom Γ ℂ.C₀) → 𝔻.Homi (F .Fi₀ x) (G .Fi₀ x)
    is-naturali : ∀ {Γ} (x y : Hom Γ ℂ.C₀) (f : ℂ.Homi x y)
                → ηi y 𝔻.∘i F .Fi₁ f ≡ G .Fi₁ f 𝔻.∘i ηi x
    ηi-nat : ∀ {Γ Δ} (x : Hom Δ ℂ.C₀)
           → (σ : Hom Γ Δ)
           → PathP (λ i → 𝔻.Homi (F .Fi₀-nat x σ i) (G .Fi₀-nat x σ i))
               (ηi x [ σ ]) (ηi (x ∘ σ))

infix 20 _=>i_
open _=>i_
```

<!--
```agda
module _ {ℂ 𝔻 : Internal-cat} {F G : Internal-functor ℂ 𝔻} where
  private
    module ℂ = Internal-cat ℂ
    module 𝔻 = Internal-cat 𝔻

  Internal-nat-path
    : {α β : F =>i G}
    → (∀ {Γ} (x : Hom Γ ℂ.C₀) → α .ηi x ≡ β .ηi x)
    → α ≡ β
  Internal-nat-path {α} {β} p i .ηi x = p x i
  Internal-nat-path {α} {β} p i .is-naturali x y f =
    is-prop→pathp (λ i → Internal-hom-set (p y i 𝔻.∘i F .Fi₁ f) (G .Fi₁ f 𝔻.∘i p x i))
      (α .is-naturali x y f)
      (β .is-naturali x y f) i
  Internal-nat-path {α} {β} p i .ηi-nat x σ =
    is-set→squarep (λ i j → Internal-hom-set)
      (λ i → p x i [ σ ])
      (α .ηi-nat x σ)
      (β .ηi-nat x σ)
      (λ i → p (x ∘ σ) i) i

  private unquoteDecl nat-eqv = declare-record-iso nat-eqv (quote _=>i_)

  Internal-nat-set : is-set (F =>i G)
  Internal-nat-set = Iso→is-hlevel 2 nat-eqv $
    Σ-is-hlevel 2 hlevel! $ λ _ →
    Σ-is-hlevel 2 hlevel! $ λ _ →
    Π-is-hlevel²' 2 λ _ _ →
    Π-is-hlevel 2 λ _ → Π-is-hlevel 2 λ _ →
    PathP-is-hlevel 2 Internal-hom-set

instance
  H-Level-Internal-nat
    : ∀ {ℂ 𝔻 : Internal-cat} {F G : Internal-functor ℂ 𝔻} {n}
    → H-Level (F =>i G) (2 + n)
  H-Level-Internal-nat = basic-instance 2 Internal-nat-set
```
-->
