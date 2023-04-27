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

# Internal Categories

We often think of categories as "places where we can do mathematics".
This is done by translating definitions into the internal language of
some suitably structured class of categories, and then working within
that internal language to prove theorems.

This is all fine and good, but there is an obvious question: what happens
if we internalize the definition of a category? Such categories are
(unsurprisingly) called *internal categories*, and are quite well-studied.
The traditional definition goes as follows: Let $\cC$ have pullbacks,
let $(C_0, C_1)$ be a pair of objects, and let $src, tgt : C_1 \to C_0$
be a pair of parallel morphisms.

The idea here is that $C_0$ and $C_1$ are meant to be the
"object of objects" and "object of morphisms", resp. The $src$ and $tgt$
maps do what their names suggest, mapping each morphism to it's domain
and codomain. We say a diagram $(C_0, C_1, src, tgt)$ is an internal
category in $\cC$ if it has an internal identity morphism
$i : C_0 \to C_1$ and internal composition operator
$c : C_1 \times_{C_0} C_1 \to C_1$. The pullback in the domain of the
composite morphism ensures that the domain and codomain of the 2
morphisms match, and is given by the following pullback square.

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

We also impose equations for left/right identity and associativity,
though we only show the associativity condition for reasons that shall
become painfully clear.

~~~{.quiver}
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

Encoding this diagram is a *nightmare* in a proof assistant; the we have
a mountain of proof obligations to be able to form maps into
$C_1 \times_{C_0} C_1$, and there are all sorts of horrifying
reassociations required for iterated pullbacks. Clearly, we need a
different definition.

To solve the problem, we look to a simpler case: [internal monoids] in
$\cC$. These are straightforward to define in diagramatic language, but
can also be defined [in terms of representability]! The core idea here is
that we can define internal structure in the category of presheaves on
$\cC$ instead of in $\cC$ directly, letting us us use the structure of
the meta-language to our advantage. To ensure that the structure defined
in presheaves can be internalized to $\cC$, we restrict ourselves to
working with [representable] presheaves, which is equivalent to $\cC$
by the [Yoneda lemma].

[internal monoids]: Cat.Monoidal.Diagram.Monoid.html
[in terms of representability]: Cat.Monoidal.Diagram.Monoid.Representable.html
[representable]: Cat.Functor.Hom.Representable.html
[Yoneda lemma]: Cat.Functor.Hom.html

From a type theoretic point of view, this is akin to defining structure
relative to an arbitrary context $\Gamma$, rather than in the smallest
context possible. However, we need to ensure that we have defined the
same structure in every context, IE: it needs to be stable under
substitutions. We encode this categorically via a naturality condition.

## Internal Morphisms

Let $\cC$ be a category, and $(C_0, C_1, src, tgt)$ be a diagram as
before. Furthermore, let $x, y: \Gamma \to C_0$ be 2 generalized objects
of $C_0$. We define an internal morphism from $x$ to $y$ to be a
generalized object $f : \Gamma \to C_1$ that makes the following diagram
commute.

~~~{.quiver}
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
  src(f) \equiv x\quad
  tgt(f) \equiv y\quad
}{
  \Gamma \vdash f : Hom\ x\ y
}
$$


<!--
```agda
Internal-hom-path
  : ∀ {C₀ C₁ Γ} {src tgt : Hom C₁ C₀} {x y : Hom Γ C₀}
  → {f g : Internal-hom src tgt x y}
  → f .ihom ≡ g .ihom
  → f ≡ g
Internal-hom-path p i .ihom = p i
Internal-hom-path {src = src} {f = f} {g = g} p i .has-src =
  is-prop→pathp (λ i → Hom-set _ _ (src ∘ p i) _) (f .has-src) (g .has-src) i
Internal-hom-path {tgt = tgt} {f = f} {g = g} p i .has-tgt =
  is-prop→pathp (λ i → Hom-set _ _ (tgt ∘ p i) _) (f .has-tgt) (g .has-tgt) i

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
```
-->

We also must define the action of substitutions $\Delta \to \Gamma$ on
internal morphisms. In the external view of $\cC$, substitutions are
morphisms $\cC(\Gamma, \Delta)$, and act via precomposition.

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

With this piece of machinery out of the way, we can proceed to define
internal categories in terms of internal morphisms.

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

The equations are *much* easier to state in this form.

```agda
  field
    idli : ∀ {Γ} {x y : Hom Γ C₀} → (f : Internal-hom src tgt x y)
         → ((idi y) ∘i f) .ihom ≡ f .ihom
    idri : ∀ {Γ} {x y : Hom Γ C₀} → (f : Internal-hom src tgt x y)
         → (f ∘i (idi x)) .ihom ≡ f .ihom
    associ : ∀ {Γ} {w x y z : Hom Γ C₀}
           → (f : Internal-hom src tgt y z)
           → (g : Internal-hom src tgt x y)
           → (h : Internal-hom src tgt w x)
           → (f ∘i (g ∘i h)) .ihom ≡ ((f ∘i g) ∘i h) .ihom
```

However, we do need to add naturality conditions; from the perspective
of the internal language, this requires that the category structure on
$(C_0, C_1)$ be stable under substitution.

```agda
    idi-nat : ∀ {Γ Δ} {x : Hom Δ C₀}
            → (σ : Hom Γ Δ)
            → (idi x .ihom ∘ σ) ≡ idi (x ∘ σ) .ihom
    ∘i-nat : ∀ {Γ Δ} {x y z : Hom Δ C₀}
           → (f : Internal-hom src tgt y z) (g : Internal-hom src tgt x y)
           → (σ : Hom Γ Δ)
           → (f ∘i g) .ihom ∘ σ ≡ (f [ σ ] ∘i g [ σ ]) .ihom
```

We also provide a bundled definition.

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

### Where did the pullbacks go?

Note that the above definition doesn't reference pullbacks at all! This
may seem somewhat alarming: how on earth is our definition the same
as the traditional one? The catch is that $\cC$ must have pullbacks for
us to actually internalize the external category structure. To start,
we note that internalizing the identity morphism can be done by looking
instantiating `idi`{.Agda} to the identity morphism.

```agda
private module _ (pbs : has-pullbacks C) (ℂ : Internal-cat) where
  open Internal-cat ℂ
  open Pullbacks C pbs
  open pullback

  internal-id : Hom C₀ C₁
  internal-id = idi id .ihom
```

Composition is where the pullbacks are required. First, we define
$C_2$ to be the pullback mentioned above, where the source and target
must agree. We can then internalize the composition operation by using
the first and second projections of the pullback.

```agda
  C₂ : Ob
  C₂ = Pb src tgt

  internal-comp : Hom C₂ C₁
  internal-comp = (f ∘i g) .ihom
    where
      f : Homi (src ∘ p₁ src tgt) (tgt ∘ p₁ src tgt)
      f .ihom = p₁ src tgt
      f .has-src = refl
      f .has-tgt = refl

      g : Homi (src ∘ p₂ src tgt) (src ∘ p₁ src tgt)
      g .ihom = p₂ src tgt
      g .has-src = refl
      g .has-tgt = sym $ square src tgt
```


## Internal Functors

Let $\ica{C}, \ica{D}$ be internal categories. An *internal functor*
$\ica{C} \to \ica{D}$ consists of an internal mapping of objects,
along with an internal mapping of internal morphisms.

```agda
record Internal-functor (ℂ 𝔻 : Internal-cat) : Type (o ⊔ ℓ) where
  no-eta-equality
  private
    module ℂ = Internal-cat ℂ
    module 𝔻 = Internal-cat 𝔻
  field
    Fi₀ : ∀ {Γ} → Hom Γ ℂ.C₀ → Hom Γ 𝔻.C₀
    Fi₁ : ∀ {Γ} {x y : Hom Γ ℂ.C₀} → ℂ.Homi x y → 𝔻.Homi (Fi₀ x) (Fi₀ y)
```

These mappings must satisfy internal versions of the functoriality
conditions.

```agda
    Fi-id : ∀ {Γ} {x : Hom Γ ℂ.C₀}
          → Fi₁ (ℂ.idi x) .ihom ≡ 𝔻.idi (Fi₀ x) .ihom
    Fi-∘  : ∀ {Γ} {x y z : Hom Γ ℂ.C₀}
          → (f : ℂ.Homi y z) (g : ℂ.Homi x y)
          → Fi₁ (f ℂ.∘i g) .ihom ≡ (Fi₁ f 𝔻.∘i Fi₁ g) .ihom
```

We also need naturality conditions.

```agda
    Fi₀-nat : ∀ {Γ Δ} {x : Hom Δ ℂ.C₀}
            → (σ : Hom Γ Δ)
            → Fi₀ x ∘ σ ≡ Fi₀ (x ∘ σ)
    Fi₁-nat : ∀ {Γ Δ} {x y : Hom Δ ℂ.C₀}
            → (f : ℂ.Homi x y)
            → (σ : Hom Γ Δ)
            → Fi₁ f .ihom ∘ σ ≡ Fi₁ (f [ σ ]) .ihom
```

## Internal natural transformations

Internal natural transformations follow the same pattern: we replace
objects with generalized objects, homs with internal homs, and tack
on naturality conditions to ensure that the operations are stable under
substitution.

```agda
open Internal-functor

record _=>i_
  {ℂ 𝔻 : Internal-cat}
  (F G : Internal-functor ℂ 𝔻)
  : Type (o ⊔ ℓ) where
  no-eta-equality
  private
    module ℂ = Internal-cat ℂ
    module 𝔻 = Internal-cat 𝔻
  field
    ηi : ∀ {Γ} (x : Hom Γ ℂ.C₀) → 𝔻.Homi (F .Fi₀ x) (G .Fi₀ x)
    is-naturali : ∀ {Γ} (x y : Hom Γ ℂ.C₀) (f : ℂ.Homi x y)
                → (ηi y 𝔻.∘i F .Fi₁ f) .ihom ≡ (G .Fi₁ f 𝔻.∘i ηi x) .ihom
    ηi-nat : ∀ {Γ Δ} {x : Hom Δ ℂ.C₀}
           → (σ : Hom Γ Δ)
           → ηi x .ihom ∘ σ ≡ ηi (x ∘ σ) .ihom
```
