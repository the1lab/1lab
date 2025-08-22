---
description: |
  Lifting properties.
---

<!--
```agda
open import Cat.Instances.Shape.Interval
open import Cat.Morphism.Class
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Morphism.Lifts where
```

# Lifting properties of morphisms

<!--
```agda
private module Impl {o ℓ} {C : Precategory o ℓ} where
  open Precategory C
  private
    variable
      a b c d x y : ⌞ C ⌟
      f g h u v : Hom a b
```
-->

:::{.definition #lifting}
Let $f, g, u, v$ be a square of morphisms fitting into a commutative
square like so:

~~~{.quiver}
\[\begin{tikzcd}
  A && X \\
  \\
  B && {Y\text{.}}
  \arrow["f", from=1-1, to=1-3]
  \arrow["g", from=3-1, to=3-3]
  \arrow["u"', from=1-1, to=3-1]
  \arrow["v", from=1-3, to=3-3]
\end{tikzcd}\]
~~~

A **lifting** of such a square is a morphism $w : \cC(B, X)$ such
that $w \circ f = u$ and $g \circ w = v$.
:::

```agda
  Lifting
    : (f : Hom a b) (g : Hom x y) (u : Hom a x) (v : Hom b y)
    → Type _
  Lifting {a} {b} {x} {y} f g u v = Σ[ w ∈ Hom b x ] w ∘ f ≡ u × g ∘ w ≡ v
```

:::{.definition #lifting-property}
Let $L, R$ be two collections of morphisms of $\cC$. We say
that $L$ *left lifts against* $R$ and $R$ *right lifts against* $L$
if for every commutative square

~~~{.quiver}
\[\begin{tikzcd}
  A && X \\
  \\
  B && {Y\text{.}}
  \arrow["f", from=1-1, to=1-3]
  \arrow["g", from=3-1, to=3-3]
  \arrow["u"', from=1-1, to=3-1]
  \arrow["v", from=1-3, to=3-3]
\end{tikzcd}\]
~~~

with $f \in L$ and $g \in R4, there [[merely]] exists a lifting $w$.
:::

We can specialize this general definition in quite a few ways, so we will
make use of instance arguments to avoid a quadratic blowup of definitions.

```agda
  record Lifts-against
    {ℓl ℓr}
    (L : Type ℓl) (R : Type ℓr)
    (ℓp : Level)
    : Type (ℓl ⊔ ℓr ⊔ (lsuc ℓp)) where
    field
      lifting-prop : L → R → Type ℓp

  open Lifts-against

  Lifts
    : ∀ {ℓl ℓr ℓp} {L : Type ℓl} {R : Type ℓr}
    → L → R → ⦃ _ :  Lifts-against L R ℓp ⦄ → Type _
  Lifts l r ⦃ Lifts ⦄ = Lifts .lifting-prop l r
```

:::{.definition #lifts-against}
We say $f$ *lifts against* $g$ if there is a map assigning lifts to
every commutative squares with opposing $f$ and $g$ faces, as above.
This is a special case of a lifting property, where $L$ and $R$ are taken
to be singleton sets containing $f$ and $g$, resp.
:::

```agda
  instance
    Lifts-against-hom-hom : ∀ {a b x y} → Lifts-against (Hom a b) (Hom x y) ℓ
    Lifts-against-hom-hom .lifting-prop f g = ∀ u v → v ∘ f ≡ g ∘ u → ∥ Lifting f g u v ∥
```

We can also consider lifting against objects.

```agda
    Lifts-against-ob-hom : ∀ {x y} → Lifts-against Ob (Hom x y) ℓ
    Lifts-against-ob-hom {x} {y} .lifting-prop a f = ∀ (u : Hom a y) → ∥ Σ[ h ∈ Hom a x ] f ∘ h ≡ u ∥

    Lifts-against-hom-ob : ∀ {a b} → Lifts-against (Hom a b) Ob ℓ
    Lifts-against-hom-ob {a} {b} .lifting-prop f x = ∀ (u : Hom a x) → ∥ Σ[ h ∈ Hom b x ] h ∘ f ≡ u ∥
```

Finally, we can define general lifting properties against sets of morphisms
via instance resolution.

```agda
    Lifts-against-arrows-left
      : ∀ {ℓr ℓp κ} {R : Type ℓr}
      → ⦃ _ : ∀ {a b} → Lifts-against (Hom a b) R ℓp ⦄
      → Lifts-against (Arrows C κ) R (o ⊔ ℓ ⊔ ℓp ⊔ κ)
    Lifts-against-arrows-left .lifting-prop L r = ∀ {a b} → (f : Hom a b) → f ∈ L → Lifts f r

    Lifts-against-arrows-right
      : ∀ {ℓl ℓp κ} {L : Type ℓl}
      → ⦃ _ : ∀ {x y} → Lifts-against L (Hom x y) ℓp ⦄
      → Lifts-against L (Arrows C κ) (o ⊔ ℓ ⊔ ℓp ⊔ κ)
    Lifts-against-arrows-right .lifting-prop l R = ∀ {x y} → (f : Hom x y) → f ∈ R → Lifts l f
    {-# INCOHERENT Lifts-against-arrows-right #-}
```

<!--
```agda
open Impl hiding (Lifts; Lifting) public
private open module Reimpl {o ℓ} (C : Precategory o ℓ) = Impl {C = C} using (Lifts; Lifting) public
{-# DISPLAY Impl.Lifts {C = C} L R = Lifts C L R #-}
{-# DISPLAY Impl.Lifting {C = C} f g h k = Lifting C f g h k #-}

module _ {o ℓ} (C : Precategory o ℓ) where
  open Cat.Reasoning C
  private
    module Arr = Cat.Reasoning (Arr C)
    variable
      a b c d x y : ⌞ C ⌟
      f g h u v : Hom a b

```
-->

## Basic properties of liftings

[[Invertible]] morphisms have left and right liftings against all morphisms.

```agda
  invertible-left-lifts : Lifts C Isos g
  invertible-right-lifts : Lifts C f Isos
```

Consider a square like the one below with $f$ invertible.

~~~{.quiver}
\begin{tikzcd}
  A && X \\
  \\
  B && Y
  \arrow["u", from=1-1, to=1-3]
  \arrow["f"', from=1-1, to=3-1]
  \arrow["g", from=1-3, to=3-3]
  \arrow[dashed, from=3-1, to=1-3]
  \arrow["v"', from=3-1, to=3-3]
\end{tikzcd}
~~~

The composite $v \circ f^{-1}$ fits perfectly along the diagonal, and
some short calculations show that both triangles commute.

~~~{.quiver}
\begin{tikzcd}
  A && X \\
  \\
  B && Y
  \arrow["u", from=1-1, to=1-3]
  \arrow["f"', from=1-1, to=3-1]
  \arrow["g", from=1-3, to=3-3]
  \arrow["{u \circ f^{-1}}"{description}, dashed, from=3-1, to=1-3]
  \arrow["v"', from=3-1, to=3-3]
\end{tikzcd}
~~~

```agda
  invertible-left-lifts f f-inv u v vf=gu =
    pure (u ∘ f.inv , cancelr f.invr , pulll (sym vf=gu) ∙ cancelr f.invl)
    where
      module f = is-invertible f-inv
```

<details>
<summary>The proof for right lifts is formally dual.
</summary>

```agda
  invertible-right-lifts g g-inv u v vf=gu =
    pure (g.inv ∘ v , pullr vf=gu ∙ cancell g.invr , cancell g.invl)
    where
      module g = is-invertible g-inv
```
</details>

If both $f : \cC(B,C)$ and $g : \cC(A,B)$ left lift against some $h : \cC(X,Y)$,
then so does $f \circ g$.

```agda
  ∘l-lifts-against : Lifts C f h → Lifts C g h → Lifts C (f ∘ g) h
```

Showing that $f \circ g$ lifts against $h$ amounts to finding a diagonal
for the rectangle

~~~{.quiver}
\begin{tikzcd}
  A && X \\
  \\
  B \\
  \\
  C && Y
  \arrow["u", from=1-1, to=1-3]
  \arrow["g"', from=1-1, to=3-1]
  \arrow["h", from=1-3, to=5-3]
  \arrow["f"', from=3-1, to=5-1]
  \arrow["v"', from=5-1, to=5-3]
\end{tikzcd}
~~~

under the assumption that $v \circ f \circ g = h \circ u$. Our first move
is to re-orient the square and use $g$'s lifting property to find a map
$w : \cC(B,X)$ with $g \circ w = u$ and $v \circ f = h \circ w$.

~~~{.quiver}
\begin{tikzcd}
  A &&&& X \\
  \\
  B && C && Y
  \arrow["u", from=1-1, to=1-5]
  \arrow["g"', from=1-1, to=3-1]
  \arrow["h", from=1-5, to=3-5]
  \arrow["w"{description}, dashed, from=3-1, to=1-5]
  \arrow["f"', from=3-1, to=3-3]
  \arrow["v"', from=3-3, to=3-5]
\end{tikzcd}
~~~

The bottom triangle of the above diagram can be arranged as a square
with $f$ on the right and $h$ on the left, which lets us use $f$'s
lifting property to find a map $t : \cC(C,X)$.

If we place $t$ along the diagonal of our original square, we can see
that $t \circ f \circ g = w \circ g = u$ and $h \circ t = v$.

~~~{.quiver}
\begin{tikzcd}
  A && X \\
  \\
  B \\
  \\
  C && Y
  \arrow["u", from=1-1, to=1-3]
  \arrow["g"', from=1-1, to=3-1]
  \arrow["h", from=1-3, to=5-3]
  \arrow["w"{description}, dashed, from=3-1, to=1-3]
  \arrow["f"', from=3-1, to=5-1]
  \arrow["t"{description}, dashed, from=5-1, to=1-3]
  \arrow["v"', from=5-1, to=5-3]
\end{tikzcd}
~~~

```agda
  ∘l-lifts-against {f = f} f-lifts g-lifts u v vfg=hu = do
    (w , wg=u , hw=vf) ← g-lifts u (v ∘ f) (reassocl.from vfg=hu)
    (t , tf=w , ht=v)  ← f-lifts w v (sym hw=vf)
    pure (t , pulll tf=w ∙ wg=u , ht=v)
```

Dually, if $g : \cC(Y,Z)$ and $h : \cC(X,Y)$ both right lift against a
morphism $f$, then so does $g \circ h$.

```agda
  ∘r-lifts-against : Lifts C f g → Lifts C f h → Lifts C f (g ∘ h)
```

<details>
<summary>The proof follows the exact same trajectory as the left case,
so we will spare the reader the details.
</summary>
```agda
  ∘r-lifts-against {h = h} f-lifts g-lifts u v ve=fgu = do
    (w , we=gu , fw=v) ← f-lifts (h ∘ u) v (reassocr.to ve=fgu)
    (t , te=u , gt=w)  ← g-lifts u w we=gu
    pure (t , te=u , pullr gt=w ∙ fw=v)
```
</details>

For the next few lemmas, consider a square of the following form, where
$l$ and $k$ are both lifts of the outer square

~~~{.quiver}
\begin{tikzcd}
  a && b \\
  \\
  c && d.
  \arrow["f", from=1-1, to=1-3]
  \arrow["u"', from=1-1, to=3-1]
  \arrow["l"', shift right, from=1-3, to=3-1]
  \arrow["k", shift left, from=1-3, to=3-1]
  \arrow["v", from=1-3, to=3-3]
  \arrow["g"', from=3-1, to=3-3]
\end{tikzcd}
~~~

<!--
```agda
  ∘l-lifts-class : ∀ {κ} (R : Arrows C κ) → Lifts C f R → Lifts C g R → Lifts C (f ∘ g) R
  ∘l-lifts-class R f-lifts g-lifts r r∈R = ∘l-lifts-against (f-lifts r r∈R) (g-lifts r r∈R)

  ∘r-lifts-class : ∀ {κ} (L : Arrows C κ) → Lifts C L f → Lifts C L g → Lifts C L (f ∘ g)
  ∘r-lifts-class L f-lifts g-lifts l l∈L = ∘r-lifts-against (f-lifts l l∈L) (g-lifts l l∈L)
```
-->

If $f$ is an [[epimorphism]], then $l = k$. In more succinct terms, the
type of lifts of such a square is a proposition.

```agda
  left-epic→lift-is-prop
    : is-epic f → v ∘ f ≡ g ∘ u → is-prop (Lifting C f g u v)
  left-epic→lift-is-prop f-epi vf=gu (l , lf=u , _) (k , kf=u , _) =
    Σ-prop-path! (f-epi l k (lf=u ∙ sym kf=u))
```

Dually, if $g$ is a [[monomorphism]], then we the type of lifts is also
a proposition.

```agda
  right-monic→lift-is-prop
    : is-monic g → v ∘ f ≡ g ∘ u → is-prop (Lifting C f g u v)
  right-monic→lift-is-prop g-mono vf=gu (l , _ , gl=v) (k , _ , gk=v) =
    Σ-prop-path! (g-mono l k (gl=v ∙ sym gk=v))
```
