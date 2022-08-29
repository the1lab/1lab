```agda
open import Cat.Displayed.Base
open import Cat.Prelude

module Cat.Displayed.Cartesian
  {o ℓ o′ ℓ′} {B : Precategory o ℓ} (E : Displayed B o′ ℓ′) where

open Precategory B
open Displayed E
```

# Cartesian morphisms and Fibrations

While displayed categories give the essential framework we need to
express the idea of families of categories indexed by a category, they
do not _quite_ capture the concept precisely. The problem is that while
a category $\ca{E}$ displayed over $\ca{B}$ does indeed give a
_collection_ of fibre categories $\ca{E}^*(x)$, this assignment isn't
necessarily functorial!

More precisely, we should have that a collection of categories, indexed
by a category, should be a _pseudofunctor_ $\ca{B} \to \Cat$, where
$\Cat$ is a [bicategory] of categories. It turns out that we can
characterise this assignment entirely in terms of the displayed objects
and morphisms in $\ca{E}$!

[bicategory]: Cat.Bi.Base.html

Fix an arrow $f : a \to b$ in the base category $\ca{B}$, an object $a'$
over $a$ (resp. $b'$ over $b$), and an arrow $f' : a' \to_f b'$ over
$f$. We say that $f'$ is **cartesian** if, up to very strong handwaving,
it fits into a "pullback diagram". The barred arrows with triangle tips
here indicate the "projection" from a displayed object to its base, and
so are implicit in the type dependency.

~~~{.quiver}
\[\begin{tikzcd}
  {a'} && {b'} \\
  \\
  a && b
  \arrow["{f'}"', from=1-1, to=1-3]
  \arrow["f", from=3-1, to=3-3]
  \arrow[lies over, from=1-1, to=3-1]
  \arrow[lies over, from=1-3, to=3-3]
\end{tikzcd}\]
~~~

```agda
record
  Cartesian {a b a′ b′} (f : Hom a b) (f′ : Hom[ f ] a′ b′) : Type (o ⊔ ℓ ⊔ o′ ⊔ ℓ′)
  where
  no-eta-equality
```

More specifically, let $u : \ca{B}$ and $u'$ be over $u$, and suppose
that we have a map $m : u \to a$ (below, in violet), and a map $h' : u'
\to_m b'$ lying over the composite $fm$ (in red). The universal property
of a Cartesian map says that we have a universal factorisation of $h'$
through a map $u' \to a'$ (in green, marked $\exists!$).

~~~{.quiver .tall-2}
\[\begin{tikzcd}
  \textcolor{rgb,255:red,124;green,50;blue,189}{u'} \\
  & {a'} && {b'} \\
  \textcolor{rgb,255:red,124;green,50;blue,189}{u} \\
  & a && b
  \arrow["{f'}"', from=2-2, to=2-4]
  \arrow["f", from=4-2, to=4-4]
  \arrow[lies over, from=2-2, to=4-2]
  \arrow[lies over, from=2-4, to=4-4]
  \arrow["m"', color={rgb,255:red,124;green,50;blue,189}, from=3-1, to=4-2]
  \arrow[lies over, color={rgb,255:red,124;green,50;blue,189}, from=1-1, to=3-1]
  \arrow["{h'}", color={rgb,255:red,204;green,51;blue,51}, curve={height=-12pt}, from=1-1, to=2-4]
  \arrow["{\exists!}"', color={rgb,255:red,36;green,202;blue,28}, dashed, from=1-1, to=2-2]
\end{tikzcd}\]
~~~

```agda
  field
    universal : ∀ {u u′} (m : Hom u a) (h′ : Hom[ f ∘ m ] u′ b′) → Hom[ m ] u′ a′
    commutes  : ∀ {u u′} (m : Hom u a) (h′ : Hom[ f ∘ m ] u′ b′)
              → f′ ∘′ universal m h′ ≡ h′
    unique    : ∀ {u u′} {m : Hom u a} {h′ : Hom[ f ∘ m ] u′ b′}
              → (m′ : Hom[ m ] u′ a′) → f′ ∘′ m′ ≡ h′ → m′ ≡ universal m h′
```

Given a "right corner" like that of the diagram below, and note that the
input data consists of $a$, $b$, $f : a \to b$ and $b'$ over $a$,

~~~{.quiver}
\[\begin{tikzcd}
  && {b'} \\
  \\
  a && {b\text{,}}
  \arrow[lies over, from=1-3, to=3-3]
  \arrow["f"', from=3-1, to=3-3]
\end{tikzcd}\]
~~~

we call an object $a'$ over $a$ together with a Cartesian arrow $f' : a'
\to b'$ a _Cartesian lift_ of $f$. Cartesian lifts, defined by universal
property as they are, are unique when they exist, so that "having
Cartesian lifts" is a _property_, not a structure.

```agda
record
  Cartesian-lift {x y} (f : Hom x y) (y′ : Ob[ y ]) : Type (o ⊔ ℓ ⊔ o′ ⊔ ℓ′)
  where
  no-eta-equality
  field
    {x′}      : Ob[ x ]
    lifting   : Hom[ f ] x′ y′
    cartesian : Cartesian f lifting
  open Cartesian cartesian public
```

We note that the classical literature often differentiates between
_fibrations_ --- those displayed categories for which _there exist_
Cartesian lifts for every right corner --- and _cloven fibrations_,
those for which the Cartesian lifts are "algebraic" in a sense.  This is
because, classically, _essentially unique_ means that there are still
some choices to be made, and invoking the axiom of choice makes an
"arbitrary" set of such choices. But, in the presence of univalence,
there is exactly _one_ choice to be made, that is, no choice at all.
Thus, we do not dwell on the distinction.

```agda
record Cartesian-fibration : Type (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) where
  no-eta-equality
  field
    has-lift : ∀ {x y} (f : Hom x y) (y′ : Ob[ y ]) → Cartesian-lift f y′
```

A Cartesian fibration is a displayed category having Cartesian lifts for
every right corner.

## Why?

Admittedly, the notion of Cartesian morphism is slightly artificial. It
arises from studying the specific properties of the pullback functors
$f^* : \ca{C}/y \to \ca{C}/x$ which exist in a category of pullbacks,
hence the similarity in universal property!

In fact, the quintessential example of a Cartesian fibration is the
[_codomain fibration_], which is a category displayed over $\ca{C}$, where
the fibre over $x$ is the slice category $\ca{C}/x$. We may investigate
further (to uncover the name "codomain"): the total space of this
fibration is the arrow category $\id{Arr}(\ca{C})$, and the projection
functor is the codomain functor $\id{Arr}(\ca{C}) \to \ca{C}$.

[_codomain fibration_]: Cat.Displayed.Instances.Slice.html

This displayed category extends to a pseudofunctor exactly when $\ca{C}$
has all pullbacks, because in a world where the vertical arrows are
"_just_" arrows, a Cartesian morphism is exactly a pullback square.

Other examples exist:

- The [family fibration] exhibits any category $\ca{C}$ as displayed
over $\sets$. The fibres are functor categories (with discrete domains),
reindexing is given by composition.

[family fibration]: Cat.Displayed.Instances.Family.html

- The [category of modules] is fibred over the category of rings. The
fibre over a ring $R$ is the category of $R$-modules, Cartesian lifts
are given by restriction of scalars.

[category of modules]: Algebra.Ring.Module.html
