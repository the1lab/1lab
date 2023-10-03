<!--
```agda
open import Cat.Diagram.Pullback
open import Cat.Diagram.Terminal
open import Cat.Prelude hiding (Ω ; true)

import Cat.Displayed.Instances.Subobjects as Subobjs
import Cat.Reasoning
```
-->

```agda
module Cat.Diagram.Subobject where
```

# Subobject classifiers

In an arbitrary category $\cC$, a [[subobject]] of $X$ is, colloquially
speaking, given by a monomorphism $m : A \mono X$. Formally, though, we
must consider the object $A$ to be part of this data, since we can only
speak of morphisms if we already know their domain and codomain. The
generality in the definition means that the notion of subobject applies
to completely arbitrary $\cC$, but in completely arbitrary situations,
the notion might be _very_ badly behaved.

There are several observations we can make about $\cC$ that "tame" the
behaviour of $\Sub_{\cC}(X)$. For example, if it has [[pullbacks]], then
$\Sub(-)$ is a [[fibration]], so that there is a universal way of
re-indexing a subobject $x : \Sub(X)$ along a morphism $f : Y \to X$,
and if it has [[images]], it's even a [[bifibration]], so that each of
these reindexings has a [[left adjoint]], giving an interpretation of
existential quantifiers. If $\cC$ is a [[regular category]], existential
quantifiers and substitution commute, restricting the behaviour of
subobjects even further.

However, there is one assumption we can make about $\cC$ that rules them
all: it has a **generic subobject**, so that $\Sub(X)$ is equivalent to
a given $\hom$-set in $\cC$. A generic subobject is a morphism $\top : 1
\to \Omega$ so that, for any a subobject $m : A \mono X$, there is a
_unique_ arrow $\name{m}$ making the square

~~~{.quiver}
\[\begin{tikzcd}[ampersand replacement=\&]
  A \&\& 1 \\
  \\
  X \&\& \Omega
  \arrow["{!}", from=1-1, to=1-3]
  \arrow["\top", from=1-3, to=3-3]
  \arrow["{\name{m}}"', from=3-1, to=3-3]
  \arrow["m"', hook, from=1-1, to=3-1]
\end{tikzcd}\]
~~~

into a pullback. We can investigate this definition by instantiating it
in $\Sets$, which _does_ have a generic subobject. Given an
[[embedding]] $m : A \mono X$, we have a family of propositions
$\name{m} : X \to \Omega$ which maps $x : X$ to $m^*(x)$, the
`fibre`{.Agda} of $m$ over $x$. The square above _also_ computes a
fibre, this time of $\name{m}$, and saying that it is $m$ means that
$\name{m}$ assigns $\top$ to precisely those $x : X$ which are in $m$.

<!--
```
_ = fibre

module _ {o ℓ} (C : Precategory o ℓ) (term : Terminal C) where
  open Cat.Reasoning C
  open Terminal term
  open Subobjs C
```
-->

```agda
  record is-generic-subobject {Ω} (true : Hom top Ω) : Type (o ⊔ ℓ) where
    field
      name : ∀ {X} (m : Subobject X) → Hom X Ω
      classifies
        : ∀ {X} (m : Subobject X)
        → is-pullback C (m .map) (name m) ! true
      unique
        : ∀ {X} {m : Subobject X} {nm : Hom X Ω}
        → is-pullback C (m .map) nm ! true
        → nm ≡ name m
```

::: terminology
We follow [@Elephant, A1.6] for our terminology: the morphism $\top : 1
\to \Omega$ is called the **generic subobject**, and $\Omega$ is the
**subobject classifier**. This differs from the terminology in the
[nLab](https://ncatlab.org/nlab/show/subobject+classifier), where the
_morphism_ $\top$ is called the subobject classifier.
:::

```agda
  record Subobject-classifier : Type (o ⊔ ℓ) where
    field
      {Ω}     : Ob
      true    : Hom top Ω
      generic : is-generic-subobject true
```
