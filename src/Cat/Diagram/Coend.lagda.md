<!--
```agda
open import Cat.Instances.Product
open import Cat.Prelude

import Cat.Functor.Bifunctor as Bifunctor
import Cat.Reasoning as Cat
```
-->

```agda
module Cat.Diagram.Coend where
```

<!--
```agda
private
  variable
    o ℓ o' ℓ' : Level
    C D : Precategory o' ℓ'
  coend-level
    : {C : Precategory o ℓ} {D : Precategory o' ℓ'}
    → Functor (C ^op ×ᶜ C) D
    → Level
  coend-level {o = o} {ℓ} {o'} {ℓ'} _ = o ⊔ o' ⊔ ℓ ⊔ ℓ'
```
-->

# Coends {defines=coend}

Let $F : \cC\op \times \cC \to \cD$ be a functor, which, by the
general yoga of [bifunctors] we think of as combining a contravariant
action $F(-,x) : \cC\op \to \cD$ and a covariant action $F(x,-) :
\cC \to \cD$ of $\cC$ on $\cD$[^action]. As a concrete
example, we could take $\cC = \bf{B}R$, the 1-object [$\Ab$-category]
associated to a [ring] $R$ --- then the functors $F(-,x)$ and $F(x,-)$
would be left- and right- $R$-modules, respectively. In fact, let us
focus on this case and consider two modules $A$ and $B$, incarnated as a
pair of functors $A : \bf{B}R\op \to \Ab$ and $B : \bf{B}R \to \Ab$.

[^action]: "Action" here is meant evoke the idea of e.g. [group
actions], and does not refer to a specific concept

[bifunctors]: Cat.Functor.Bifunctor.html
[group actions]: Algebra.Group.Action.html
[$\Ab$-category]: Cat.Abelian.Base.html#ab-enriched-categories
[ring]: Algebra.Ring.html

In this situation, we may study the **tensor product** (of modules!) $A
\otimes_R B$ as being an "universal object where the actions of $A$ and
$B$ agree". In particular, it's known that we can compute the tensor
product of modules as being (the object in) a coequaliser diagram like

$$
A \otimes R \otimes B \tto A \otimes B \epi A \otimes_R B\text{,}
$$

where the undecorated $A \otimes B$ stands for the [tensor product of
abelian groups], and the two maps are given by the $R$-actions of $A$
and $B$. More explicitly, letting $a \otimes b$ stand for a tensor, the
equation $a\otimes rb = ar\otimes b$ holds in $A \otimes_R B$, and the
tensor product is the universal object where this is forced to hold.

[tensor product of abelian groups]: Algebra.Group.Ab.Tensor.html

Going back to the absurd generality of a bifunctor $F : \cC\op \times
\cC \to \cD$, we may still wish to consider these sorts of
"universal quotients where a pair of actions are forced to agree", even
if our codomain category $\cD$ does not have a well-behaved calculus
of tensor products. As a motivating example, the computation of [left
Kan extensions][lan] as certain colimits has this form!

[lan]: Cat.Functor.Kan.Pointwise.html#computing-pointwise-extensions

We call such an object a **coend** of the functor $F$, and denote it by
$\int^c F(c,c)$ (or $\int F$ for short). Being a type of [colimit],
coends are [initial objects] in a particular category, but we will
unpack the definition here and talk about **cowedges** instead.

[colimit]: Cat.Diagram.Colimit.Base.html
[initial objects]: Cat.Diagram.Initial.html

## Formalisation {defines="cowedge"}

```agda
record Cowedge (F : Functor (C ^op ×ᶜ C) D) : Type (coend-level F) where
  no-eta-equality
```

A **cowedge** under a functor $F$ is given by an object $w : \cD$
(which we refer to as the `nadir`{.Agda}, because we're pretentious),
together with a family of maps $\psi_c : F(c,c) \to w$.

<!--
```agda
  private
    module C = Cat C
    module D = Cat D
    module F = Bifunctor F
```
-->

```agda
  field
    nadir : D.Ob
    ψ     : ∀ c → D.Hom (F.₀ (c , c)) nadir
```

This family of maps must satisfy a condition called **extranaturality**,
expressing that the diagram below commutes. As the name implies, this is
like the naturality condition for a [natural transformation], but extra!
In particular, it copes with the functor being covariant in one argument
and contravariant in the other.

~~~{.quiver}
\[\begin{tikzcd}
  {F(c',c)} && {F(c',c')} \\
  \\
  {F(c,c)} && w
  \arrow["{F(\mathrm{id}_{c'},f)}", from=1-1, to=1-3]
  \arrow["{\psi_{c'}}", from=1-3, to=3-3]
  \arrow["{\psi_c}"', from=3-1, to=3-3]
  \arrow["{F(f,\mathrm{id}_{c})}"', from=1-1, to=3-1]
\end{tikzcd}\]
~~~

[natural transformation]: Cat.Base.html#natural-transformations

```agda
    extranatural
      : ∀ {c c'} (f : C.Hom c c')
      → ψ c' D.∘ F.second f ≡ ψ c D.∘ F.first f
```

A coend, then, is a universal cowedge. In particular, we say that
**$(w,\psi)$ is a coend for $F$** such that, given any other wedge
$(w',\psi)$ under $F$, we can factor $w$ through $w'$ by a unique map $e
: w \to w'$. Furthermore, the map $e$ must commute with the maps $\psi$,
meaning explicitly that $e\psi_a = \psi'_a$.

```agda
record Coend (F : Functor (C ^op ×ᶜ C) D) : Type (coend-level F) where
```

<!--
```agda
  private
    module C = Cat C
    module D = Cat D
    module F = Bifunctor F
```
-->

```agda
  field
    cowedge : Cowedge F
```

<!--
```agda
  module cowedge = Cowedge cowedge
  open cowedge public
  open Cowedge
```
-->

Unfolding the requirement of uniqueness for $e$, we require that, given
any other map $f : w \to w'$ s.t. $f\psi_a = \psi'_a$ for all objects
$a$, then $e = f$. This is exactly analogous to the uniqueness
properties of colimiting maps for every other colimit.

```agda
  field
    factor   : ∀ (W : Cowedge F) → D.Hom cowedge.nadir (W .nadir)
    commutes : ∀ {W : Cowedge F} {a} → factor W D.∘ cowedge.ψ a ≡ W .ψ a
    unique
      : ∀ {W : Cowedge F} {g : D.Hom cowedge.nadir (W .nadir)}
      → (∀ {a} → g D.∘ cowedge.ψ a ≡ W .ψ a)
      → g ≡ factor W
```
