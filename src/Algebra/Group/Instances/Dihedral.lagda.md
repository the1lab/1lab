<!--
```agda
open import Algebra.Group.Instances.Integers
open import Algebra.Group.Instances.Cyclic
open import Algebra.Group.Semidirect
open import Algebra.Group.Cat.Base
open import Algebra.Group.Action
open import Algebra.Group.Ab

open import Cat.Functor.Base
open import Cat.Prelude
```
-->

```agda
module Algebra.Group.Instances.Dihedral where
```

# Dihedral groups {defines="dihedral-group generalised-dihedral-group"}

The [[group]] of symmetries of a regular $n$-gon, comprising rotations
around the center and reflections, is called the **dihedral group**
of order $2n$: there are $n$ rotations and $n$ reflections, where
each reflection can be obtained by composing a rotation with a chosen
reflection.

::: terminology
There are two notational conventions for the dihedral group associated
with the regular $n$-gon: the *geometric* convention is to write $D_n$,
while the *algebraic* convention is to write $D_{2n}$, alluding to the
order of the group. We will use the geometric convention here.
:::

Given any [[abelian group]] $G$, we define the **generalised dihedral
group** $\mathrm{Dih}(G)$ as the [[semidirect product]]^[See
[[there|semidirect product]] for some intuition.] group $\ZZ/2\ZZ \ltimes
G$, where the [[cyclic group]] $\ZZ/2\ZZ$ [[acts|group action]] on $G$
by `negation`{.Agda}.

```agda
Dih : ∀ {ℓ} → Abelian-group ℓ → Group ℓ
Dih G = Semidirect-product (Lift-group _ (ℤ/ 2)) (Abelian→Group G) $
  ℤ/-out 2 (F-map-iso Ab↪Grp (negation G)) (ext λ _ → inv-inv)
  where open Abelian-group-on (G .snd)
```

We can then define the dihedral group $D_n$ as the generalised dihedral
group of $\ZZ/n\ZZ$, the group of *rotations* of the regular $n$-gon.

```agda
D : Nat → Group lzero
D n = Dih (ℤ-ab/ n)
```

We also define the **infinite dihedral group** $D_\infty$ as the
generalised dihedral group of the [[group of integers]],
$\mathrm{Dih}(\ZZ)$.

```agda
D∞ : Group lzero
D∞ = Dih ℤ-ab
```

Geometrically, $D_\infty$ is the symmetry group of the following
infinitely repeating frieze pattern, also known as $p1m1$: there is
a horizontal translation for every integer, as well as a reflection
across the vertical axis that flips all the translations.

~~~{.quiver}
\begin{tikzpicture}
  \node (-3) at (-3, 0) {};
  \node (-2) at (-2, 0) {};
  \node (-1) at (-1, 0) {};
  \node (0) at (0, 0) {};
  \node (1) at (1, 0) {};
  \node (2) at (2, 0) {};
  \node (3) at (3, 0) {};
  \draw (-3.center) to (-2.center);
  \draw (-2.center) to (-1.center);
  \draw (-1.center) to (0.center);
  \draw (0.center) to (1.center);
  \draw (1.center) to (2.center);
  \draw (2.center) to (3.center);

  \node[left,at=(-3)] {$\cdots$};
  \node[right,at=(3)] {$\cdots$};

  \node (-2') at (-2, 1) {};
  \draw (-2.center) to (-2'.center);
  \node (-1') at (-1, 1) {};
  \draw (-1.center) to (-1'.center);
  \node (0') at (0, 1) {};
  \draw (0.center) to (0'.center);
  \node (1') at (1, 1) {};
  \draw (1.center) to (1'.center);
  \node (2') at (2, 1) {};
  \draw (2.center) to (2'.center);
\end{tikzpicture}
~~~

Note that our construction of $D_n$ makes $D_0$ equal to $D_\infty$,
since $\ZZ/0\ZZ$ is $\ZZ$.

```agda
D₀≡D∞ : D 0 ≡ D∞
D₀≡D∞ = ap Dih ℤ-ab/0≡ℤ-ab
```
