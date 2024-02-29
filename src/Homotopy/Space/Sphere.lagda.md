<!--
```
open import 1Lab.Prelude

open import Homotopy.Space.Suspension
open import Homotopy.Space.Circle
```
-->

```agda
module Homotopy.Space.Sphere where
```

# The -1 and 0 spheres

In classical topology, the _topological space_ $S^n$ is typically
defined as the subspace of $\bb{R}^{n+1}$ consisting of all points
at unit distance from the origin. We see from this definition that the
$0$-sphere is the discrete two point space $\{-1, 1\} \subset \bb{R}$,
and that the $-1$ sphere is the empty subspace $\varnothing \subset \{0\}$.
We will recycle existing types and define:

```agda
S⁻¹ : Type
S⁻¹ = ⊥

S⁰ : Type
S⁰ = Bool
```

We note that `S⁰` may be identified with `Susp S⁻¹`. Since the pattern
matching checker can prove that `merid x i` is impossible when `x : ⊥`,
the case for this constructor does not need to be written, this makes
the proof look rather tautologous.

```agda
open is-iso

SuspS⁻¹≃S⁰ : Susp S⁻¹ ≡ S⁰
SuspS⁻¹≃S⁰ = ua (SuspS⁻¹→S⁰ , is-iso→is-equiv iso-pf) where
  SuspS⁻¹→S⁰ : Susp S⁻¹ → S⁰
  SuspS⁻¹→S⁰ N = true
  SuspS⁻¹→S⁰ S = false

  S⁰→SuspS⁻¹ : S⁰ → Susp S⁻¹
  S⁰→SuspS⁻¹ true = N
  S⁰→SuspS⁻¹ false = S

  iso-pf : is-iso SuspS⁻¹→S⁰
  iso-pf .inv = S⁰→SuspS⁻¹
  iso-pf .rinv false = refl
  iso-pf .rinv true = refl
  iso-pf .linv N = refl
  iso-pf .linv S = refl
```

# n-Spheres {defines="sphere"}

The spheres of higher dimension can be defined inductively:
$S^{n + 1} = \Sigma S^n$, that is, suspending the $n$-sphere constructs
the $n+1$-sphere.

The spheres are essentially indexed by the natural numbers, except that
we want to start at $-1$ instead of $0$. To remind ourselves of this,
we name our spheres with a superscript $^{n-1}$:

```agda
Sⁿ⁻¹ : Nat → Type
Sⁿ⁻¹ zero = S⁻¹
Sⁿ⁻¹ (suc n) = Susp (Sⁿ⁻¹ n)
```

A slightly less trivial example of definitions lining up is the verification
that `Sⁿ⁻¹ 2` is equivalent to our previous definition of `S¹`:

```agda
SuspS⁰≡S¹ : Sⁿ⁻¹ 2 ≡ S¹
SuspS⁰≡S¹ = ua (SuspS⁰→S¹ , is-iso→is-equiv iso-pf) where
```

In `Sⁿ⁻¹ 2`, we have two point constructors joined by two paths, while in
`S¹` we have a single point constructor and a loop. Geometrically, we
can picture morphing `Sⁿ⁻¹ 2` into `S¹` by squashing one of the meridians
down to a point, thus bringing `N` and `S` together. This intuition leads
to a definition:

```agda
  SuspS⁰→S¹ : Sⁿ⁻¹ 2 → S¹
  SuspS⁰→S¹ N = base
  SuspS⁰→S¹ S = base
  SuspS⁰→S¹ (merid N i) = base
  SuspS⁰→S¹ (merid S i) = loop i
```

In the other direction, we send `base` to `N`, and then need to send
`loop` to some path `N ≡ N`. Since this map should define an equivalence,
we make it such that loop wraps around the space `Sⁿ 2` by way of traversing
both meridians.

```agda
  S¹→SuspS⁰ : S¹ → Sⁿ⁻¹ 2
  S¹→SuspS⁰ base = N
  S¹→SuspS⁰ (loop i) = (merid S ∙ sym (merid N)) i
```

<details> <summary> We then verify that these maps are inverse equivalences.
One of the steps involves a slightly tricky `hcomp`, although this can be
avoided by working with transports instead of dependent paths, and then by
using lemmas on transport in pathspaces. </summary>

```agda
  iso-pf : is-iso SuspS⁰→S¹
  iso-pf .inv = S¹→SuspS⁰
  iso-pf .rinv base = refl
  iso-pf .rinv (loop i) =
    ap (λ p → p i)
      (ap SuspS⁰→S¹ (merid S ∙ sym (merid N)) ≡⟨ ap-∙ SuspS⁰→S¹ (merid S) (sym (merid N))⟩
      loop ∙ refl                             ≡⟨ ∙-idr _ ⟩
      loop                                    ∎)
  iso-pf .linv N = refl
  iso-pf .linv S = merid N
  iso-pf .linv (merid N i) j = merid N (i ∧ j)
  iso-pf .linv (merid S i) j = hcomp (∂ i ∨ ∂ j) λ where
    k (k = i0) → merid S i
    k (i = i0) → N
    k (i = i1) → merid N (j ∨ ~ k)
    k (j = i0) → ∙-filler (merid S) (sym (merid N)) k i
    k (j = i1) → merid S i
```
</details>

<!--
```agda
Sⁿ : Nat → Type∙ lzero
Sⁿ n = Sⁿ⁻¹ (suc n) , N
```
-->
