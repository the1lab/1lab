<!--
```agda
open import 1Lab.Reflection.Induction
open import 1Lab.Prelude

open import Algebra.Group.Cat.Base
open import Algebra.Semigroup
open import Algebra.Group.Ab
open import Algebra.Monoid
open import Algebra.Group
open import Algebra.Magma

open import Data.Set.Truncation
```
-->

```agda
module Algebra.Group.Homotopy where
```

<!--
```agda
private variable
  ℓ : Level
  A : Type ℓ
```
-->

# Homotopy groups {defines="homotopy-group fundamental-group"}

:::{.definition #loop-space}
Given a [[pointed type]] $(A, a)$ we refer to the type $a = a$ as the
**loop space of $A$**, and refer to it in short as $\Omega A$. Since we
always have $\refl : a = a$, $\Omega A$ is _itself_ a pointed type, the
construction can be iterated, a process which we denote $\Omega^n A$.

```agda
Ωⁿ : Nat → Type∙ ℓ → Type∙ ℓ
Ωⁿ zero A    = A
Ωⁿ (suc n) (A , x) with Ωⁿ n (A , x)
... | (T , x) = Path T x x , refl
```
:::

::: popup
The **$n$th homotopy group** $\pi_n(A)$ of a [[pointed type]] $A$ is the
[[set truncation]] of the [[loop space]] $\Omega^n(A)$, made into a
[[group]] under composition of loops.

The first homotopy group $\pi_1(A)$ is also called the **fundamental
group** of $A$.
:::

For positive $n$, we can give $\Omega^n A$ a `Group`{.Agda} structure,
obtained by [[truncating|set-truncation]] the higher groupoid structure
that $A$ is equipped with. We call the sequence $\pi_n(A)$ the
**homotopy groups** of $A$, but remark that the indexing used by
`πₙ₊₁`{.Agda} is off by 1: `πₙ₊₁ 0 A` is the **fundamental group**
$\pi_1(A)$.

```agda
πₙ₊₁ : Nat → Type∙ ℓ → Group ℓ
πₙ₊₁ n t = to-group omega where
  omega : make-group ∥ Ωⁿ (suc n) t .fst ∥₀
  omega .make-group.group-is-set = squash
  omega .make-group.unit = inc refl
  omega .make-group.mul = ∥-∥₀-map₂ _∙_
  omega .make-group.inv = ∥-∥₀-map sym
```

As mentioned above, the group structure is given entirely by the
groupoid structure of types: The neutral element is `refl`{.Agda}, the
group operation is `path concatenation`{.Agda ident=_∙_}, and the
inverses are given by `inverting paths`{.Agda ident=sym}.

```agda
  omega .make-group.assoc = elim! λ x y z i → inc (∙-assoc x y z i)
  omega .make-group.invl = elim! λ x i → inc (∙-invl x i)
  omega .make-group.idl = elim! λ x i → inc (∙-idl x i)
```

A direct cubical transcription of the Eckmann-Hilton argument tells us
that path concatenation for $\Omega^{n + 2} A$ is
commutative, independent of $A$.

```agda
Ωⁿ⁺²-is-abelian-group
  : ∀ {ℓ} {A : Type∙ ℓ} (n : Nat) (p q : Ωⁿ (2 + n) A .fst)
  → p ∙ q ≡ q ∙ p
Ωⁿ⁺²-is-abelian-group n p q =
  transport
    (λ k → ap (λ x → ∙-idr x k) p ∙ ap (λ x → ∙-idl x k) q
         ≡ ap (λ x → ∙-idl x k) q ∙ ap (λ x → ∙-idr x k) p)
    (λ i → (λ j → p (j ∧ ~ i) ∙ q (j ∧ i))
         ∙ (λ j → p (~ i ∨ j) ∙ q (i ∨ j)))
```

The proof can be visualized with the following diagram, where the
vertices are in $\Omega^{n + 1} A$. The outer rectangle shows `p ∙ q ≡
q ∙ p`, which is filled by transporting the two inner squares using
`∙-idr`{.Agda} on `p j` and `∙-idl`{.Agda} on `q j`. Note that
`∙-idr refl` and `∙-idl refl` are definitionally equal.  In the two
inner squares, `p j` and `q j` are on different sides of the path
composition, so we can use the De Morgan structure on the interval to
have `p` and `q` slip by each other.

~~~{.quiver}
\[\begin{tikzcd}
	{\refl} &&& {\refl} &&& {\refl} \\
	& {\refl \cdot \refl} && {\refl \cdot \refl} && {\refl \cdot \refl} \\
	\\
	& {\refl \cdot \refl} && {\refl \cdot \refl} && {\refl \cdot \refl} \\
	{\refl} &&& {\refl} &&& {\refl}
	\arrow[from=2-2, to=4-2]
	\arrow["{p\ \neg i \cdot q\ i}"{description}, color={rgb,255:red,214;green,92;blue,214}, from=2-4, to=4-4]
	\arrow[from=2-6, to=4-6]
	\arrow[from=1-1, to=5-1]
	\arrow[from=1-7, to=5-7]
	\arrow[""{name=0, anchor=center, inner sep=0}, "{p\ j \cdot \refl}"', color={rgb,255:red,214;green,92;blue,92}, from=2-2, to=2-4]
	\arrow[""{name=1, anchor=center, inner sep=0}, "{\refl \cdot q\ j}"', color={rgb,255:red,153;green,92;blue,214}, from=2-4, to=2-6]
	\arrow[""{name=2, anchor=center, inner sep=0}, "{\refl \cdot q\ j}", color={rgb,255:red,153;green,92;blue,214}, from=4-2, to=4-4]
	\arrow[""{name=3, anchor=center, inner sep=0}, "{p\ j \cdot \refl}", color={rgb,255:red,214;green,92;blue,92}, from=4-4, to=4-6]
	\arrow[""{name=4, anchor=center, inner sep=0}, "{p\ j}", color={rgb,255:red,214;green,92;blue,92}, from=1-1, to=1-4]
	\arrow[""{name=5, anchor=center, inner sep=0}, "{q\ j}", color={rgb,255:red,153;green,92;blue,214}, from=1-4, to=1-7]
	\arrow[""{name=6, anchor=center, inner sep=0}, "{q\ j}"', color={rgb,255:red,153;green,92;blue,214}, from=5-1, to=5-4]
	\arrow[""{name=7, anchor=center, inner sep=0}, "{p\ j}"', color={rgb,255:red,214;green,92;blue,92}, from=5-4, to=5-7]
	\arrow[from=2-2, to=1-1]
	\arrow[from=4-2, to=5-1]
	\arrow[from=2-4, to=1-4]
	\arrow[from=4-4, to=5-4]
	\arrow[from=2-6, to=1-7]
	\arrow[from=4-6, to=5-7]
	\arrow["{p (j \land \neg i) \cdot q (j \land i)}"{description}, color={rgb,255:red,214;green,92;blue,214}, draw=none, from=0, to=2]
	\arrow["{p (\neg i \lor j) \cdot q (i \lor j)}"{description}, color={rgb,255:red,214;green,92;blue,214}, draw=none, from=1, to=3]
	\arrow["{\rm{\cdot\text{-id-r}}\ (p\ j)\ k}"{description}, color={rgb,255:red,214;green,92;blue,92}, draw=none, from=0, to=4]
	\arrow["{\rm{\cdot\text{-id-l}}\ (q\ j)\ k}"{description}, color={rgb,255:red,153;green,92;blue,214}, draw=none, from=1, to=5]
	\arrow["{\rm{\cdot\text{-id-l}}\ (q\ j)\ k}"{description}, color={rgb,255:red,153;green,92;blue,214}, draw=none, from=2, to=6]
	\arrow["{\rm{\cdot\text{-id-r}}\ (p\ j)\ k}"{description}, color={rgb,255:red,214;green,92;blue,92}, draw=none, from=3, to=7]
\end{tikzcd}\]
~~~

Lifting this result through the set truncation establishes that
$\pi_{n+2}$ is an [[Abelian group]]:

```agda
πₙ₊₂-is-abelian-group : ∀ {ℓ} {A : Type∙ ℓ} (n : Nat)
                      → Group-on-is-abelian (πₙ₊₁ (1 + n) A .snd)
πₙ₊₂-is-abelian-group {A = A} n =
  elim! λ x y i → inc (Ωⁿ⁺²-is-abelian-group n x y i)
```

We can give an alternative construction of the fundamental group $\pi_1$ for types
that are known to be [[groupoids]]: in that case, we can avoid using a set truncation
since the loop space is already a set.

```agda
module π₁Groupoid {ℓ} ((T , t) : Type∙ ℓ) (grpd : is-groupoid T) where
  private
    mk : make-group (t ≡ t)
    mk .make-group.group-is-set = grpd t t
    mk .make-group.unit         = refl
    mk .make-group.mul          = _∙_
    mk .make-group.inv          = sym
    mk .make-group.assoc        = ∙-assoc
    mk .make-group.invl         = ∙-invl
    mk .make-group.idl          = ∙-idl

  on-Ω : Group-on (t ≡ t)
  on-Ω = to-group-on mk

  π₁ : Group ℓ
  π₁ = to-group mk

  π₁≡π₀₊₁ : π₁ ≡ πₙ₊₁ 0 (T , t)
  π₁≡π₀₊₁ = ∫-Path
    (total-hom inc (record { pres-⋆ = λ _ _ → refl }))
    (∥-∥₀-idempotent (grpd _ _))
```
