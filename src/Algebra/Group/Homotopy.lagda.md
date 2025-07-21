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

open import Homotopy.Conjugation
open import Homotopy.Truncation
open import Homotopy.Loopspace
```
-->

```agda
module Algebra.Group.Homotopy where
```

<!--
```agda
private variable
  ℓ     : Level
  A B C : Type∙ ℓ
```
-->

# Homotopy groups {defines="homotopy-group fundamental-group"}

For positive $n$, we can give the iterated [[loop space]] $\Omega^n A$ a
`Group`{.Agda} structure, obtained by [[truncating|set-truncation]] the
higher groupoid structure that $A$ is equipped with. We call the
sequence $\pi_n(A)$ the **homotopy groups** of $A$, but remark that the
indexing used by `πₙ₊₁`{.Agda} is off by 1: `πₙ₊₁ 0 A` is the
**fundamental group** $\pi_1(A)$.

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
  omega .make-group.invl  = elim! λ x i → inc (∙-invl x i)
  omega .make-group.idl   = elim! λ x i → inc (∙-idl x i)
```

<!--
```agda
πₙ₊₁-ap
  : ∀ {ℓ} {A B : Type∙ ℓ} n (e : A ≃∙ B)
  → πₙ₊₁ n A Groups.≅ πₙ₊₁ n B
πₙ₊₁-ap n e = total-iso (∥-∥₀-ap (Ωⁿ-ap (suc n) e .fst)) record
  { pres-⋆ = elim! λ q r → ap ∥_∥₀.inc (Ωⁿ-map-∙ n (Equiv∙.to∙ e) _ _) }

πₙ₊₁-map
  : ∀ {ℓ ℓ'} {A : Type∙ ℓ} {B : Type∙ ℓ'} n (f : A →∙ B)
  → ⌞ πₙ₊₁ n A ⌟ → ⌞ πₙ₊₁ n B ⌟
πₙ₊₁-map n f = ∥-∥₀-map (Ωⁿ-map (suc n) f .fst)

opaque

  πₙ-def
    : ∀ {ℓ} (A : Type∙ ℓ) n
    → (⌞ πₙ₊₁ n A ⌟ , inc refl) ≃∙ Ωⁿ (suc n) (n-Tr∙ A (suc (n + 2)))
  πₙ-def A n = n-Tr-set ∙e n-Tr-Ωⁿ A 1 (suc n) .fst , n-Tr-Ωⁿ A 1 (suc n) .snd

  πₙ-def-inc
    : ∀ {ℓ} (A : Type∙ ℓ) n → (l : ⌞ Ωⁿ (1 + n) A ⌟)
    → πₙ-def A n · inc l ≡ Ωⁿ-map (1 + n) inc∙ · l
  πₙ-def-inc A n l = n-Tr-Ωⁿ-inc A 1 (suc n) ·ₚ l

  πₙ-def-∙
    : ∀ {ℓ} (A : Type∙ ℓ) n → (p q : ⌞ Ωⁿ (1 + n) A ⌟)
    → πₙ-def A n · inc (p ∙ q) ≡ πₙ-def A n · inc p ∙ πₙ-def A n · inc q
  πₙ-def-∙ A = n-Tr-Ωⁿ-∙ A 1
```
-->

A direct cubical transcription of the Eckmann-Hilton argument tells us
that path concatenation for $\Omega^{n + 2} A$ is commutative,
independent of $A$.

```agda
Ωⁿ⁺²-is-abelian
  : ∀ {ℓ} {A : Type∙ ℓ} (n : Nat) (p q : Ωⁿ (2 + n) A .fst)
  → p ∙ q ≡ q ∙ p
Ωⁿ⁺²-is-abelian n p q =
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
  elim! λ x y i → inc (Ωⁿ⁺²-is-abelian n x y i)
```

We can give an alternative construction of the fundamental group $\pi_1$
for types that are known to be [[groupoids]]: in that case, we can avoid
using a set truncation since the loop space is already a set.

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

  π₁≡π₀₊₁ : π₁ Groups.≅ πₙ₊₁ 0 (T , t)
  π₁≡π₀₊₁ = total-iso (inc , ∥-∥₀-idempotent (grpd _ _)) (record { pres-⋆ = λ x y → refl })
```
