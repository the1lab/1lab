<!--
```agda
open import 1Lab.Prelude
open import Data.Rel.Base
open import Data.Rel.Closure
```
-->

```agda
module Rewriting.Base where
```

<!--
```agda
private variable
  ℓ ℓ' ℓ'' : Level
  A B X : Type ℓ
  R S _↝₁_ _↝₂_ : Rel A A ℓ
```
-->

# Abstract Rewriting Systems

Many problems in computer science can be phrased in terms of
**term rewriting systems**. Concretely, these are given by a collection
of terms in some language, along with a collection of rules that describe
how we can simplify terms. As an example, the untyped $\lambda$-calculus
can be naturally presented as a term rewriting system, where only
reduction rule is $\beta$-reduction. More abstractly, a rewriting system
on a type $A$ is simply a [relation] $\to$ on $A$ which encodes the
rewriting rules. Sequences of rewrites are then described using the
[reflexive transitive closure] of $\to$.

[relation]: Data.Rel.Base.html
[reflexive transitive closure]: Data.Rel.Closure.html#reflexive-transitive-closure.html

## Basic Concepts

Let $R$ and $S$ be a pair of relations on $A$. We say that
2 elements $x$ and $y$ are **joinable** by $R$ and $S$ if there
exists some $z$ such that $R(x,z)$ and $S(y,z)$.

```agda
is-joinable 
  : ∀ {ℓa ℓr ℓs} {A : Type ℓa}
  → (R : Rel A A ℓr) (S : Rel A A ℓs)
  → A → A → Type _
is-joinable {A = A} R S x y = ∃[ z ∈ A ] (R x z × S y z)
```

This is equivalent to the composite of $S^{-1}$ and $R$, but this is
less intuitive to think about.

```agda
private
  ∘≡joinable
    : ∀ {R : Rel A A ℓ} {S : Rel A A ℓ'} {x y : A}
    → (flipr S ∘r R) x y ≡ is-joinable R S x y
  ∘≡joinable = refl
```

Let $P$, $Q$, $R$ and $S$ all be relations on $A$. We say that $P$ and
$Q$ are resolvable by $R$ and $S$ if for all $x,y,z : A$, $P(x,y)$ and
$Q(x,z)$ implies that $y$ and $z$ are joinable by $R$ and $S$.

~~~{.quiver}
\begin{tikzcd}
  & x \\
  y && z \\
  & {\exists! w}
  \arrow["R"', dashed, from=2-1, to=3-2]
  \arrow["S", dashed, from=2-3, to=3-2]
  \arrow["P"', from=1-2, to=2-1]
  \arrow["Q", from=1-2, to=2-3]
\end{tikzcd}
~~~

```agda
is-resolvable
  : ∀ {ℓa ℓp ℓq ℓr ℓs} {A : Type ℓa}
  → (P : Rel A A ℓp) → (Q : Rel A A ℓq)
  → (R : Rel A A ℓr) → (S : Rel A A ℓs)
  → Type _
is-resolvable {A = A} P Q R S =
  ∀ {x y z} → P x y → Q x z → is-joinable R S y z
```

This condition is equivalent to $Q \circ P^{-1} \subseteq S^{-1} \circ R$,
but the latter version is much more confusing to think about.

```agda
private
  ←∘→⊆→∘←≃resolvable
    : ∀ {ℓa ℓp ℓq ℓr ℓs} {A : Type ℓa}
    → {P : Rel A A ℓp} {Q : Rel A A ℓq}
    → {R : Rel A A ℓr} {S : Rel A A ℓs}
    → ((Q ∘r flipr P) ⊆r (flipr S ∘r R)) ≃ is-resolvable P Q R S
  ←∘→⊆→∘←≃resolvable =
    prop-ext!
      (λ sub p q → sub (pure (_ , p , q)))
      (λ diamond q∘p → do
        x , p , q ← q∘p
        diamond p q)
```
