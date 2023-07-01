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
  P Q R S P' Q' R' S' : Rel A A ℓ
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
[reflexive transitive closure]: Data.Rel.Closure.ReflexiveTransitive.html

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

If $P \subseteq R$ and $Q \subseteq S$, then $R$ and $S$ are joinable
if $P$ and $Q$ are.

```agda
joinable-⊆
  : P ⊆r R → Q ⊆r S
  → ∀ x y → is-joinable P Q x y → is-joinable R S x y
joinable-⊆ P⊆R Q⊆S x y = ∥-∥-map λ where
  (z , p , q) → z , P⊆R p , Q⊆S q
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

We also have the following useful lemma characterizing resolvability
of subrelations.

```agda
resolvable-⊆
  : P' ⊆r P → Q' ⊆r Q
  → R ⊆r R' → S ⊆r S'
  → is-resolvable P Q R S → is-resolvable P' Q' R' S'
resolvable-⊆ p q r s sq {x = x} {y = y} x↝y x↝z =
  joinable-⊆ r s x y (sq (p x↝y) (q x↝z))
```

## Normal Forms

Let $R$ be an abstract rewriting relation on a type $A$. We say
that an element $x : A$ is a **normal form** if it cannot be reduced
by $R$.

```agda
is-normal-form : (R : Rel A A ℓ) → A → Type _
is-normal-form {A = A} R x = ¬ Σ[ y ∈ A ] R x y
```

This allows us to give a restricted form of elimination for the
reflexive-transitive closure when the domain is a normal form.

```agda
Refl-trans-rec-normal-form
  : (S : A → A → Type ℓ)
  → (∀ {x} → S x x)
  → (∀ {x y} → is-prop (S x y))
  → ∀ {x y} → is-normal-form R x → Refl-trans R x y → S x y
Refl-trans-rec-normal-form {R = R} S srefl sprop x-nf x↝y =
  Refl-trans-rec-chain
    (λ x y → is-normal-form R x → S x y)
    (λ _ → srefl)
    (λ x↝y _ _ x-nf → absurd (x-nf (_ , x↝y)))
    (Π-is-hlevel 1 λ _ → sprop)
    x↝y x-nf
```


If if $A$ is a set, $x : A$ is a normal form, and $x \to^{*} y$, then
$x = y$.

```agda
normal-form+reduces→path
  : ∀ {R : Rel A A ℓ} {x y}
  → is-set A
  → is-normal-form R x
  → Refl-trans R x y
  → x ≡ y
normal-form+reduces→path A-set =
  Refl-trans-rec-normal-form _≡_ refl (A-set _ _)
```

As a corollary, if $x$ and $y$ are normal forms such that
$x \to^{*} z \leftarrow^{*} y$, then $x = y$.

```agda
normal-forms+wedge→path
  : ∀ {R : Rel A A ℓ} {x y z}
  → is-set A
  → is-normal-form R x → is-normal-form R y
  → Refl-trans R x z → Refl-trans R y z
  → x ≡ y
normal-forms+wedge→path set x-nf y-nf x↝z y↝z =
  normal-form+reduces→path set x-nf x↝z
  ∙ (sym $ normal-form+reduces→path set y-nf y↝z)
```


<!-- [TODO: Reed M, 28/06/2023] Prove that this yields a pointed identity system -->

If $x$ is a normal form, and $x \to^{*} z$ and $y \to^{*} z$, then
$y$ must reduce to $x$.

```agda
normal-form+reduces→reduces
  : ∀ {R : Rel A A ℓ} {x y z}
  → is-normal-form R x
  → Refl-trans R x z → Refl-trans R y z
  → Refl-trans R y x
normal-form+reduces→reduces {R = R} {y = y} x-nf x↝z y↝z =
  Refl-trans-rec-normal-form
    (λ x z → Refl-trans R y z → Refl-trans R y x)
    id
    hlevel!
    x-nf x↝z y↝z
```

A normal form of $x : A$ is another $y : A$ such that $y$ is a normal form
and $R^{*}(x,y)$. Note that this is untruncated; uniqueness of normal forms
shall be derived from other properties of $R$.

```agda
record Normal-form {A : Type ℓ} (R : Rel A A ℓ') (x : A) : Type (ℓ ⊔ ℓ') where
  constructor normal-form
  no-eta-equality
  field
    nf : A
    reduces : Refl-trans R x nf
    has-normal-form : is-normal-form R nf

open Normal-form
```

If $A$ is a set, then the type of normal forms is also a set.

```agda
private unquoteDecl eqv = declare-record-iso eqv (quote Normal-form)

Normal-form-is-hlevel
  : ∀ {R : A → A → Type ℓ} {x}
  → (n : Nat) → is-hlevel A (2 + n) → is-hlevel (Normal-form R x) (2 + n)
Normal-form-is-hlevel n A-set =
  Iso→is-hlevel (2 + n) eqv (Σ-is-hlevel (2 + n) A-set hlevel!)
```

<!--
```agda
instance
  H-Level-normal-form
    : ∀ {R : A → A → Type ℓ} {x} {n}
    → ⦃ A-hlevel : ∀ {n} → H-Level A (2 + n) ⦄ → H-Level (Normal-form R x) (2 + n)
  H-Level-normal-form ⦃ A-hlevel ⦄ =
    basic-instance 2 (Normal-form-is-hlevel 0 (H-Level.has-hlevel {n = 2} A-hlevel))

Normal-form-pathp
  : ∀ {x y}
  → (p : x ≡ y)
  → (x-nf : Normal-form R x) → (y-nf : Normal-form R y)
  → x-nf .nf ≡ y-nf. nf
  → PathP (λ i → Normal-form R (p i)) x-nf y-nf
Normal-form-pathp p x-nf y-nf nf-path i .nf = nf-path i
Normal-form-pathp {R = R} p x-nf y-nf nf-path i .reduces =
  is-prop→pathp {B = λ i → Refl-trans R (p i) (nf-path i)}
    (λ i → trunc)
    (x-nf .reduces) (y-nf .reduces) i
Normal-form-pathp {R = R} p x-nf y-nf nf-path i .has-normal-form =
  is-prop→pathp {B = λ i → is-normal-form R (nf-path i)}
    (λ i → hlevel!)
    (x-nf .has-normal-form) (y-nf .has-normal-form) i

Normal-form-path
  : ∀ {x}
  → (x-nf x-nf' : Normal-form R x)
  → x-nf .nf ≡ x-nf'. nf
  → x-nf ≡ x-nf'
Normal-form-path x-nf x-nf' p = Normal-form-pathp refl x-nf x-nf' p
```
-->
