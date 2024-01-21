<!--
```agda
open import 1Lab.Function.Surjection

open import Algebra.Monoid

open import Cat.Functor.Subcategory
open import Cat.Functor.Adjoint
open import Cat.Prelude

open import Data.Fin.Indexed
open import Data.Fin.Base
open import Data.Sum.Base
open import Data.Power

open import Order.Semilattice.Join.Subsemilattice
open import Order.Instances.Pointwise.Diagrams
open import Order.Semilattice.Join.NAry
open import Order.Instances.Pointwise
open import Order.Semilattice.Join
open import Order.Diagram.Lub
open import Order.Subposet
open import Order.Base

import Order.Semilattice.Join.Reasoning
```
-->

```agda
module Order.Semilattice.Free where
```

# Free (semi)lattices

This module provides an *impredicative* construction of the free [[join
semilattice]] on a set $A$, as the semilattice of [[Kuratowski-finite
subsets]] $K(A)$, ordered by inclusion, under the operation of union.
While this construction might feel like it comes out of left field,
finite subsets are actually a very natural model for join semilattices,
since *every subset is a join of singletons*.

While this Coyoneda-like theorem about $K(A)$ provides an abstract
justification for the construction, it's important to keep in mind that
a Kuratowski-finite subset of $A$ can be equivalently presented as a
list with elements drawn from $A$, but considered modulo order and
repetition. Therefore, a concrete intuition for this construction can
also be drawn from the connection between semilattices and monoids: a
semilattice is a *commutative, idempotent* monoid.

```agda
module _ {ℓ} (A : Set ℓ) where
  K-finite-subset : Type ℓ
  K-finite-subset = Σ[ P ∈ (∣ A ∣ → Ω) ] (is-K-finite P)

  _∪ᵏ_ : K-finite-subset → K-finite-subset → K-finite-subset
  (P , pf) ∪ᵏ (Q , qf) = P ∪ Q , union-is-K-finite {P = P} {Q = Q} pf qf

  minimalᵏ : K-finite-subset
  minimalᵏ = minimal , minimal-is-K-finite
```

Since $K(A)$ is closed under unions (and contains the least element), it
follows that it's a semilattice, being a sub-semilattice of the power
set of $A$. In fact, a different characterisation of $K(A)$ is as the
smallest sub-semilattice of $K(A)$ containing the singletons and closed
under union.

<!--
```agda
  K[_] : Join-semilattice ℓ ℓ
  K[_] .fst = Subposet (Subsets ∣ A ∣) λ P → el! (is-K-finite P)
  K[_] .snd =
    Subposet-is-join-semilattice Subsets-is-join-slat
      (λ {P} {Q} pf qf → union-is-K-finite {P = P} {Q = Q} pf qf)
      minimal-is-K-finite

  private module KA = Order.Semilattice.Join.Reasoning (K[_] .snd)
```
-->

We shall refer to the singleton-assigning map $A \to K(A)$ as $\eta$,
since it will play the role of our adjunction unit when we establish the
universal property of $K(A)$.

```agda
  singletonᵏ : ∣ A ∣ → K-finite-subset
  singletonᵏ x = singleton x , singleton-is-K-finite (A .is-tr) x
```

We can then establish the aforementioned Coyoneda-like statement: a
K-finite subset $P \sube A$ is the join of the singleton subsets it
contains.

```agda
  K-singleton-lub
    : (P : K-finite-subset)
    → is-lub (K[_] .fst) {I = ∫ₚ (P .fst)} (singletonᵏ ⊙ fst) P
  K-singleton-lub P = subposet-has-lub _ (P .snd) (subset-singleton-lub _)
```

In a similar vein, given a map $f : A \to B$ and a semilattice structure
on $B$, we can extend this to a semilattice homomorphism^[Here we
construct the underlying map first, the proof that it's a semilattice
homomorphism follows.] $f' : K(A) \to B$ by first expressing $S : K(A)$
as $\bigcup_{i:[n]} \eta(a_i)$ for some $n$, $a_i$, then computing
$\bigcup_{i:[n]} f(a_i)$.

```agda
  module _ {o ℓ'} (B : Join-semilattice o ℓ') where
    private module B = Order.Semilattice.Join.Reasoning (B .snd)

    fold-K : (∣ A ∣ → ⌞ B ⌟) → K-finite-subset → ⌞ B ⌟
    fold-K f (P , P-fin) = Lub.lub ε' module fold-K where
      fam : (Σ ∣ A ∣ λ x → ∣ P x ∣) → ⌞ B ⌟
      fam (x , _) = f x
```

Since precomposition with a [[surjection]] both _preserves and reflect_
the property of being a [[least upper bound]], we can compute a join for
our family $P \mono A$ by first computing a join for the composite $[n]
\epi P \mono A$, then "forgetting" about the fact we used the epi from
$[n]$.

```agda
      ε : Finite-cover (∫ₚ P) → Lub (B .fst) fam
      ε (covering {card} g surj) =
        cover-reflects-lub surj (Finite-lubs (B .snd) (fam ⊙ g))

      ε' : Lub (B .fst) fam
      ε' = □-rec! ε P-fin

      module ε' = Lub ε'
```

This extension of $f : A \to B$ is [[monotonic|monotone map]], since
it's computed as a join.

```agda
    fold-K-pres-≤
      : ∀ (f : ⌞ A ⌟ → ⌞ B ⌟)
      → (P Q : K-finite-subset)
      → P .fst ⊆ Q .fst
      → fold-K f P B.≤ fold-K f Q
    fold-K-pres-≤ f (P , Pf) Qqf@(Q , Qf) P⊆Q =
      fold-K.ε'.least f P Pf (fold-K f Qqf) λ
        (x , x∈P) → fold-K.ε'.fam≤lub f Q Qf (x , P⊆Q x x∈P)
```

Likewise, it can be shown to preserve binary joins, and the bottom
element.

```agda
    fold-K-∪-≤
      : (f : ⌞ A ⌟ → ⌞ B ⌟) (P Q : K-finite-subset)
      → fold-K f (P ∪ᵏ Q) B.≤ (fold-K f P B.∪ fold-K f Q)
    fold-K-bot-≤ : (f : ⌞ A ⌟ → ⌞ B ⌟) → fold-K f minimalᵏ B.≤ B.bot
```

<details>
<summary>The proofs follow the same pattern as the proof of monotonicity,
so we omit them.
</summary>

```agda
    fold-K-∪-≤ f Ppf@(P , Pf) Qqf@(Q , Qf) =
      fold-K.ε'.least f (P ∪ Q) (union-is-K-finite Pf Qf) _ go where
      go : (i : ∫ₚ (P ∪ Q)) → f (i .fst) B.≤ fold-K f Ppf B.∪ fold-K f Qqf
      go (x , inc (inl p)) = B.≤-trans (fold-K.ε'.fam≤lub f P Pf (x , p)) B.l≤∪
      go (x , inc (inr p)) = B.≤-trans (fold-K.ε'.fam≤lub f Q Qf (x , p)) B.r≤∪
      go (x , squash p q i) = B.≤-thin (go (x , p)) (go (x , q)) i

    fold-K-bot-≤ f = fold-K.ε'.least f minimal minimal-is-K-finite B.bot λ ()
```
</details>

Crucially for the universal property, when applied to a singleton
subset, this extension agrees with our original function. Intuitively,
this is because we're taking the join of a single thing, but we still
have to show this!

```agda
    fold-K-singleton
      : (f : ⌞ A ⌟ → ⌞ B ⌟) (x : ⌞ A ⌟) → f x ≡ fold-K f (singletonᵏ x)
    fold-K-singleton f x = B.≤-antisym
      (ε'.fam≤lub (x , inc refl))
      (ε'.least (f x) λ (y , □x=y) → □-rec!
        (λ x=y → subst (λ ϕ → f ϕ B.≤ f x) x=y B.≤-refl) □x=y)
      where open fold-K f (singleton x) (singleton-is-K-finite (A .is-tr) x)
```

We now have all the ingredients to show that $K$ is a left adjoint.  The
unit of the adjunction takes an element $x : A$ to the singleton set $\{
x \}$, and the universal extension of $f : A \to B$ is as defined above.

```agda
open make-left-adjoint
open is-join-slat-hom
open Subcat-hom

make-free-join-slat : ∀ {ℓ} → make-left-adjoint (Forget-poset {ℓ} {ℓ} F∘ Forget-join-slat)
make-free-join-slat .free A = K[ A ]
make-free-join-slat .unit x = singletonᵏ x
make-free-join-slat .universal {A} {B} f .hom .hom = fold-K A B f
make-free-join-slat .universal {A} {B} f .hom .pres-≤ {P} {Q} =
  fold-K-pres-≤ A B f P Q
make-free-join-slat .universal {A} {B} f .witness .∪-≤ P Q =
  fold-K-∪-≤ A B f P Q
make-free-join-slat .universal {A} {B} f .witness .bot-≤ =
  fold-K-bot-≤ A B f
```

As noted earlier, the extension of $f$ agrees with $f$ on singleton
sets, so the universal extension commutes with the unit of the
adjunction.

```agda
make-free-join-slat .commutes {A} {B} f = ext (fold-K-singleton A B f)
```

Finally, we shall show that the universal extension of $f$ is unique.
Let $g : K(A) \to B$ such that $f = g \circ \{ - \}$, and let $P :
K(A)$. To see that the $g(P) = f'(P)$, note that $f'$ is computed via
taking a join, so it suffices to show that $g$ is *also* computed via a
join over the same family.

By our assumptions, $g$ agrees with $f$ on singleton sets. However,
every K-finite subset $P$ can be described as a (finitely-indexed) join
over the elements of $P$. Furthermore, $g$ preserves all
finitely-indexed joins, so $g$ *must* be computed as a join over the
elements of $P$, which is the same join used to compute the extension of
$f$.

```agda
make-free-join-slat .unique {A} {B} {f} {g} p = ext λ P pfin → lub-unique
  (fold-K.ε'.has-lub A B f P pfin)
  (cast-is-lubᶠ (λ Q → sym (p #ₚ Q .fst)) $
    pres-finitely-indexed-lub (g .witness) pfin _ _ $
    K-singleton-lub A _)
```
