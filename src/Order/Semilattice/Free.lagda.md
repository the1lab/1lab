<!--
```agda
open import Algebra.Monoid

open import Cat.Functor.Adjoint
open import Cat.Functor.Subcategory
open import Cat.Prelude

open import Data.Fin.Closure
open import Data.Fin.Indexed
open import Data.Fin.Finite
open import Data.Fin.Base
open import Data.Sum.Base
open import Data.Power

open import Order.Base
open import Order.Subposet
open import Order.Diagram.Lub
open import Order.Semilattice.Join
open import Order.Semilattice.Join.Subsemilattice
open import Order.Instances.Pointwise

import Order.Semilattice.Join.Reasoning
```
-->

```agda
module Order.Semilattice.Free where
```

# Free (semi)lattices

We construct the free semilattice on a type $A$, i.e., a lattice
$K(A)$^[The reason for the name $K(A)$ will become clear soon!] having
the property that $\hom_{\rm{SLat}}(K(A), B) \cong (A \to B)$, where on
the right we have ordinary functions from $A$ to the (underlying set of)
$B$. We'll actually construct $K$ in two different ways: first
impredicatively, then higher-inductively.

## Impredicatively

The impredicative construction of $K(A)$ is as follows: $K(A)$ is the
object of [[kuratowski-finite-subsets]] of $A$, i.e., of predicates $P :
A \to \Omega$ such that the total space $\sum S$ [[merely]] admits a
surjection from some [[standard finite set]] $[n] \epi \sum S$.

```agda
module _ {ℓ} (A : Set ℓ) where
  K-finite-subset : Type ℓ
  K-finite-subset = Σ[ P ∈ (∣ A ∣ → Ω) ] (is-K-finite P)
```

The operator we'll choose to make $K(A)$ into a semilattice is subset
union. This is because, under subset union, the universal property of a
free semilattice holds "almost for free": $K$-finite subsets admit a
reduction theorem (which we will prove after we have defined the
semilattice) into a join of singletons, and this theorem will be
necessary to prove the universal property.

```agda
  _∪ᵏ_ : K-finite-subset → K-finite-subset → K-finite-subset
  (P , pf) ∪ᵏ (Q , qf) = P ∪ Q , union-is-K-finite {P = P} {Q = Q} pf qf
```

```agda
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

  private module KA = Order.Semilattice.Join.Reasoning K[_]
```
-->

We shall refer to the singleton-assigning map $A \to K(A)$ as $\eta$,
since it will play the role of our adjunction unit when we establish the
universal property of $K(A)$.

```agda
  singletonᵏ : ∣ A ∣ → K-finite-subset
  singletonᵏ x = singleton x , singleton-is-K-finite (A .is-tr) x
```

We can now prove the aforementioned reduction theorem: Every element $S : K(A)$
can be expressed (in a noncanonical way) as the finite union of a
diagram of singletons. This is _almost_ a pure restatement of the
$K$-finiteness condition, but it will be very useful!

```agda
  K-reduce
    : (x : K-finite-subset)
    → ∃ Nat λ n → Σ (Fin n → ∣ A ∣) λ f → is-lub KA.po (λ i → singletonᵏ (f i)) x
  K-reduce (P , P-fin) = □-rec! (pure ⊙ reduce) P-fin where
    open is-lub

    reduce
      : Finite-cover (∫ₚ P) 
      → Σ Nat λ n → Σ (Fin n → ∣ A ∣) λ f → is-lub KA.po (λ i → singletonᵏ (f i)) (P , P-fin)
    reduce (cover {card} covers surj) = card , fst ⊙ covers , λ where
      .fam≤lub i j i=j →
       subst (λ ϕ → ∣ P ϕ ∣) (out! i=j) (covers i .snd)
      .least ub wit i i∈P → ∥-∥-proj! do
        (idx , path) ← surj (i , i∈P)
        pure (wit idx i (inc (ap fst path)))
```

<!--
```agda
  K-singleton-lub
    : (P : K-finite-subset)
    → is-lub KA.po {I = ∫ₚ (P .fst)} (singletonᵏ ⊙ fst) P
  K-singleton-lub P = subposet-has-lub _ (P .snd) (subset-singleton-lub _)
```
-->

In a similar vein, given a map $f : A \to B$ and a semilattice structure
on $B$, we can extend this to a semilattice homomorphism^[Here we
construct the underlying map first, the proof that it's a semilattice
homomorphism `follows`{.Agda ident=pres}] $K(A) \to B$ by first
expressing $S : K(A)$ as $\bigcup_{i:[n]} \eta(a_i)$ for some $n$,
$a_i$, then computing $\bigcup_{i:[n]} f(a_i)$.

Normally this would only let us compute a map $K(A) \to \| B \|$ into
the support of $B$, since we had to choose an expression for $S$, but it
turns out that the diagram $\bigcup_{i:[n]} f(a_i)$ is not only a lub
for the $f(a_i)$, but also for the family

$$
(\sum_{x : A} P(x)) \xto{\pi_1} A \xto{f} B\text{,}
$$

and since lubs are unique, we can get our computed value out from under
the truncation.

```agda
  module _ {o ℓ'} (B : Join-semilattice o ℓ') where
    private module B = Order.Semilattice.Join.Reasoning B

    fold-K : (∣ A ∣ → ⌞ B ⌟) → K-finite-subset → ⌞ B ⌟
    fold-K f (P , P-fin) = Lub.lub ε' module fold-K where

      fam : (Σ ∣ A ∣ λ x → ∣ P x ∣) → ⌞ B ⌟
      fam (x , _) = f x
```

We need to do a slight bit of symbol pushing to "pull back", so to
speak, the join of our family $[n] \epi P \to B$ to a join of $P \to B$,
using surjectivity of the first map.

```agda
      ε : Finite-cover (∫ₚ P) → Lub B.po fam
      ε (cover {card} g surj) =
        cover-reflects-lub B.po surj (B.Finite-lubs (fam ⊙ g))

      ε' : Lub B.po fam
      ε' = □-rec! {pa = Lub-is-prop B.po} ε P-fin

      module ε' = Lub ε'
```

```agda
    fold-K-pres-≤
      : ∀ (f : ⌞ A ⌟ → ⌞ B ⌟)
      → (P Q : K-finite-subset)
      → P .fst ⊆ Q .fst
      → fold-K f P B.≤ fold-K f Q
    fold-K-pres-≤ f P Q P⊆Q =
      fold-K.ε'.least f (P .fst) (P .snd) (fold-K f Q) λ where
        (x , x∈P) → fold-K.ε'.fam≤lub f (Q .fst) (Q .snd) (x , (P⊆Q x x∈P))

    fold-K-∪-≤
      : ∀ (f : ⌞ A ⌟ → ⌞ B ⌟)
      → (P Q : K-finite-subset)
      → fold-K f (P ∪ᵏ Q) B.≤ (fold-K f P B.∪ fold-K f Q)
    fold-K-∪-≤ f P Q =
      fold-K.ε'.least f (P .fst ∪ Q .fst) (union-is-K-finite (P .snd) (Q .snd))
        (fold-K f P B.∪ fold-K f Q) λ where
          (x , x∈P∪Q) →
            ∥-∥-rec B.≤-thin
              [ (λ x∈P →
                B.≤-trans (fold-K.ε'.fam≤lub f (P .fst) (P .snd) (x , x∈P)) B.l≤∪)
              , (λ x∈Q →
                B.≤-trans (fold-K.ε'.fam≤lub f (Q .fst) (Q .snd) (x , x∈Q)) B.r≤∪)
              ]
              x∈P∪Q

    fold-K-bot-≤
      : ∀ (f : ⌞ A ⌟ → ⌞ B ⌟)
      → fold-K f minimalᵏ B.≤ B.bot
    fold-K-bot-≤ f =
      fold-K.ε'.least f minimal minimal-is-K-finite B.bot λ ()

    fold-K-singleton
      : ∀ (f : ⌞ A ⌟ → ⌞ B ⌟) (x : ⌞ A ⌟)
      → f x ≡ fold-K f (singletonᵏ x)
    fold-K-singleton f x =
      B.≤-antisym
        (fold-K.ε'.fam≤lub f (singleton x) (singleton-is-K-finite (A .is-tr) x) (x , inc refl))
        (fold-K.ε'.least f (singleton x) (singleton-is-K-finite (A .is-tr) x) (f x) λ where
          (y , □x=y) → □-rec! {pa = B.≤-thin}
            (λ x=y → subst (λ ϕ → f ϕ B.≤ f x) x=y B.≤-refl)
            □x=y)
```

```
open make-left-adjoint
open Subcat-hom

make-free-join-slat : ∀ {ℓ} → make-left-adjoint (Forget-poset {ℓ} {ℓ} F∘ Forget-join-slat)
make-free-join-slat .free A = K[ A ]
make-free-join-slat .unit x = singletonᵏ x
make-free-join-slat .universal {A} {B} f .hom .hom =
  fold-K A B f
make-free-join-slat .universal {A} {B} f .hom .pres-≤ {P} {Q} =
  fold-K-pres-≤ A B f P Q
make-free-join-slat .universal {A} {B} f .witness .is-join-slat-hom.∪-≤ P Q =
  fold-K-∪-≤ A B f P Q
make-free-join-slat .universal {A} {B} f .witness .is-join-slat-hom.bot-≤ =
  fold-K-bot-≤ A B f
make-free-join-slat .commutes {A} {B} f = ext λ x →
  fold-K-singleton A B f x
make-free-join-slat .unique {A} {B} {f} {g} p = ext λ P →
  lub-unique B.po
    (fold-K.ε'.has-lub A B f (P .fst) (P .snd))
    (cast-is-lubᶠ B.po (λ Q → sym (p #ₚ Q .fst)) $
    is-join-slat-hom.pres-finitely-indexed-lub (g .witness) (P .snd) _ _ $
    K-singleton-lub A _)
  where
    module B = Order.Semilattice.Join.Reasoning B
```
