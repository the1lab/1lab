<!--
```agda
open import Algebra.Monoid

open import Cat.Displayed.Univalence.Thin
open import Cat.Functor.Subcategory
open import Cat.Functor.Adjoint
open import Cat.Prelude

open import Data.Fin.Finite.Indexed
open import Data.Fin.Base
open import Data.Sum.Base
open import Data.Power

open import Order.Instances.Pointwise.Diagrams
open import Order.Instances.Pointwise
open import Order.Diagram.Lub
open import Order.Diagram.Glb
open import Order.Semilattice
open import Order.Subposet
open import Order.Base
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
object of [[**K**uratowski-finite subsets]] of $A$, i.e., of predicates
$P : A \to \Omega$ such that the total space $\sum S$ [[merely]] admits
a surjection from some [[standard finite set]] $[n] \epi \sum S$.

```agda
module _ {ℓ} (A : Set ℓ) where
```

Since $K(A)$ is closed under unions (and contains the least element), it
follows that it's a semilattice, being a sub-semilattice of the power
set of $A$. In fact, a different characterisation of $K(A)$ is as the
_smallest_ sub-semilattice of $K(A)$ containing the singletons and
closed under union.

<!--
```agda
  K[_] : Join-semilattice ℓ ℓ
  K[_] .fst = Subposet (Subsets ⌞ A ⌟) λ x → el (is-K-finite x) squash
  K[_] .snd = is-join-subsemilattice
    (Subsets ⌞ A ⌟)
    (record { has-bottom = Subsets-bottom
            ; has-joins  = Subsets-join })
    minimal-is-K-finite
    λ x y → union-is-K-finite {P = x} {Q = y}

  private module KA = Join-semilattice K[_]
```
-->

```agda
  ηₛₗ : ∣ A ∣ → KA.Ob
  ηₛₗ x .fst y = elΩ (x ≡ y)
  ηₛₗ x .snd = singleton-is-K-finite hlevel! x
```

We can now prove the aforementioned reduction theorem: Every element $S
: K(A)$ can be expressed (in a noncanonical way) as the finite union of
a diagram of singletons. This is _almost_ a pure restatement of the
$K$-finiteness condition, but it will be very useful!

```agda
  K[]-coyoneda : (x : KA.Ob) → Type _
  K[]-coyoneda x = Σ Nat λ n → Σ (Fin n → ⌞ A ⌟) λ f → is-lub KA.poset (ηₛₗ ⊙ f) x

  K-reduce : (x : ⌞ K[_] ⌟) → ∥ K[]-coyoneda x ∥
  K-reduce (P , P-fin) = □-tr (□-map reduce P-fin) where
    open is-lub

    reduce : Finite-cover (∫ₚ P) → K[]-coyoneda (P , P-fin)
    reduce (cover cov surj) = _ , (λ x → cov x .fst) , λ where
      .fam≤lub i a ci=a → subst (_∈ P) (out! ci=a) (cov i .snd)
      .least lb′ wit a a∈P → ∥-∥-proj do
        (ix , α) ← surj (a , a∈P)
        pure (wit ix a (inc (ap fst α)))
```

In a similar vein, given a map $f : A \to B$ and a semilattice structure
on $B$, we can extend this to a semilattice homomorphism^[Here we
construct the underlying map first, the proof that it's a semilattice
homomorphism follows.] $K(A) \to B$ by first expressing $S : K(A)$ as
$\bigcup_{i:[n]} \eta(a_i)$ for some $n$, $a_i$, then computing
$\bigcap_{i:[n]} f(a_i)$.

Normally this would only let us compute a map $K(A) \to \| B \|$ into
the support of $B$, since we had to choose an expression for $S$, but it
turns out that the diagram $\bigcap_{i:[n]} f(a_i)$ is not only a glb
for the $f(a_i)$, but also for the family

$$
(\sum_{x : A} P(x)) \xto{\pi_1} A \xto{f} B\text{,}
$$

and since glbs are unique, we can get our computed value out from under
the truncation.

```agda
  fold-K
    : ∀ {ℓ′} (B : Join-semilattice ℓ ℓ′)
    → (∣ A ∣ → ⌞ B ⌟)
    → KA.Ob → ⌞ B ⌟
  fold-K B f (P , P-fin) = Lub.lub ε′ module fold-K where
    module B = Join-semilattice B

    fam : (Σ ∣ A ∣ λ x → ∣ P x ∣) → ⌞ B ⌟
    fam (x , _) = f x
```

We need to do a slight bit of symbol pushing to "pull back", so to
speak, the meet of our family $[n] \epi P \to B$ to a meet of $P \to B$,
using surjectivity of the first map.

```agda
    opaque
      ε : Finite-cover (∫ₚ P) → Lub B.poset fam
      ε (cover {card} g surj) = lub where
        module h = Lub (Fin-joins B.has-is-join-semilattice (λ x → fam (g x)))
        lub : Lub B.poset fam
        lub .Lub.lub = _
        lub .Lub.has-lub .is-lub.fam≤lub elt = ∥-∥-proj do
          (ix , p) ← surj elt
          pure $ fam elt     B.=⟨ ap fam (sym p) ⟩
                 fam (g ix)  B.≤⟨ h.fam≤lub ix ⟩
                 h.lub       B.≤∎
        lub .Lub.has-lub .is-lub.least lb′ subset<lb′ =
          h.least lb′ λ i → subset<lb′ (g i)

    ε′ : Lub B.poset fam
    ε′ = □-rec! {pa = Lub-is-prop B.poset} ε P-fin
```

```agda
open is-glb
open make-left-adjoint
make-free-slat : ∀ {ℓ} → make-left-adjoint (Forget-join-semilattice ℓ ℓ)
make-free-slat .free A = K[ A ]
make-free-slat .unit x = ηₛₗ x
make-free-slat .universal {x} {y} f = done module slat-universal where
  module Kx = Join-semilattice K[ x ]
  module y = Join-semilattice y
  module go = fold-K x y f
  go = fold-K x y f

  monotone : (P Q : ⌞ K[ x ] ⌟) → (∀ i → i ∈ P .fst → i ∈ Q .fst) → go P y.≤ go Q
  monotone P Q P≤Q = fold-K.ε′ x y f (P .fst) (P .snd) .Lub.least (go Q)
    λ (i , i∈P) → fold-K.ε′ x y f (Q .fst) (Q .snd) .Lub.fam≤lub (i , P≤Q i i∈P)

  opaque
    unfolding minimal-is-K-finite fold-K.ε
    pres-⊥ : go Kx.bot ≡ y.bot
    pres-⊥ = refl

  module _ (P Q : ⌞ K[ x ] ⌟) where
    private
      gou = fold-K.ε′ x y f ((P Kx.∪ Q) .fst) ((P Kx.∪ Q) .snd)
      gop = fold-K.ε′ x y f (P .fst) (P .snd)
      goq = fold-K.ε′ x y f (Q .fst) (Q .snd)

    pres-∪ : go (P Kx.∪ Q) ≡ go P y.∪ go Q
    pres-∪ = y.≤-antisym
      (gou .Lub.least _ λ (i , i∈cup) → □-rec!
        [ (λ i∈P → y.≤-trans (gop .Lub.fam≤lub (i , i∈P)) (y.l≤∪ _ _))
        , (λ i∈Q → y.≤-trans (goq .Lub.fam≤lub (i , i∈Q)) (y.r≤∪ _ _))
        ]
        i∈cup)
      (y.∪-universal _ _ _
        (gop .Lub.least _ λ (i , i∈P) → gou .Lub.fam≤lub (i , inc (inl i∈P)))
        (goq .Lub.least _ λ (i , i∈Q) → gou .Lub.fam≤lub (i , inc (inr i∈Q))))

  open preserves-finite-joins

  done : Join-semilattices.Hom (make-free-slat .free x) y
  done .Subcat-hom.hom .hom = go
  done .Subcat-hom.hom .preserves = monotone
  done .Subcat-hom.witness .pres-bottoms = preserves-bottom Kx.has-bottom y.has-bottom go pres-⊥
  done .Subcat-hom.witness .pres-joins = preserves-join Kx.has-joins y.has-joins go pres-∪

  opaque
    unfolding fold-K.ε singleton-is-K-finite

    comm : f ≡ (λ i → go (ηₛₗ x i))
    comm = funext λ x → sym (y.∪-idr _)

make-free-slat .commutes {x} {y} f = slat-universal.comm {x = x} {y} f

make-free-slat .unique {x = x} {y = y} {f = f} {g = g} w =
  Subcat-hom-path $ Homomorphism-path λ kf → ∥-∥-rec hlevel! (comm kf) (K-reduce x kf) where
  module Kx = Join-semilattice K[ x ]
  module y = Join-semilattice y

  comm : (kf : ⌞ K[ x ] ⌟) (red : K[]-coyoneda x kf)
       → fold-K x y f kf ≡ g # kf
  comm kf (card , dia , lub) =
    fh # kf                          ≡⟨ ap (fh #_) (lub-unique Kx.poset lub h.has-lub) ⟩
    fh # Kx.⋃ (λ i → ηₛₗ x (dia i))  ≡⟨ preserves-fin-joins (K[ x ] .snd) (y .snd) _ (fh .Subcat-hom.witness) (λ i → ηₛₗ x (dia i)) ⟩
    y.⋃ (λ i → fh # ηₛₗ x (dia i))   ≡⟨ ap (y.⋃ {n = card}) (funext λ i → sym (slat-universal.comm {x = x} {y} f) $ₚ dia i) ⟩
    y.⋃ (λ i → f (dia i))            ≡⟨ ap (y.⋃ {n = card}) (funext λ i → w $ₚ dia i) ⟩
    y.⋃ (λ i → g # ηₛₗ x (dia i))    ≡⟨ sym (preserves-fin-joins (K[ x ] .snd) (y .snd) _ (g .Subcat-hom.witness) (λ i → ηₛₗ x (dia i))) ⟩
    g # Kx.⋃ (λ i → ηₛₗ x (dia i))   ≡˘⟨ ap (g #_) (lub-unique Kx.poset lub h.has-lub) ⟩
    g # kf                           ∎
    where
    module h = Lub (Fin-joins Kx.has-is-join-semilattice (λ i → ηₛₗ x (dia i)))
    fh   = slat-universal.done {x = x} {y} f
```
