<!--
```agda
open import 1Lab.Function.Surjection

open import Algebra.Monoid

open import Cat.Displayed.Univalence.Thin
open import Cat.Functor.Adjoint
open import Cat.Prelude

open import Data.Fin.Closure
open import Data.Fin.Base
open import Data.Sum.Base

open import Order.Diagram.Glb
open import Order.Semilattice
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
object of **K**uratowski-finite subsets of $A$, i.e., of predicates $P :
A \to \Omega$ such that the total space $\sum S$ [[merely]] admits a
surjection from some [[standard finite set]] $[n] \epi \sum S$.

```agda
module _ {ℓ} (A : Set ℓ) where
  K-finite-subset : Type ℓ
  K-finite-subset =
    Σ (∣ A ∣ → Ω) λ P →
    ∃ Nat λ n →
    Fin n ↠ Σ ∣ A ∣ (λ x → x ∈ P)
```

The operator we'll choose to make $K(A)$ into a semilattice is subset
union. This is because, under subset union, the universal property of a
free semilattice holds "almost for free": $K$-finite subsets admit a
reduction theorem (which we will prove after we have defined the
semilattice) into a join of singletons, and this theorem will be
necessary to prove the universal property.

```agda
  {- TODO [Amy 2022-12-27] Refactor Data.Power.Lattice so we can "just" use that instead -}
  _∪_ : K-finite-subset → K-finite-subset → K-finite-subset
  (P , pf) ∪ (Q , qf) = (λ x → el ∥ x ∈ P ⊎ x ∈ Q ∥ squash) , do
    (Pn , Pf , Ps) ← pf
    (Qn , Qf , Qs) ← qf
```

Now, the astute reader has probably noticed that, unless $A$ is assumed
to have decidable equality, we can not compute the cardinality of the
union $P \cup Q$ --- and we have placed no such assumption on $A$.
That's why we're using $K$-finite, rather than just "finite", subsets:
since all we have to do is _cover_ the subset with a finite ordinal,
it's not a problem to have duplicated elements.

Put another way, the "size field" of a $K$-finite subset $S$ expresses a
_possible upper bound_ on the size of $S$, and in that case, we do not
need decidable equality: the size of $P \cup Q$ is bounded above by
$s(P) + s(Q)$, where we will abusively write $s$ for "an arbitrary upper
bound". Note that this definition does not require choice to.. choose..
an upper bound, because we're really computing a proposition.

```agda
    let
      cover : Fin Pn ⊎ Fin Qn → Σ ∣ A ∣ (λ x → ∥ x ∈ P ⊎ x ∈ Q ∥)
      cover = λ where
        (inl x) → Pf x .fst , inc (inl (Pf x .snd))
        (inr x) → Qf x .fst , inc (inr (Qf x .snd))
```

Since $[n + k] = [n] \uplus [k]$, and we know how to cover $P$ and $Q$
by $[n]$ and $[k]$ respectively, we can define an epimorphism

$$
[n + k] \simeq [n] \uplus [k] \epi P \cup Q\text{,}
$$

by^[Since we're _merely_ showing that fibres are inhabited, we can treat
$P \cup Q$ as $P \uplus Q$] showing that $\rm{inl}(x)$ (resp.
$\rm{inr}(x)$) is associated with an element in $[n]$ (resp. $[k]$).

```agda
    pure
      $ Pn + Qn
      , (λ x → cover (Equiv.from Finite-coproduct x))
      , λ (elt , elt∈P∪Q) → elt∈P∪Q >>= λ where
        (inl elt∈P) → do
          (pix , path) ← Ps (elt , elt∈P)
          pure ( Equiv.to Finite-coproduct (inl pix)
               , ap cover (Equiv.η Finite-coproduct _)
               ∙ Σ-prop-path hlevel! (ap fst path))
        (inr elt∈Q) → do
          (qix , path) ← Qs (elt , elt∈Q)
          pure ( Equiv.to Finite-coproduct (inr qix)
               , ap cover (Equiv.η Finite-coproduct _)
               ∙ Σ-prop-path hlevel! (ap fst path))
```

Since $K(A)$ is closed under unions (and contains the least element), it
follows that it's a semilattice, being a sub-semilattice of the power
set of $A$. In fact, a different characterisation of $K(A)$ is as the
smallest sub-semilattice of $K(A)$ containing the singletons and closed
under union.

<!--
```agda
  K[_] : Semilattice ℓ
  K[_] = to-semilattice make-ka where
    open make-semilattice
    make-ka : make-semilattice K-finite-subset
    make-ka .has-is-set = hlevel!
    make-ka .top = (λ _ → ⊥Ω) , inc (0 , (λ { () }) , λ { () })
    make-ka .op = _∪_
    make-ka .idl = Σ-prop-path! $ funext λ i →
      Ω-ua (∥-∥-rec! (λ { (inr x) → x ; (inl ()) })) (λ x → inc (inr x))
    make-ka .idempotent = Σ-prop-path! $ funext λ i → Ω-ua
      (∥-∥-rec! (λ { (inl x) → x ; (inr x) → x }))
      (λ x → inc (inl x))
    make-ka .commutative = Σ-prop-path! $ funext λ i → Ω-ua
      (∥-∥-rec squash λ { (inl x) → inc (inr x) ; (inr x) → inc (inl x) })
      (∥-∥-rec squash λ { (inl x) → inc (inr x) ; (inr x) → inc (inl x) })
    make-ka .associative = Σ-prop-path! $ funext λ i → Ω-ua
      (∥-∥-rec squash λ where
        (inl x) → inc (inl (inc (inl x)))
        (inr x) → ∥-∥-rec squash (λ where
          (inl x) → inc (inl (inc (inr x)))
          (inr x) → inc (inr x)) x)
      (∥-∥-rec squash λ where
        (inl x) → ∥-∥-rec squash (λ where
          (inl x) → inc (inl x)
          (inr x) → inc (inr (inc (inl x)))) x
        (inr x) → inc (inr (inc (inr x))))

  private module KA = Semilattice K[_]
  K-fin-lt
    : ∀ {x y : K-finite-subset}
    → (∀ i → i ∈ y .fst → i ∈ x .fst)
    → x KA.≤ y
  K-fin-lt wit = Σ-prop-path! $ funext λ i →
    Ω-ua (λ x → inc (inl x)) (∥-∥-rec! λ { (inl x) → x ; (inr y) → wit _ y })

  K-fin-lt'
    : ∀ {x y : K-finite-subset}
    → x KA.≤ y
    → ∀ i → i ∈ y .fst → i ∈ x .fst
  K-fin-lt' wit idx y' = transport (λ i → idx ∈ wit (~ i) .fst) (inc (inr y'))
```
-->

We shall refer to the singleton-assigning map $A \to K(A)$ as $\eta$,
since it will play the role of our adjunction unit when we establish the
universal property of $K(A)$.

```agda
  ηₛₗ : ∣ A ∣ → K-finite-subset
  ηₛₗ x = (λ y → elΩ (x ≡ y)) , inc (1 , (λ _ → x , inc refl) ,
    λ (y , p) → inc (fzero , Σ-prop-path (λ _ → squash) (out! p)))
```

We can now prove the aforementioned reduction theorem: Every element $S : K(A)$
can be expressed (in a noncanonical way) as the finite union of a
diagram of singletons. This is _almost_ a pure restatement of the
$K$-finiteness condition, but it will be very useful!

```agda
  K-reduce
    : (x : K-finite-subset)
    → ∃ Nat λ n → Σ (Fin n → ∣ A ∣) λ f → is-glb KA.po (λ i → ηₛₗ (f i)) x
  K-reduce (P , P-fin) = ∥-∥-map reduce P-fin where
    open is-glb

    reduce : Σ Nat (λ n → Fin n ↠ Σ ∣ A ∣ (λ x → x ∈ P))
           → Σ Nat λ n → Σ (Fin n → ∣ A ∣) λ f → is-glb KA.po (λ i → ηₛₗ (f i)) (P , P-fin)
    reduce (card , cover , surj) = card , (λ x → cover x .fst) , λ where
      .glb≤fam i →
        K-fin-lt {P , P-fin} {ηₛₗ (cover i .fst)} λ j i=j →
          subst (λ e → ∣ P e ∣) (out! i=j) (cover i .snd)
      .greatest lb' wit → K-fin-lt {lb'} {P , P-fin} λ i i∈p → ∥-∥-proj! do
        (idx , path) ← surj (i , i∈p)
        pure (K-fin-lt' {lb'} {ηₛₗ (cover idx .fst)} (wit idx) i (inc (ap fst path)))
```

In a similar vein, given a map $f : A \to B$ and a semilattice structure
on $B$, we can extend this to a semilattice homomorphism^[Here we
construct the underlying map first, the proof that it's a semilattice
homomorphism `follows`{.Agda ident=pres}] $K(A) \to B$ by first
expressing $S : K(A)$ as $\bigcup_{i:[n]} \eta(a_i)$ for some $n$,
$a_i$, then computing $\bigcap_{i:[n]} f(a_i)$.

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
    : ∀ {ℓ'} (B : Semilattice ℓ')
    → (∣ A ∣ → ⌞ B ⌟)
    → K-finite-subset → ⌞ B ⌟
  fold-K B f (P , P-fin) = Glb.glb ε' module fold-K where
    module B = Semilattice B

    fam : (Σ ∣ A ∣ λ x → ∣ P x ∣) → ⌞ B ⌟
    fam (x , _) = f x
```

We need to do a slight bit of symbol pushing to "pull back", so to
speak, the meet of our family $[n] \epi P \to B$ to a meet of $P \to B$,
using surjectivity of the first map.

```agda
    ε : Σ Nat (λ n → Fin n ↠ Σ ∣ A ∣ (λ x → x ∈ P))
      → Glb B.po fam
    ε (card , g , surj) = glb
      where
        module h = is-glb (B.⋂-is-glb (λ x → fam (g x)))
        glb : Glb B.po fam
        glb .Glb.glb = B.⋂ (λ x → fam (g x))
        glb .Glb.has-glb .is-glb.glb≤fam elt =
          ∥-∥-rec B.≤-thin (λ { (ix , p) →
            B.⋂ (λ x → fam (g x)) B.≤⟨ h.glb≤fam ix ⟩
            fam (g ix)            B.=⟨ ap fam p ⟩
            fam elt               B.≤∎
          }) (surj elt)
        glb .Glb.has-glb .is-glb.greatest lb' lb'<subset =
          h.greatest lb' λ i → lb'<subset (g i)

    ε' : Glb B.po fam
    ε' = ∥-∥-rec (Glb-is-prop B.po) ε P-fin

open is-glb
open make-left-adjoint
make-free-slat : ∀ {ℓ} → make-left-adjoint (Forget-structure (Semilattice-structure ℓ))
make-free-slat .free A = K[ A ]
make-free-slat .unit x = ηₛₗ x
make-free-slat .universal {x} {y} f = total-hom go pres where
  module y = Semilattice y
  open Monoid-hom
  go = fold-K x y f
  module go = fold-K x y f

  pres : Monoid-hom (Semilattice-on.to-monoid (K[ x ] .snd)) (Semilattice-on.to-monoid (y .snd)) _
  pres .pres-id = refl
  pres .pres-⋆ (A , af) (B , bf) =
    glb-unique y.po
      (Glb.has-glb (go.ε' (_∪_ x (A , af) (B , bf) .fst) (_∪_ x (A , af) (B , bf) .snd)))
      (λ where
        .glb≤fam (x , w) → ∥-∥-proj! $ w >>= λ where
          (inl w) → pure $
            Glb.glb g1 y.∩ Glb.glb g2 y.≤⟨ y.∩≤l ⟩
            Glb.glb g1                y.≤⟨ g1.glb≤fam (x , w) ⟩
            _                         y.≤∎
          (inr w) → pure $
            Glb.glb g1 y.∩ Glb.glb g2 y.≤⟨ y.∩≤r ⟩
            Glb.glb g2                y.≤⟨ g2.glb≤fam (x , w) ⟩
            _                         y.≤∎
        .greatest lb' f → y.∩-univ _
          (g1.greatest lb' (λ i → f (_ , inc (inl (i .snd)))))
          (g2.greatest lb' (λ i → f (_ , inc (inr (i .snd))))))
    where
      g1 = go.ε' A af
      g2 = go.ε' B bf
      module g1 = is-glb (Glb.has-glb g1)
      module g2 = is-glb (Glb.has-glb g2)
make-free-slat .commutes {y = y} f = funext λ x → sym y.∩-idr
  where module y = Semilattice y
make-free-slat .unique {x = x} {y = y} {f = f} {g = g} w =
  Homomorphism-path λ arg → ∥-∥-proj (y.Ob-is-set _ _) do
    (card , diagram , glb) ← K-reduce x arg
    let
      path : arg ≡ KA.⋂ λ i → ηₛₗ x (diagram i)
      path = glb-unique KA.po glb (KA.⋂-is-glb λ i → ηₛₗ x (diagram i))
      f' = make-free-slat .universal {x = x} {y = y} f
    pure $
      f' # arg                                 ≡⟨ ap (f' #_) path ⟩
      f' # KA.⋂ (λ i → ηₛₗ x (diagram i))      ≡⟨ slat-pres-⋂ (K[ x ] .snd) (y .snd) _ (f' .preserves) {card} _ ⟩
      y.⋂ (λ i → f' # ηₛₗ x (diagram i))       ≡⟨ ap (y.⋂ {card}) (funext λ i → y.∩-idr) ⟩
      y.⋂ (λ i → f (diagram i))                ≡⟨ ap (y.⋂ {card}) (funext λ i → happly w (diagram i)) ⟩
      y.⋂ {card} (λ i → g # ηₛₗ x (diagram i)) ≡˘⟨ slat-pres-⋂ (K[ x ] .snd) (y .snd) _ (g .preserves) {card} _ ⟩
      g # KA.⋂ (λ i → ηₛₗ x (diagram i))       ≡˘⟨ ap (g #_) path ⟩
      g # arg                                  ∎
  where
    module y = Semilattice y
    module KA = Semilattice K[ x ]
    module go = fold-K x y f
```
