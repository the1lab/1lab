```agda
open import Algebra.Semilattice

open import Cat.Prelude

open import Data.Nat.Properties
open import Data.Fin.Closure
open import Data.Nat.Order
open import Data.Fin.Base
open import Data.Sum.Base

open import Principles.Resizing

module Algebra.Lattice.Free where
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
A \to \Omega$ such that the total space $\sum S$ [merely] admits a
surjection from some [finite ordinal] $[n] \epi \sum S$.

[merely]: 1Lab.HIT.Truncation.html
[finite ordinal]: Data.Fin.Base.html

```agda
module _ {ℓ} (A : Set ℓ) where
  K-finite-subset : Type ℓ
  K-finite-subset =
    Σ (∣ A ∣ → Ω) λ P →
    ∃ Nat λ n →
    Σ (Fin n → (Σ ∣ A ∣ λ x → ∣ P x ∣)) λ f →
      ∀ x → ∥ fibre f x ∥

  _∪_ : K-finite-subset → K-finite-subset → K-finite-subset
  (P , pf) ∪ (Q , qf) = (λ x → el ∥ ∣ P x ∣ ⊎ ∣ Q x ∣ ∥ squash) , do
    (Pn , Pf , Ps) ← pf
    (Qn , Qf , Qs) ← qf
    let
      cover : Fin Pn ⊎ Fin Qn → Σ ∣ A ∣ (λ x → ∥ ∣ P x ∣ ⊎ ∣ Q x ∣ ∥)
      cover = λ where
        (inl x) → Pf x .fst , inc (inl (Pf x .snd))
        (inr x) → Qf x .fst , inc (inr (Qf x .snd))
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

  ηₛₗ : ∣ A ∣ → K-finite-subset
  ηₛₗ x = (λ y → elΩ (x ≡ y)) , inc (1 , (λ _ → x , inc refl) ,
    λ (y , p) → inc (fzero , Σ-prop-path (λ _ → squash) (out! p)))

  -- fold-K
  --   : ∀ {ℓ′} {B : Type ℓ′}
  --   → Semilattice-on B
  --   → (∣ A ∣ → B)
  --   → K-finite-subset → B
  -- fold-K {B = B} Bsl f (P , P-fin) = {!   !} where
  --   module B = Semilattice-on Bsl
  --   ⋀ : (n : Nat) → (Fin n → B) → B
  --   ⋀ zero f    = {!   !}
  --   ⋀ (suc n) f = {!   !}

  --   ε : Σ Nat (λ n → Σ (Fin n → Σ ∣ A ∣ λ x → ∣ P x ∣) λ f → ∀ x → ∥ fibre f x ∥)
  --     → B
  --   ε (x , f , surj) = {!   !}

  --   ε-const : ∀ x y → ε x ≡ ε y
  --   ε-const x y = {!   !}

  --   ε′ : B
  --   ε′ = ∥-∥-rec-set ε ε-const B.has-is-set P-fin
```
