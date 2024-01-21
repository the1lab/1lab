open import 1Lab.Reflection.Induction
open import 1Lab.HLevel
open import 1Lab.Path hiding (J)
open import 1Lab.Type

open import Data.Set.Truncation hiding (∥-∥₀-elim)
open import Data.Wellfounded.W hiding (W-elim; P)
open import Data.Fin.Base hiding (Fin-elim)
open import Data.Id.Base

open import Homotopy.Space.Circle hiding (S¹-elim)

module 1Lab.Reflection.Induction.Examples where

unquoteDecl Fin-elim = make-elim Fin-elim (quote Fin)

_ : {ℓ : Level} {P : {n : Nat} (f : Fin n) → Type ℓ}
    (P0 : {n : Nat} → P fzero)
    (Psuc : {n : Nat} (f : Fin n) (Pf : P f) → P (fsuc f))
    {n : Nat} (f : Fin n) → P f
_ = Fin-elim

unquoteDecl J = make-elim-with default-elim-visible J (quote _≡ᵢ_)

_ : {ℓ : Level} {A : Type ℓ} {x : A} {ℓ₁ : Level}
    (P : (z : A) (z₁ : x ≡ᵢ z) → Type ℓ₁)
    (Prefl : P x reflᵢ)
    (y : A) (p : x ≡ᵢ y) → P y p
_ = J

unquoteDecl W-elim = make-elim W-elim (quote W)

_ : {ℓ ℓ' : Level} {A : Type ℓ} {B : (z : A) → Type ℓ'}
    {ℓ₁ : Level} {P : (w : W A B) → Type ℓ₁}
    (Psup : (x : A) (f : (z : B x) → W A B) (Pf : (z : B x) → P (f z)) → P (sup x f))
    (w : W A B) → P w
_ = W-elim

unquoteDecl S¹-elim = make-elim S¹-elim (quote S¹)
unquoteDecl S¹-elim-prop = make-elim-n 1 S¹-elim-prop (quote S¹)

_ : {ℓ : Level} {P : (s : S¹) → Type ℓ}
    (Pbase : P base)
    (Ploop : PathP (λ i → P (loop i)) Pbase Pbase)
    (s : S¹) → P s
_ = S¹-elim

_ : {ℓ : Level} {P : (s : S¹) → Type ℓ}
  → (∀ s → is-prop (P s))
  → P base → ∀ s → P s
_ = S¹-elim-prop

unquoteDecl ∥-∥₀-elim = make-elim-n 2 ∥-∥₀-elim (quote ∥_∥₀)

_ : {ℓ : Level} {A : Type ℓ} {ℓ₁ : Level} {P : (z : ∥ A ∥₀) → Type ℓ₁}
    (h : (z : ∥ A ∥₀) → is-hlevel (P z) 2)
    (Pinc : (z : A) → P (inc z))
    (x : ∥ A ∥₀) → P x
_ = ∥-∥₀-elim

-- Test case: this should not generate unsolved metavariables.
unquoteDecl Nat-rec = make-elim-with (record default-rec { hide-cons-args = true }) Nat-rec (quote Nat)

_ : {ℓ : Level} {P : Type ℓ}
  → P
  → ({n : Nat} → P → P)
  → Nat → P
_ = Nat-rec
