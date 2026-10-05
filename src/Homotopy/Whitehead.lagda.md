<!--
```agda
open import 1Lab.Path.Reasoning
open import 1Lab.Prelude

open import Algebra.Group.Cat.Base
open import Algebra.Group.Homotopy
open import Algebra.Group

open import Data.Set.Truncation

open import Homotopy.Space.Delooping
open import Homotopy.Conjugation
open import Homotopy.Loopspace
```
-->

```agda
module Homotopy.Whitehead where
```

# Whitehead's theorem

In classical homotopy theory, **Whitehead's theorem** states that if a function
$f : A \to B$ induces [[isomorphisms|quasi-inverse]] between $\pi_n(A, a)$ and $\pi_n(B, f(a))$
for all points $a$ in $A$, it is itself an [[equivalence]].

In homotopy type theory however, this statement doesn't not hold in general.
Instead we can prove it for any [[n-types]] by induction on n by first constructing
an equivalence between the trivial higher loopspace and working downward from there.

```agda
Ω¹-map-is-equiv→is-cancellable
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B)
  → is-equiv (∥-∥₀-map f)
  → (∀ x → is-equiv (Ω¹-map {A = (A , x)} (f , refl) .fst))
  → {x y : A} → (x ≡ y) ≃ (f x ≡ f y)
Ω¹-map-is-equiv→is-cancellable f is-eqv Ω¹-is-equiv {x} {y} =
  ap f , is-equiv-if-inhabited→is-equiv (ap f) isequiv where
    x≡y : f x ≡ f y → ∥ x ≡ y ∥
    x≡y p = ∥-∥₀-path-equiv .fst $ equiv→inverse (equiv→cancellable is-eqv) (ap inc p)

    ap-is-equiv-on-loop : is-equiv {A = x ≡ x} (ap f)
    ap-is-equiv-on-loop =
      subst is-equiv (λ i → Ω¹-map-refl {A = _ , x} f i .fst) (Ω¹-is-equiv x)

    ap-is-equiv' : (p : x ≡ y) → is-equiv {A = x ≡ y} (ap f)
    ap-is-equiv' = J (λ y _ → is-equiv {A = x ≡ y} (ap f)) ap-is-equiv-on-loop

    isequiv : f x ≡ f y → is-equiv (ap f)
    isequiv p = ∥-∥-rec (is-equiv-is-prop _) ap-is-equiv' (x≡y p)

Ω¹-map-is-equiv→is-equiv
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B)
  → is-equiv (∥-∥₀-map f)
  → (∀ x → is-equiv (Ω¹-map {A = A , x} (f , refl) .fst))
  → is-equiv f
Ω¹-map-is-equiv→is-equiv {A = A} {B} f is-eqv Ω¹-is-equiv =
  embeding-∥-∥₀-surjective→is-equiv f
    (is-equiv→is-surjective is-eqv)
    (cancellable→embedding (Ω¹-map-is-equiv→is-cancellable f is-eqv Ω¹-is-equiv e⁻¹))

π-map-is-equiv→is-equiv
  : ∀ {ℓ} n {A : Type ℓ} {B : Type ℓ}
  → is-hlevel A n → is-hlevel B n
  → (f : A → B)
  → is-equiv (∥-∥₀-map f)
  → (∀ x k → is-equiv (πₙ₊₁-map {A = A , x} k (f , refl)))
  → is-equiv f
π-map-is-equiv→is-equiv zero A-hlvl B-hlvl f is-eqv π-is-equiv =
  is-contr→is-equiv A-hlvl B-hlvl
π-map-is-equiv→is-equiv (suc n) {A} A-hlvl B-hlvl f is-eqv π-is-equiv = isequiv where
  π-ap-is-equiv : ∀ x y k (p : x ≡ y) → is-equiv (πₙ₊₁-map {A = _ , p} k (ap f , refl))
  π-ap-is-equiv x y k =
    J (λ _ p → is-equiv (πₙ₊₁-map {A = _ , p} k (ap f , refl)))
      (substd is-equiv (π-suc-naturalP k (f , refl) ▷ ap (πₙ₊₁-map k) (Ω¹-map-refl f))
        (π-is-equiv x (suc k)))

  step : (x : A) → is-equiv (Ω¹-map (f , refl) .fst)
  step x = π-map-is-equiv→is-equiv n
    (Path-is-hlevel' _ A-hlvl x x)
    (Path-is-hlevel' _ B-hlvl (f x) (f x))
    (Ω¹-map (f , refl) .fst)
    (π-is-equiv x 0)
    (λ p k → substd (λ f → is-equiv (πₙ₊₁-map k f))
      (symP (Ω¹-map-refl' f p))
      (π-ap-is-equiv x x k p))

  isequiv : is-equiv f
  isequiv = Ω¹-map-is-equiv→is-equiv f is-eqv step
```
