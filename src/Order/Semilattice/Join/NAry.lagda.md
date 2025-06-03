<!--
```agda
open import Cat.Prelude

open import Data.Finset.Properties
open import Data.Fin.Indexed
open import Data.Finset.Base
open import Data.Fin.Finite
open import Data.Fin.Base using (Fin ; suc ; zero ; fsuc ; fzero ; fin-view)
open import Data.Sum.Base

open import Meta.Idiom

open import Order.Semilattice.Join
open import Order.Diagram.Bottom
open import Order.Diagram.Join
open import Order.Diagram.Lub
open import Order.Base

import Order.Semilattice.Join.Reasoning as Joins
```
-->

```agda
module Order.Semilattice.Join.NAry where
```

<!--
```agda
open is-lub
open Lub

module _ {o ℓ} {P : Poset o ℓ} (l : is-join-semilattice P) where
  open Joins l
```
-->

# n-Ary joins

Let $P$ be a [[join semilattice]], and let $f$ be a finite family of
elements of $P$. We can compute joins of $f$ in $P$ via induction on the
size of the family.

```agda
  ⋃ᶠ : ∀ {n} (f : Fin n → ⌞ P ⌟) → ⌞ P ⌟
  ⋃ᶠ {0}           f = bot
  ⋃ᶠ {1}           f = f fzero
  ⋃ᶠ {suc (suc n)} f = f fzero ∪ ⋃ᶠ (λ i → f (fsuc i))

  ⋃ᶠ-inj : ∀ {n} {f : Fin n → Ob} → (i : Fin n) → f i ≤ ⋃ᶠ f
  ⋃ᶠ-inj i with fin-view i
  ⋃ᶠ-inj {1}           .fzero    | zero  = ≤-refl
  ⋃ᶠ-inj {suc (suc n)} .fzero    | zero  = l≤∪
  ⋃ᶠ-inj {suc (suc n)} .(fsuc i) | suc i = ≤-trans (⋃ᶠ-inj i) r≤∪

  ⋃ᶠ-universal
    : ∀ {n} {f : Fin n → Ob} (x : Ob)
    → (∀ i → f i ≤ x) → ⋃ᶠ f ≤ x
  ⋃ᶠ-universal {0} x p = ¡
  ⋃ᶠ-universal {1} x p = p fzero
  ⋃ᶠ-universal {suc (suc n)} x p =
    ∪-universal _ (p fzero) (⋃ᶠ-universal x (p ⊙ fsuc))

  Finite-lubs : ∀ {n} (f : Fin n → Ob) → Lub P f
  Finite-lubs f .lub              = ⋃ᶠ f
  Finite-lubs f .has-lub .fam≤lub = ⋃ᶠ-inj
  Finite-lubs f .has-lub .least   = ⋃ᶠ-universal
```

Furthermore, $P$ must also have joins of [[finitely indexed sets]].
Let $I$ be a finitely indexed set with enumeration $e$, and let $f : I \to P$
be an $I$-indexed family in $P$. $f \circ e$ is a finite family in $P$, so it must
have a least upper bound. Furthermore, $e$ is surjective, so it must reflect the
least upper bound.

<!--
```agda
  ⋃ᶠˢ : Finset ⌞ P ⌟ → ⌞ P ⌟
  ⋃ᶠˢ []       = bot
  ⋃ᶠˢ (x ∷ xs) = x ∪ ⋃ᶠˢ xs
  ⋃ᶠˢ (∷-dup x xs i) = along i $
    x ∪ x ∪ ⋃ᶠˢ xs ≡⟨ ∪.pulll ∪-idem ⟩
    x ∪ ⋃ᶠˢ xs     ∎
  ⋃ᶠˢ (∷-swap x y xs i) = along i $
    x ∪ y ∪ ⋃ᶠˢ xs ≡⟨ ∪.extendl ∪-comm ⟩
    y ∪ x ∪ ⋃ᶠˢ xs ∎
  ⋃ᶠˢ (squash x y p q i j) = hlevel 2 (⋃ᶠˢ x) (⋃ᶠˢ y) (λ i → ⋃ᶠˢ (p i)) (λ i → ⋃ᶠˢ (q i)) i j

  abstract
    ⋃ᶠˢ-inj : {x : ⌞ P ⌟} (xs : Finset ⌞ P ⌟) → x ∈ xs → x ≤ ⋃ᶠˢ xs
    ⋃ᶠˢ-inj {x} xs = ∈ᶠˢ-elim (λ xs _ → x ≤ ⋃ᶠˢ xs) l≤∪ (λ q r → ≤-trans r r≤∪) xs

    ⋃ᶠˢ-univ
      : (xs : Finset ⌞ P ⌟) {o : ⌞ P ⌟}
      → ((x : ⌞ P ⌟) → x ∈ᶠˢ xs → x ≤ o)
      → ⋃ᶠˢ xs ≤ o
    ⋃ᶠˢ-univ xs {o} = Finset-elim-prop (λ xs → ((x : ⌞ P ⌟) → x ∈ᶠˢ xs → x ≤ o) → ⋃ᶠˢ xs ≤ o)
      (λ _ → ¡)
      (λ x ih le → ∪-universal o (le x hereₛ) (ih (λ y w → le y (thereₛ w))))
      xs

    ⋃ᶠˢ-union : (xs ys : Finset ⌞ P ⌟) → ⋃ᶠˢ (xs <> ys) ≡ (⋃ᶠˢ xs ∪ ⋃ᶠˢ ys)
    ⋃ᶠˢ-union xs ys = ≤-antisym
      (⋃ᶠˢ-univ (xs <> ys) λ x m → case ∈ᶠˢ-union _ xs ys m of λ where
        (inl x) → ≤-trans (⋃ᶠˢ-inj xs x) l≤∪
        (inr x) → ≤-trans (⋃ᶠˢ-inj ys x) r≤∪)
      (∪-universal _
        (⋃ᶠˢ-univ xs λ x m → ⋃ᶠˢ-inj (xs <> ys) (unionl-∈ᶠˢ _ xs ys m))
        (⋃ᶠˢ-univ ys λ x m → ⋃ᶠˢ-inj (xs <> ys) (unionr-∈ᶠˢ _ xs ys m)))
```
-->

```agda
  opaque
    Finitely-indexed-lubs
      : ∀ {ℓᵢ} {I : Type ℓᵢ}
      → is-finitely-indexed I
      → (f : I → Ob)
      → Lub P f
    Finitely-indexed-lubs {I = I} fin-indexed f = case fin-indexed of λ cov →
      cover-reflects-lub (cov .is-cover) (Finite-lubs (f ⊙ cov .cover))
      where open Finite-cover
```

Join semilattice homomorphisms must also preserve finite joins. This follows
from another induction on the size of the family we are taking a join over.

```agda
module
  _ {o ℓ o' ℓ'} {P : Poset o ℓ} {Q : Poset o' ℓ'} {f : Monotone P Q} {Pl Ql}
    (hom : is-join-slat-hom f Pl Ql) where abstract

  private
    module Pₗ = is-join-semilattice Pl
    module Qₗ = is-join-semilattice Ql

  open is-join-slat-hom hom

  pres-⋃ᶠ : ∀ {n} (k : Fin n → ⌞ P ⌟) → f · (⋃ᶠ Pl k) ≡ ⋃ᶠ Ql (apply f ⊙ k)
  pres-⋃ᶠ {n = 0} k = pres-bot
  pres-⋃ᶠ {n = 1} k = refl
  pres-⋃ᶠ {n = suc (suc n)} k =
    f · (k fzero Pₗ.∪ ⋃ᶠ Pl (k ⊙ fsuc))       ≡⟨ pres-∪ _ _ ⟩
    f · (k fzero) Qₗ.∪ f · (⋃ᶠ Pl (k ⊙ fsuc)) ≡⟨ ap₂ Qₗ._∪_ refl (pres-⋃ᶠ (k ⊙ fsuc)) ⟩
    ⋃ᶠ Ql (apply f ⊙ k)                       ∎

  pres-⋃ᶠˢ : ∀ xs → f · ⋃ᶠˢ Pl xs ≡ ⋃ᶠˢ Ql (map (f ·_) xs)
  pres-⋃ᶠˢ = Finset-elim-prop _ pres-bot (λ x ih → pres-∪ _ _ ∙ ap₂ Qₗ._∪_ refl ih)

  pres-fin-lub
    : ∀ {n} (k : Fin n → ⌞ P ⌟) (x : ⌞ P ⌟)
    → is-lub P k x
    → is-lub Q (λ x → f · (k x)) (f · x)
  pres-fin-lub k x lub = done where
    rem₁ : x ≡ ⋃ᶠ Pl k
    rem₁ = lub-unique lub (Finite-lubs Pl k .has-lub)

    rem₂ : f · x ≡ ⋃ᶠ Ql (apply f ⊙ k)
    rem₂ = ap (apply f) rem₁ ∙ pres-⋃ᶠ k

    done : is-lub Q (λ x → f · k x) (f · x)
    done = subst (is-lub Q (apply f ⊙ k)) (sym rem₂) (Finite-lubs Ql _ .has-lub)

  pres-finite-lub
    : ∀ {ℓᵢ} {I : Type ℓᵢ}
    → Finite I
    → (k : I → ⌞ P ⌟)
    → (x : ⌞ P ⌟)
    → is-lub P k x
    → is-lub Q (λ x → f · k x) (f · x)
  pres-finite-lub I-finite k x P-lub = ∥-∥-out! do
    li ← I-finite
    let enum = listing→equiv-fin li
    pure $
      cast-is-lub (enum e⁻¹) (λ _ → refl) $
      pres-fin-lub (k ⊙ Equiv.from enum) x $
      cast-is-lub enum (λ x → sym (ap k (Equiv.η enum x))) P-lub
```

As a corollary, join semilattice homomorphisms must also preserve joins of
finitely-indexed sets.

```agda
  pres-finitely-indexed-lub
    : ∀ {ℓᵢ} {I : Type ℓᵢ}
    → is-finitely-indexed I
    → (k : I → ⌞ P ⌟)
    → (x : ⌞ P ⌟)
    → is-lub P k x
    → is-lub Q (λ x → f · k x) (f · x)
  pres-finitely-indexed-lub I-fin-indexed k x P-lub = case I-fin-indexed of λ cov →
    cover-reflects-is-lub (Finite-cover.is-cover cov) $
    pres-fin-lub (k ⊙ Finite-cover.cover cov) x $
    cover-preserves-is-lub (Finite-cover.is-cover cov) P-lub
```
