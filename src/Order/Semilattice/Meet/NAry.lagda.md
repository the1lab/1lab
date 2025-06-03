<!--
```agda
open import Cat.Prelude

open import Data.Finset.Properties
open import Data.Fin.Indexed
open import Data.Finset.Base
open import Data.Fin.Finite
open import Data.Fin.Base using (Fin ; fsuc ; fzero ; suc ; zero ; fin-view)
open import Data.Sum.Base

open import Meta.Idiom

open import Order.Semilattice.Meet
open import Order.Diagram.Meet
open import Order.Diagram.Glb
open import Order.Diagram.Top
open import Order.Base

import Order.Semilattice.Meet.Reasoning as Meets
```
-->

```agda
module Order.Semilattice.Meet.NAry where
```

<!--
```agda
open is-glb
open Glb

module _ {o ℓ} {P : Poset o ℓ} (l : is-meet-semilattice P) where
  open Meets l
```
-->

# n-Ary meets

Let $P$ be a [[meet semilattice]], and let $f$ be a finite family of
elements of $P$. We can compute meets of $f$ in $P$ via induction on the
size of the family.

```agda
  ⋂ᶠ : ∀ {n} (f : Fin n → Ob) → Ob
  ⋂ᶠ {0}           f = top
  ⋂ᶠ {1}           f = f fzero
  ⋂ᶠ {suc (suc n)} f = f fzero ∩ ⋂ᶠ (λ i → f (fsuc i))

  ⋂ᶠ-proj : ∀ {n} {f : Fin n → Ob} (i : Fin n) → ⋂ᶠ f ≤ f i
  ⋂ᶠ-proj i with fin-view i
  ⋂ᶠ-proj {1}           .fzero    | zero  = ≤-refl
  ⋂ᶠ-proj {suc (suc n)} .fzero    | zero  = ∩≤l
  ⋂ᶠ-proj {suc (suc n)} .(fsuc i) | suc i = ≤-trans ∩≤r (⋂ᶠ-proj i)

  ⋂ᶠ-universal
    : ∀ {n} {f : Fin n → Ob} (x : Ob)
    → (∀ i → x ≤ f i) → x ≤ ⋂ᶠ f
  ⋂ᶠ-universal {n = 0} {f = f} x p = !
  ⋂ᶠ-universal {n = 1} {f = f} x p = p fzero
  ⋂ᶠ-universal {n = suc (suc n)} {f = f} x p =
    ∩-universal _ (p fzero) (⋂ᶠ-universal x (p ⊙ fsuc))

  Finite-glbs : ∀ {n} (f : Fin n → Ob) → Glb P f
  Finite-glbs f .Glb.glb = ⋂ᶠ f
  Finite-glbs f .Glb.has-glb .is-glb.glb≤fam = ⋂ᶠ-proj
  Finite-glbs f .Glb.has-glb .is-glb.greatest = ⋂ᶠ-universal
```

<!--
```agda
  ⋂ᶠˢ : Finset ⌞ P ⌟ → ⌞ P ⌟
  ⋂ᶠˢ []       = top
  ⋂ᶠˢ (x ∷ xs) = x ∩ ⋂ᶠˢ xs
  ⋂ᶠˢ (∷-dup x xs i) = along i $
    x ∩ x ∩ ⋂ᶠˢ xs ≡⟨ ∩.pulll ∩-idem ⟩
    x ∩ ⋂ᶠˢ xs     ∎
  ⋂ᶠˢ (∷-swap x y xs i) = along i $
    x ∩ y ∩ ⋂ᶠˢ xs ≡⟨ ∩.extendl ∩-comm ⟩
    y ∩ x ∩ ⋂ᶠˢ xs ∎
  ⋂ᶠˢ (squash x y p q i j) = hlevel 2 (⋂ᶠˢ x) (⋂ᶠˢ y) (λ i → ⋂ᶠˢ (p i)) (λ i → ⋂ᶠˢ (q i)) i j

  abstract
    ⋂ᶠˢ-proj : {x : ⌞ P ⌟} (xs : Finset ⌞ P ⌟) → x ∈ xs → ⋂ᶠˢ xs ≤ x
    ⋂ᶠˢ-proj {x} xs = ∈ᶠˢ-elim (λ xs _ → ⋂ᶠˢ xs ≤ x) ∩≤l (λ q r → ≤-trans ∩≤r r) xs

    ⋂ᶠˢ-univ
      : (xs : Finset ⌞ P ⌟) {o : ⌞ P ⌟}
      → ((x : ⌞ P ⌟) → x ∈ᶠˢ xs → o ≤ x)
      → o ≤ ⋂ᶠˢ xs
    ⋂ᶠˢ-univ xs {o} = Finset-elim-prop (λ xs → ((x : ⌞ P ⌟) → x ∈ᶠˢ xs → o ≤ x) → o ≤ ⋂ᶠˢ xs)
      (λ _ → !)
      (λ x ih le → ∩-universal o (le x hereₛ) (ih (λ y w → le y (thereₛ w))))
      xs

    ⋂ᶠˢ-union : (xs ys : Finset ⌞ P ⌟) → ⋂ᶠˢ (xs <> ys) ≡ (⋂ᶠˢ xs ∩ ⋂ᶠˢ ys)
    ⋂ᶠˢ-union xs ys = ≤-antisym
      (∩-universal _
        (⋂ᶠˢ-univ xs λ x m → ⋂ᶠˢ-proj (xs <> ys) (unionl-∈ᶠˢ _ xs ys m))
        (⋂ᶠˢ-univ ys λ y m → ⋂ᶠˢ-proj (xs <> ys) (unionr-∈ᶠˢ _ xs ys m)))
      (⋂ᶠˢ-univ (xs <> ys) λ x m → case ∈ᶠˢ-union _ xs ys m of λ where
        (inl x) → ≤-trans ∩≤l (⋂ᶠˢ-proj xs x)
        (inr x) → ≤-trans ∩≤r (⋂ᶠˢ-proj ys x))
```
-->

Furthermore, $P$ must also have meets of [[finitely indexed sets]].
Let $I$ be a finitely indexed set with enumeration $e$, and let $f : I \to P$
be an $I$-indexed family in $P$. $f \circ e$ is a finite family in $P$, so it must
have a meet. Furthermore, $e$ is surjective, so it must reflect the
meet.

```agda
  opaque
    Finitely-indexed-glbs
      : ∀ {ℓᵢ} {I : Type ℓᵢ}
      → is-finitely-indexed I
      → (f : I → Ob)
      → Glb P f
    Finitely-indexed-glbs {I = I} fin-indexed f = case fin-indexed of λ cov →
      cover-reflects-glb (cov .is-cover) (Finite-glbs (f ⊙ cov .cover))
      where open Finite-cover
```

Meet semilattice homomorphisms must also preserve finite meets. This follows
from another induction on the size of the family we are taking a meet over.

```agda
module
  _ {o ℓ o' ℓ'} {P : Poset o ℓ} {Q : Poset o' ℓ'} {f : Monotone P Q} {Pl Ql}
    (hom : is-meet-slat-hom f Pl Ql) where abstract

  private
    module Pₗ = is-meet-semilattice Pl
    module Qₗ = is-meet-semilattice Ql

  open is-meet-slat-hom hom

  pres-⋂ᶠ : ∀ {n} (k : Fin n → ⌞ P ⌟) → f · (⋂ᶠ Pl k) ≡ ⋂ᶠ Ql (apply f ⊙ k)
  pres-⋂ᶠ {n = 0} k = pres-top
  pres-⋂ᶠ {n = 1} k = refl
  pres-⋂ᶠ {n = suc (suc n)} k =
    f · (k fzero Pₗ.∩ ⋂ᶠ Pl (k ⊙ fsuc))      ≡⟨ pres-∩ _ _ ⟩
    f · (k fzero) Qₗ.∩ f · ⋂ᶠ Pl (k ⊙ fsuc)  ≡⟨ ap₂ Qₗ._∩_ refl (pres-⋂ᶠ (k ⊙ fsuc)) ⟩
    ⋂ᶠ Ql (apply f ⊙ k)                      ∎

  pres-⋂ᶠˢ : ∀ xs → f · ⋂ᶠˢ Pl xs ≡ ⋂ᶠˢ Ql (map (f ·_) xs)
  pres-⋂ᶠˢ = Finset-elim-prop _ pres-top (λ x ih → pres-∩ _ _ ∙ ap₂ Qₗ._∩_ refl ih)
```
