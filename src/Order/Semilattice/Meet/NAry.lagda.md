<!--
```agda
open import Cat.Prelude

open import Data.Fin.Indexed
open import Data.Fin.Finite
open import Data.Fin.Base using (Fin ; fsuc ; fzero)

open import Order.Semilattice.Meet
open import Order.Diagram.Meet
open import Order.Diagram.Glb
open import Order.Diagram.Top
open import Order.Base
```
-->

```agda
module Order.Semilattice.Meet.NAry where
```

<!--
```
open is-glb
open Glb

module _ {o ℓ} {P : Poset o ℓ} (l : is-meet-semilattice P) where
  open is-meet-semilattice l
  open Poset P
```
-->

# n-Ary meets

```agda
  ⋂ᶠ : ∀ {n} (f : Fin n → Ob) → Ob
  ⋂ᶠ {0}           f = top
  ⋂ᶠ {1}           f = f fzero
  ⋂ᶠ {suc (suc n)} f = f fzero ∩ ⋂ᶠ (λ i → f (fsuc i))

  ⋂ᶠ-proj : ∀ {n} {f : Fin n → Ob} (i : Fin n) → ⋂ᶠ f ≤ f i
  ⋂ᶠ-proj {1}           fzero    = ≤-refl
  ⋂ᶠ-proj {suc (suc n)} fzero    = ∩≤l
  ⋂ᶠ-proj {suc (suc n)} (fsuc i) = ≤-trans ∩≤r (⋂ᶠ-proj i)

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

module
  _ {o ℓ o' ℓ'} {P : Poset o ℓ} {Q : Poset o' ℓ'} {f : Monotone P Q} {Pl Ql}
    (hom : is-meet-slat-hom f Pl Ql) where abstract

  private
    module Pₗ = is-meet-semilattice Pl
    module Qₗ = is-meet-semilattice Ql

  open is-meet-slat-hom hom

  pres-⋂ᶠ : ∀ {n} (k : Fin n → ⌞ P ⌟) → f # (⋂ᶠ Pl k) ≡ ⋂ᶠ Ql (apply f ⊙ k)
  pres-⋂ᶠ {n = 0} k = pres-top
  pres-⋂ᶠ {n = 1} k = refl
  pres-⋂ᶠ {n = suc (suc n)} k =
    f # (k fzero Pₗ.∩ ⋂ᶠ Pl (k ⊙ fsuc))      ≡⟨ pres-∩ _ _ ⟩
    f # (k fzero) Qₗ.∩ f # ⋂ᶠ Pl (k ⊙ fsuc)  ≡⟨ ap₂ Qₗ._∩_ refl (pres-⋂ᶠ (k ⊙ fsuc)) ⟩
    ⋂ᶠ Ql (apply f ⊙ k)                      ∎
