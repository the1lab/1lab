<!--
```agda
open import Algebra.Group.Instances.Integers
open import Algebra.Group.Cat.Base
open import Algebra.Group.Concrete
open import Algebra.Group.Homotopy

open import Cat.Functor.Base
open import Cat.Prelude

open import Data.Nat.Properties
open import Data.Set.Truncation
open import Data.Nat.Order
open import Data.Int.Base
open import Data.Nat.Base

open import Homotopy.Space.Suspension.Freudenthal
open import Homotopy.Space.Suspension.Properties
open import Homotopy.Space.Circle.Properties
open import Homotopy.Space.Suspension.Pi2
open import Homotopy.Space.Suspension
open import Homotopy.Space.Circle
open import Homotopy.Space.Sphere
open import Homotopy.Conjugation
open import Homotopy.Truncation
open import Homotopy.Loopspace
open import Homotopy.HSpace

import Cat.Reasoning
```
-->

```agda
module Homotopy.Space.Sphere.Properties where
```

# Properties of higher spheres

We can put together what we know about [$\pi_2$ of a suspension] and
about the [[fundamental group]] $\pi_1(S^1)$ of the [[circle]] to show
that $\pi_2(S^2) \cong \bZ$.

[$\pi_2$ of a suspension]: Homotopy.Space.Suspension.Pi2.html

```agda
opaque
  π₂S²≅ℤ : πₙ₊₁ 1 (Sⁿ 2) Groups.≅ ℤ
  π₂S²≅ℤ = π₁S¹≅ℤ
    Groups.∘Iso (π₂ΣG≅ΩG S¹-concrete HSpace-S¹)
    Groups.∘Iso πₙ₊₁-ap 1 (Susp-ap SuspS⁰≃S¹ , refl)
```

The inverse to this equivalence, turning integers into 2-loops on the
sphere, is constructed purely abstractly and thus too horrible to
compute with. However, the *forward* map, giving the winding numbers of
2-loops, is more tractable. We can write down an explicit generator for
$\pi_2(S^2)$ and assert that the equivalence above takes it to the
number $1$ by computation.

```agda
private opaque
  unfolding conj conj-refl conj-of-refl π₂S²≅ℤ

  gen : Path (Path ⌞ Sⁿ 2 ⌟ north north) refl refl
  gen i j = hcomp (∂ i ∨ ∂ j) λ where
    k (k = i0) → merid (suspend (Sⁿ 0) south (~ j)) i
    k (i = i0) → north
    k (i = i1) → merid north (~ k)
    k (j = i0) → merid north (~ k ∧ i)
    k (j = i1) → merid north (~ k ∧ i)

  π₂S²≅ℤ-computes : Groups.to π₂S²≅ℤ · inc gen ≡ 1
  π₂S²≅ℤ-computes = refl
```

<!--
```agda
  {-
  Checking Homotopy.Space.Sphere.Properties (…).
  Total                                            6,655ms
  Homotopy.Space.Sphere.Properties.π₂S²≅ℤ-computes 1,073ms
  -}
```
-->

## Stability for spheres

The [[Freudenthal suspension theorem]] implies that, if $k \le 2(n - 1)$
the $k$-truncation of $\Omega S^{2+n}$ agrees with that of $S^{1 + n}$.

```agda
Sⁿ-stability-worker
  : ∀ n k (p : suc k ≤ (suc n + suc n))
  → n-Tr∙ (Sⁿ (1 + n)) (suc k) ≃∙ n-Tr∙ (Ωⁿ 1 (Sⁿ (2 + n))) (suc k)
Sⁿ-stability-worker n k p =
  n-Tr∙ (Sⁿ (1 + n)) (suc k)
    ≃∙˘⟨ n-Tr-Tr (≤-peel p) , refl ⟩
  n-Tr∙ (n-Tr∙ (Sⁿ (1 + n)) (suc n + suc n)) (suc k)
    ≃∙⟨ (let e , p = freudenthal-equivalence {A∙ = Sⁿ (suc n)} n (Sⁿ⁻¹-is-connected (2 + n)) in n-Tr-ap {n = k} e , ap n-Tr.inc p) ⟩
  n-Tr∙ (n-Tr∙ (Ωⁿ 1 (Σ¹ (Sⁿ (1 + n)))) (suc n + suc n)) (suc k)
    ≃∙⟨⟩
  n-Tr∙ (n-Tr∙ (Ωⁿ 1 (Sⁿ (2 + n))) (suc n + suc n)) (suc k)
    ≃∙⟨ n-Tr-Tr (≤-peel p) , refl ⟩
  n-Tr∙ (Ωⁿ 1 (Sⁿ (2 + n))) (suc k)
    ≃∙∎
```

As a corollary, $\pi_n(S^n) \simeq \bZ$.

```agda
πₙSⁿ≃Int : ∀ n → ⌞ πₙ₊₁ n (Sⁿ (suc n)) ⌟ ≃ ⌞ ℤ ⌟
πₙSⁿ≃Int 0 =
  ∥ ⌞ Ω¹ (Sⁿ 1) ⌟ ∥₀      ≃⟨ ∥-∥₀-ap (Ωⁿ-ap 1 (SuspS⁰≃S¹ , refl) .fst) ⟩
  ∥ ⌞ Ω¹ (S¹ , base) ⌟ ∥₀ ≃⟨ Equiv.inverse (_ , ∥-∥₀-idempotent (hlevel 2)) ⟩
  ⌞ Ω¹ (S¹ , base) ⌟      ≃⟨ ΩS¹≃Int ⟩
  Int                     ≃∎

πₙSⁿ≃Int 1 = Iso→Equiv (i.to , iso i.from (happly i.invl) (happly i.invr)) where
  module i = Cat.Reasoning._≅_ (Sets lzero) (F-map-iso (Forget-structure _) π₂S²≅ℤ)

πₙSⁿ≃Int (suc (suc n)) =
  ⌞ πₙ₊₁ (2 + n) (Sⁿ (3 + n)) ⌟
    ≃⟨ πₙ-def (Sⁿ (3 + n)) (2 + n) .fst ⟩
  ⌞ Ωⁿ (3 + n) (n-Tr∙ (Sⁿ (3 + n)) (suc ((2 + n) + 2))) ⌟
    ≃⟨ Ωⁿ-suc _ (2 + n) .fst ⟩
  ⌞ Ωⁿ (2 + n) ((Ωⁿ 1 (n-Tr∙ (Sⁿ (3 + n)) (3 + n + 2)))) ⌟
    ≃⟨ Ωⁿ-ap (2 + n) (Equiv∙.inverse (n-Tr-Ω¹ _ (1 + n + 2))) .fst ⟩
  ⌞ Ωⁿ (2 + n) (n-Tr∙ (Ωⁿ 1 (Sⁿ (3 + n))) (2 + n + 2)) ⌟
    ≃⟨
      (let
        ix = s≤s (s≤s (≤-trans (+-≤l (n + 2) n) (≤-refl' (sym (+-associative n 2 n)))))
        eqv = Sⁿ-stability-worker (1 + n) (1 + n + 2) ix
      in Ωⁿ-ap (2 + n) (Equiv∙.inverse eqv) .fst) ⟩
  ⌞ Ωⁿ (2 + n) (n-Tr∙ (Sⁿ (2 + n)) (2 + n + 2)) ⌟
    ≃⟨ Equiv.inverse (πₙ-def (Sⁿ (2 + n)) (1 + n) .fst) ⟩
  ⌞ πₙ₊₁ (1 + n) (Sⁿ (2 + n)) ⌟
    ≃⟨ πₙSⁿ≃Int (suc n) ⟩
  ⌞ ℤ ⌟
    ≃∎
```
