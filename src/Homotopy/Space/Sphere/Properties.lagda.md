<!--
```agda
open import Algebra.Group.Instances.Integers
open import Algebra.Group.Cat.Base
open import Algebra.Group.Concrete
open import Algebra.Group.Homotopy
open import Algebra.Group

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
open import Homotopy.Space.Suspension
open import Homotopy.Space.Circle
open import Homotopy.Space.Sphere
open import Homotopy.Conjugation
open import Homotopy.Truncation
open import Homotopy.Loopspace
open import Homotopy.HSpace
open import Homotopy.Base

import Cat.Reasoning

import Homotopy.Space.Suspension.Pi2
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
open Homotopy.Space.Suspension.Pi2 S¹-concrete HSpace-S¹

opaque
  π₂S²≅ℤ : πₙ₊₁ 1 (Sⁿ 2) Groups.≅ ℤ
  π₂S²≅ℤ = π₁S¹≅ℤ
    Groups.∘Iso π₂ΣG≅ΩG
    Groups.∘Iso πₙ₊₁-ap 1 (Susp-ap SuspS⁰≃∙S¹)
```

The inverse to this equivalence, turning integers into 2-loops on the
[[sphere]], is constructed purely abstractly and thus too horrible to
compute with. However, the *forward* map, giving the winding numbers of
2-loops, is more tractable. We can write down an explicit generator for
$\pi_2(S^2)$ and assert that the equivalence above takes it to the
number $1$ by computation.

```agda
private opaque
  unfolding conj conj-refl π₂S²≅ℤ ΩΣG≃G n-Tr-Ω¹ Ω¹-ap

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

## Stability for spheres {defines="stability-for-spheres"}

Applying the unit of the [[suspension–loop space adjunction]] $\sigma :
A \to_* \Loop \Susp A$ under $\Loop^k$ and specialising $A$ to the
$n$-sphere gives us a map $\Loop^k \sigma : \Loop^k S^n \to_*
\Loop^{k+1} S^{n+1}$. In this section, we will show that this map induces
an isomorphism of [[set truncations]] (hence of [[homotopy groups]],
although we do not prove this) when $n$ is large enough.

```agda
Ωⁿ-suspend : ∀ {ℓ} k (A : Type∙ ℓ) → Ωⁿ k A →∙ Ωⁿ (suc k) (Σ¹ A)
Ωⁿ-suspend k A = Equiv∙.from∙ (Ωⁿ-suc (Σ¹ A) k) ∘∙ Ωⁿ-map k (suspend∙ A)
```

<!--
```agda
Ωⁿ-suspend-natural
  : ∀ {ℓa ℓb} {A : Type∙ ℓa} {B : Type∙ ℓb} k (f : A →∙ B)
  → Ωⁿ-map (suc k) (Susp-map∙ f) ∘∙ Ωⁿ-suspend k A
  ≡ Ωⁿ-suspend k B ∘∙ Ωⁿ-map k f
Ωⁿ-suspend-natural {A = A} {B = B} k f = homogeneous-funext∙ λ l →
  Ωⁿ-map (suc k) (Susp-map∙ f) · (Equiv∙.from∙ (Ωⁿ-suc (Σ¹ A) k) · (Ωⁿ-map k (suspend∙ A) · l))
    ≡⟨ Equiv.adjunctl (Ωⁿ-suc _ k .fst) (Ω-suc-natural k (Susp-map∙ f) ·ₚ _) ⟩
  Equiv∙.from∙ (Ωⁿ-suc (Σ¹ B) k) · ⌜ Ωⁿ-map k (Ω¹-map (Susp-map∙ f)) · (Ωⁿ-map k (suspend∙ A) · l) ⌝
    ≡⟨ ap! (Ωⁿ-map-∘ k _ (suspend∙ A) ·ₚ l) ⟩
  Equiv∙.from∙ (Ωⁿ-suc (Σ¹ B) k) · (Ωⁿ-map k ⌜ Ω¹-map (Susp-map∙ f) ∘∙ suspend∙ A ⌝ · l)
    ≡⟨ ap! (suspend∙-natural f) ⟩
  Equiv∙.from∙ (Ωⁿ-suc (Σ¹ B) k) · ⌜ Ωⁿ-map k (suspend∙ B ∘∙ f) · l ⌝
    ≡˘⟨ ap¡ (Ωⁿ-map-∘ k (suspend∙ B) f ·ₚ l) ⟩
  Equiv∙.from∙ (Ωⁿ-suc (Σ¹ B) k) · (Ωⁿ-map k (suspend∙ B) · (Ωⁿ-map k f · l))
    ∎
```
-->

The [[Freudenthal suspension theorem]] implies that, if $0 < k \le 2n$,
the $k$-truncation of $\Loop S^{n+1}$ agrees with that of $S^n$, with
the map $\sigma : S^n \to_* \Loop S^{n+1}$ mediating between the two
up to truncation inclusion.

```agda
opaque
  Sⁿ-stability-n-Tr
    : ∀ n k (p : suc k ≤ (suc n + suc n))
    → n-Tr∙ (Sⁿ (1 + n)) (suc k) ≃∙ n-Tr∙ (Ω¹ (Sⁿ (2 + n))) (suc k)
  Sⁿ-stability-n-Tr n k p =
    n-Tr∙ (Sⁿ (1 + n)) (suc k)
      ≃∙˘⟨ n-Tr-Tr (≤-peel p) , refl ⟩
    n-Tr∙ (n-Tr∙ (Sⁿ (1 + n)) (suc n + suc n)) (suc k)
      ≃∙⟨ (let e , p = freudenthal-equivalence {A∙ = Sⁿ (suc n)} n (Sⁿ⁻¹-is-connected (2 + n)) in n-Tr-ap {n = k} e , ap n-Tr.inc p) ⟩
    n-Tr∙ (n-Tr∙ (Ω¹ (Σ¹ (Sⁿ (1 + n)))) (suc n + suc n)) (suc k)
      ≃∙⟨⟩
    n-Tr∙ (n-Tr∙ (Ω¹ (Sⁿ (2 + n))) (suc n + suc n)) (suc k)
      ≃∙⟨ n-Tr-Tr (≤-peel p) , refl ⟩
    n-Tr∙ (Ω¹ (Sⁿ (2 + n))) (suc k)
      ≃∙∎

  Sⁿ-stability-n-Tr-suspend
    : ∀ n k (p : suc k ≤ (suc n + suc n))
    → Equiv∙.to∙ (Sⁿ-stability-n-Tr n k p) ∘∙ inc∙
    ≡ inc∙ ∘∙ suspend∙ (Sⁿ (1 + n))
  Sⁿ-stability-n-Tr-suspend n k p = homogeneous-funext∙ λ _ → refl
```

Thus, by swapping loop spaces and truncations, we obtain
an isomorphism of sets $\pi_k(S^n) \simeq \pi_{k+1}(S^{n+1})$ whenever
$0 < k \le 2(n-1)$.

<!--
```agda
module _ n k (p : suc k ≤ n + n) where
  private abstract
    p' : suc (k + 2) ≤ suc n + suc n
    p' = s≤s
       $ ≤-trans (≤-refl' (+-commutative k 2))
       $ ≤-trans (s≤s p)
       $ ≤-refl' (+-commutative (suc n) n)
```
-->

```agda
  opaque
    Sⁿ-stability
      : ⌞ πₙ₊₁ (1 + k) (Sⁿ (2 + n)) ⌟ ≃ ⌞ πₙ₊₁ k (Sⁿ (1 + n)) ⌟
    Sⁿ-stability =
      ⌞ πₙ₊₁ (1 + k) (Sⁿ (2 + n)) ⌟
        ≃⟨ πₙ-def (Sⁿ (2 + n)) (1 + k) .fst ⟩
      ⌞ Ωⁿ (2 + k) (n-Tr∙ (Sⁿ (2 + n)) (2 + k + 2)) ⌟
        ≃⟨ Ωⁿ-suc (n-Tr∙ (Sⁿ (2 + n)) (2 + k + 2)) (1 + k) .fst ⟩
      ⌞ Ωⁿ (1 + k) (Ω¹ (n-Tr∙ (Sⁿ (2 + n)) (2 + k + 2))) ⌟
        ≃˘⟨ Ωⁿ-ap (1 + k) (n-Tr-Ω¹ (Sⁿ (2 + n)) (k + 2)) .fst ⟩
      ⌞ Ωⁿ (1 + k) (n-Tr∙ (Ω¹ (Sⁿ (2 + n))) (1 + k + 2)) ⌟
        ≃˘⟨ Ωⁿ-ap (1 + k) (Sⁿ-stability-n-Tr n (k + 2) p') .fst ⟩
      ⌞ Ωⁿ (1 + k) (n-Tr∙ (Sⁿ (1 + n)) (1 + k + 2)) ⌟
        ≃˘⟨ πₙ-def (Sⁿ (1 + n)) k .fst ⟩
      ⌞ πₙ₊₁ k (Sⁿ (1 + n)) ⌟
        ≃∎
```

<details>
<summary>
We again check that the inverse map of this equivalence is the expected
suspension map.

```agda
    Sⁿ-stability-suspend
      : Equiv.from Sⁿ-stability ⊙ inc
      ≡ ∥_∥₀.inc ⊙ Ωⁿ-suspend (suc k) (Sⁿ (suc n)) .fst
```

This boils down to chasing an element of $\Loop^k S^n$ through every step
of the equivalence above, which we express as an annoying chain of
[[pointed equivalences]].
</summary>

```agda
    Sⁿ-stability-suspend = ext λ l → trace l .snd where
      trace
        : (l : ⌞ Ωⁿ (1 + k) (Sⁿ (1 + n)) ⌟)
        →  (⌞ πₙ₊₁ k (Sⁿ (1 + n)) ⌟ , inc l)
        ≃∙ (⌞ πₙ₊₁ (1 + k) (Sⁿ (2 + n)) ⌟ , inc (Ωⁿ-suspend (suc k) (Sⁿ (suc n)) · l))
      trace l =
        ⌞ πₙ₊₁ k (Sⁿ (1 + n)) ⌟ ,
          inc l
            ≃∙⟨ πₙ-def (Sⁿ (1 + n)) k .fst , πₙ-def-inc _ k l ⟩
        ⌞ Ωⁿ (1 + k) (n-Tr∙ (Sⁿ (1 + n)) (1 + k + 2)) ⌟ ,
          Ωⁿ-map (1 + k) inc∙ · l
            ≃∙⟨ Ωⁿ-ap (1 + k) (Sⁿ-stability-n-Tr n (k + 2) p') .fst
              , (Ωⁿ-map-∘ (1 + k) (Equiv∙.to∙ (Sⁿ-stability-n-Tr n (k + 2) p')) inc∙ ·ₚ l)
              ∙ ap (λ x → Ωⁿ-map (1 + k) x · l) (Sⁿ-stability-n-Tr-suspend n (k + 2) p') ⟩
        ⌞ Ωⁿ (1 + k) (n-Tr∙ (Ω¹ (Sⁿ (2 + n))) (1 + k + 2)) ⌟ ,
          Ωⁿ-map (1 + k) (inc∙ ∘∙ suspend∙ _) · l
            ≃∙⟨ Ωⁿ-ap (1 + k) (n-Tr-Ω¹ (Sⁿ (2 + n)) (k + 2)) .fst
              , Ωⁿ-map-∘ (1 + k) (Equiv∙.to∙ (n-Tr-Ω¹ _ (k + 2))) _ ·ₚ l ⟩
        ⌞ Ωⁿ (1 + k) (Ω¹ (n-Tr∙ (Sⁿ (2 + n)) (2 + k + 2))) ⌟ ,
          Ωⁿ-map (1 + k) (Equiv∙.to∙ (n-Tr-Ω¹ _ (k + 2)) ∘∙ inc∙ ∘∙ suspend∙ _) · l
            ≃∙⟨ id≃
              , ap (λ x → Ωⁿ-map (1 + k) x · l)
                ( sym (∘∙-assoc (Equiv∙.to∙ (n-Tr-Ω¹ _ (k + 2))) inc∙ (suspend∙ _))
                ∙ ap (_∘∙ suspend∙ _) (n-Tr-Ω¹-inc _ (k + 2)))
              ∙ sym (Ωⁿ-map-∘ (1 + k) _ _ ·ₚ l) ⟩
        ⌞ Ωⁿ (1 + k) (Ω¹ (n-Tr∙ (Sⁿ (2 + n)) (2 + k + 2))) ⌟ ,
          Ωⁿ-map (1 + k) (Ω¹-map inc∙) · (Ωⁿ-map (1 + k) (suspend∙ _) · l)
            ≃∙˘⟨ Ωⁿ-suc (n-Tr∙ (Sⁿ (2 + n)) (2 + k + 2)) (1 + k) .fst
               , Ω-suc-natural (1 + k) inc∙ ·ₚ _ ⟩
        ⌞ Ωⁿ (2 + k) (n-Tr∙ (Sⁿ (2 + n)) (2 + k + 2)) ⌟ ,
          Ωⁿ-map (2 + k) inc∙ · (Ωⁿ-suspend (suc k) (Sⁿ (suc n)) · l)
            ≃∙˘⟨ πₙ-def (Sⁿ (2 + n)) (1 + k) .fst
               , πₙ-def-inc _ (suc k) _ ⟩
        ⌞ πₙ₊₁ (1 + k) (Sⁿ (2 + n)) ⌟ ,
          inc (Ωⁿ-suspend (suc k) (Sⁿ (suc n)) · l)
            ≃∙∎
```
</details>

As a corollary, $\pi_n(S^n) \simeq \bZ$.

```agda
πₙSⁿ≃Int : ∀ n → ⌞ πₙ₊₁ n (Sⁿ (suc n)) ⌟ ≃ ⌞ ℤ ⌟
πₙSⁿ≃Int 0 =
  ∥ ⌞ Ω¹ (Sⁿ 1) ⌟ ∥₀      ≃⟨ ∥-∥₀-ap (Ωⁿ-ap 1 SuspS⁰≃∙S¹ .fst) ⟩
  ∥ ⌞ Ω¹ (S¹ , base) ⌟ ∥₀ ≃⟨ Equiv.inverse (_ , ∥-∥₀-idempotent (hlevel 2)) ⟩
  ⌞ Ω¹ (S¹ , base) ⌟      ≃⟨ ΩS¹≃Int ⟩
  Int                     ≃∎

πₙSⁿ≃Int 1 = Iso→Equiv (i.to , iso i.from (happly i.invl) (happly i.invr)) where
  module i = Cat.Reasoning._≅_ (Sets lzero) (F-map-iso (Forget-structure _) π₂S²≅ℤ)

πₙSⁿ≃Int (suc (suc n)) =
  ⌞ πₙ₊₁ (2 + n) (Sⁿ (3 + n)) ⌟ ≃⟨ Sⁿ-stability (1 + n) (1 + n) (s≤s (+-≤r n (1 + n))) ⟩
  ⌞ πₙ₊₁ (1 + n) (Sⁿ (2 + n)) ⌟ ≃⟨ πₙSⁿ≃Int (suc n) ⟩
  ⌞ ℤ ⌟                         ≃∎
```

Furthermore, the isomorphisms $\pi_n(S^n) \simeq \bZ$ are compatible
with the suspension maps `Ωⁿ-suspend`{.Agda}, in the sense that the
following diagram of isomorphisms commutes:

~~~{.quiver}
\[\begin{tikzcd}
  {\pi_1(S^1)} & {\pi_2(S^2)} & {\pi_3(S^3)} & \cdots \\
  & {\bZ}
  \arrow["{\Omega\, \sigma}", from=1-1, to=1-2] % why does \Loop yields a square here?
  \arrow[from=1-1, to=2-2]
  \arrow["{\Omega^2\, \sigma}", from=1-2, to=1-3]
  \arrow[from=1-2, to=2-2]
  \arrow["{\Omega^3\, \sigma}", from=1-3, to=1-4]
  \arrow[from=1-3, to=2-2]
  \arrow[from=1-4, to=2-2]
\end{tikzcd}\]
~~~

```agda
opaque
  unfolding π₂S²≅ℤ

  πₙSⁿ≃Int-suspend
    : ∀ n (l : ⌞ Ωⁿ (suc n) (Sⁿ (suc n)) ⌟)
    → πₙSⁿ≃Int (suc n) · inc (Ωⁿ-suspend (suc n) (Sⁿ (suc n)) · l)
    ≡ πₙSⁿ≃Int n · inc l
  πₙSⁿ≃Int-suspend zero l =
    ΩS¹≃Int · (Ω²ΣG≃ΩG · ∥_∥₀.inc ⌜ Ωⁿ-map 2 (Susp-map∙ SuspS⁰→∙S¹) · (Ωⁿ-suspend 1 (Sⁿ 1) · l) ⌝)
      ≡⟨ ap! (Ωⁿ-suspend-natural 1 SuspS⁰→∙S¹ ·ₚ l) ⟩
    ΩS¹≃Int · (Ω²ΣG≃ΩG · ∥_∥₀.inc ⌜ Ωⁿ-suspend 1 _ · (Ω¹-map SuspS⁰→∙S¹ · l) ⌝)
      ≡⟨ ap! (transport-refl _) ⟩
    ΩS¹≃Int · ⌜ Ω²ΣG≃ΩG · ∥_∥₀.inc (Ω¹-map (suspend∙ _) · (Ω¹-map SuspS⁰→∙S¹ · l)) ⌝
      ≡⟨ ap! (Equiv.adjunctr Ω²ΣG≃ΩG (sym (Ω²ΣG≃ΩG-inv (Ω¹-map SuspS⁰→∙S¹ · l)))) ⟩
    ΩS¹≃Int · (Ω¹-map SuspS⁰→∙S¹ · l)
      ∎
  πₙSⁿ≃Int-suspend (suc n) l =
    ap (πₙSⁿ≃Int (1 + n) .fst) $
    Equiv.adjunctr (Sⁿ-stability (1 + n) (1 + n) _) $
    sym (Sⁿ-stability-suspend (1 + n) (1 + n) _ $ₚ l)
```
