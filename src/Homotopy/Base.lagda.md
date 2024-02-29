<!--
```agda
{-# OPTIONS -vtactic.hlevel:10 #-}
open import 1Lab.Prelude

open import Algebra.Group.Homotopy

open import Data.List using (_∷_ ; [])

open import Homotopy.Space.Suspension
open import Homotopy.Space.Sphere
```
-->

```agda
module Homotopy.Base where
```

# Synthetic homotopy theory

This module contains the basic definitions for the study of synthetic
homotopy theory. Synthetic homotopy theory is the name given to studying
$\infty$-groupoids in their own terms, i.e., the application of homotopy type
theory to computing homotopy invariants of spaces. Central to the theory
is the concept of [[pointed type]] and [[pointed map]]. After all, [homotopy
groups] are no more than the set-truncations of n-fold iterated loop
spaces, and loop spaces are always relative to a basepoint.

[homotopy groups]: Algebra.Group.Homotopy.html

A helper that will come in handy is `Σ∙`{.Agda}, which attaches the
north pole as the basepoint of the suspended space.

```agda
Σ∙ : ∀ {ℓ} → Type∙ ℓ → Type∙ ℓ
Σ∙ A = Susp∙ (A .fst)

Ω∙ : ∀ {ℓ} → Type∙ ℓ → Type∙ ℓ
Ω∙ (A , a) = Path A a a , refl
```

## The suspension-loop space adjunction

An important stepping stone in calculating loop spaces of higher types
is the _suspension-loop space_ [[adjunction]]: basepoint-preserving maps
_from_ a suspension are the same thing as basepoint-preserving maps
_into_ a loop space. We construct the equivalence in two steps, but both
halves are constructed in elementary terms.

First, we'll prove that

$$
(\Sigma A \to_* B) \simeq \left(\sum_{b_s : B} A \to b_0 \equiv b_s\right),
$$

which is slightly involved, but not too much. The actual equivalence is
very straightforward to construct, but proving that the two maps
`Σ-map→loops` and `loops→Σ-map` are inverses involves nontrivial path
algebra.

```agda
module _ {ℓ ℓ'} {A∙@(A , a₀) : Type∙ ℓ} {B∙@(B , b₀) : Type∙ ℓ'} where
  Σ-map∙→loops : (Σ∙ A∙ →∙ B∙) → (Σ _ λ bs → A → b₀ ≡ bs)
  Σ-map∙→loops f .fst   = f .fst S
  Σ-map∙→loops f .snd a = sym (f .snd) ∙ ap (f .fst) (merid a)

  loops→Σ-map∙ : (Σ _ λ bs → A → b₀ ≡ bs) → (Σ∙ A∙ →∙ B∙)
  loops→Σ-map∙ pair .fst N           = b₀
  loops→Σ-map∙ pair .fst S           = pair .fst
  loops→Σ-map∙ pair .fst (merid x i) = pair .snd x i
  loops→Σ-map∙ pair .snd = refl
```

The construction for turning a family of loops into a
basepoint-preserving map into $\Omega B$ is even simpler, perhaps
because these are almost definitionally the same thing.

```agda
  loops→map∙-Ω : (Σ _ λ bs → A → b₀ ≡ bs) → (A∙ →∙ Ω∙ B∙)
  loops→map∙-Ω (b , l) .fst a = l a ∙ sym (l a₀)
  loops→map∙-Ω (b , l) .snd   = ∙-invr (l a₀)

  map∙-Ω→loops : (A∙ →∙ Ω∙ B∙) → (Σ _ λ bs → A → b₀ ≡ bs)
  map∙-Ω→loops (f , _) .fst = b₀
  map∙-Ω→loops (f , _) .snd = f
```

<details>
<summary>The path algebra for showing these are both pairs of inverse
equivalences is not very interesting, so I've kept it hidden.</summary>

```agda
  Σ-map∙≃loops : (Σ∙ A∙ →∙ B∙) ≃ (Σ _ λ b → A → b₀ ≡ b)
  Σ-map∙≃loops = Iso→Equiv (Σ-map∙→loops , iso loops→Σ-map∙ invr invl) where
    invr : is-right-inverse loops→Σ-map∙ Σ-map∙→loops
    invr (p , q) = Σ-pathp refl $ funext λ a → ∙-idl (q a)

    invl : is-left-inverse loops→Σ-map∙ Σ-map∙→loops
    invl (f , pres) i = funext f' i , λ j → pres (~ i ∨ j) where
      f' : (a : Susp A) → loops→Σ-map∙ (Σ-map∙→loops (f , pres)) .fst a ≡ f a
      f' N = sym pres
      f' S = refl
      f' (merid x i) j = ∙-filler₂ (sym pres) (ap f (merid x)) j i

  loops≃map∙-Ω : (Σ _ λ bs → A → b₀ ≡ bs) ≃ (A∙ →∙ Ω∙ B∙)
  loops≃map∙-Ω = Iso→Equiv (loops→map∙-Ω , iso map∙-Ω→loops invr invl) where
    lemma' : ∀ {ℓ} {A : Type ℓ} {x : A} (q : x ≡ x) (r : refl ≡ q)
           → ap (λ p → q ∙ sym p) r ∙ ∙-invr q ≡ ∙-idr q ∙ sym r
    lemma' q r =
      J (λ q' r → ap (λ p → q' ∙ sym p) r ∙ ∙-invr q' ≡ ∙-idr q' ∙ sym r)
        (∙-idl _ ∙ sym (∙-idr _))
        r

    invr : is-right-inverse map∙-Ω→loops loops→map∙-Ω
    invr (b , x) = Σ-pathp (funext (λ a → ap₂ _∙_ refl (ap sym x) ∙ ∙-idr _)) (to-pathp (subst-path-left _ _ ∙ lemma)) where
      lemma =
        ⌜ sym (ap₂ _∙_ refl (ap sym x) ∙ ∙-idr (b a₀)) ⌝ ∙ ∙-invr (b a₀)          ≡⟨ ap! (sym-∙ (sym _) _) ⟩
        (sym (∙-idr (b a₀)) ∙ ap (b a₀ ∙_) (ap sym (sym x))) ∙ ∙-invr (b a₀)      ≡⟨ sym (∙-assoc _ _ _) ⟩
        sym (∙-idr (b a₀)) ∙ ⌜ ap (λ p → b a₀ ∙ sym p) (sym x) ∙ ∙-invr (b a₀) ⌝  ≡⟨ ap! (lemma' (b a₀) (sym x)) ⟩
        sym (∙-idr (b a₀)) ∙ ∙-idr (b a₀) ∙ x                                     ≡⟨ ∙-cancell _ _ ⟩
        x                                                                         ∎

    invl : is-left-inverse map∙-Ω→loops loops→map∙-Ω
    invl (f , p) = Σ-pathp (p a₀) $ to-pathp $ funext $ λ x →
        subst-path-right _ _ ∙ sym (∙-assoc _ _ _)
      ∙ ap₂ _∙_ refl (∙-invl (p a₀)) ∙ ∙-idr _
      ∙ ap p (transport-refl x)
```
</details>

Composing these equivalences, we get the adjunction:

$$
(\Sigma A \to_* B) \simeq (A \to* \Omega B).
$$

```agda
  Σ-map∙≃map∙-Ω : (Σ∙ A∙ →∙ B∙) ≃ (A∙ →∙ Ωⁿ 1 B∙)
  Σ-map∙≃map∙-Ω = Σ-map∙≃loops ∙e loops≃map∙-Ω
```

### Loop spaces are equivalently based maps out of spheres

Repeatedly applying the equivalence we just built, we can build an
equivalence

$$
(S^n \to_* A) \simeq (\Sigma S^{n - 1} \to_* \Omega A) \simeq ... \simeq \Omega^n A,
$$

thus characterising $n$-fold loop spaces as basepoint-preserving maps
out of $S^n$, the $n$-dimensional sphere.

<!--
```agda
reassoc-Ω : ∀ {ℓ} {A : Type∙ ℓ} n → Ωⁿ n (Ω∙ A) ≡ Ωⁿ (suc n) A
reassoc-Ω zero = refl
reassoc-Ω {A = A} (suc n) =
  Ωⁿ 1 (Ωⁿ n (Ωⁿ 1 A)) ≡⟨ ap (Ωⁿ 1) (reassoc-Ω n) ⟩
  Ωⁿ 1 (Ωⁿ (suc n) A)  ∎
```
-->

As a special case, in the zeroth dimension, we conclude that $(2 \to_*
A) \equiv A$, i.e., basepoint-preserving maps from the booleans (based
at either point) are the same thing as points of $A$.

```agda
Ωⁿ≃Sⁿ-map : ∀ {ℓ} {A : Type∙ ℓ} n → (Sⁿ n →∙ A) ≃ Ωⁿ n A .fst
Ωⁿ≃Sⁿ-map {A = A} zero    = Iso→Equiv (from , iso to (λ _ → refl) invr) where
  to : A .fst → ((Susp ⊥ , N) →∙ A)
  to x .fst N = A .snd
  to x .fst S = x
  to x .snd = refl

  from : ((Susp ⊥ , N) →∙ A) → A .fst
  from f = f .fst S

  invr : is-right-inverse from to
  invr (x , p) = Σ-pathp (funext (λ { N → sym p ; S → refl })) λ i j → p (~ i ∨ j)

Ωⁿ≃Sⁿ-map {A = A} (suc n) =
  (Σ∙ (Susp _ , N) →∙ A)          ≃⟨ Σ-map∙≃map∙-Ω ⟩
  ((Susp (Sⁿ⁻¹ n) , N) →∙ Ωⁿ 1 A) ≃⟨ Ωⁿ≃Sⁿ-map n ⟩
  Ωⁿ n (Ωⁿ 1 A) .fst              ≃⟨ path→equiv (ap fst (reassoc-Ω n)) ⟩
  Ωⁿ (suc n) A .fst               ≃∎
```
