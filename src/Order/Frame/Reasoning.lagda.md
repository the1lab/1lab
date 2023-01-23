```agda
open import Cat.Prelude

open import Order.Diagram.Lub
open import Order.Semilattice
open import Order.Frame
open import Order.Base

module Order.Frame.Reasoning {ℓ} (B : Frame ℓ) where
```

# Reasoning about frames

This module exposes tools to think about frames as semilattices (their
meet semilattices) and as posets. The poset which underlies a frame is
given by the meet ordering of its finite meets, i.e. $x \le y$ in the
frame $B$ iff $x = x \cap y$.

```agda
meets : Semilattice ℓ
meets .fst = B .fst
meets .snd .Semilattice-on.top = _
meets .snd .Semilattice-on._∩_ = _
meets .snd .Semilattice-on.has-is-semilattice = Frame-on.has-meets (B .snd)

open Semilattice meets public
open Frame-on (B .snd) using (⋃ ; ⋃-universal ; ⋃-colimiting ; ⋃-distrib) public
```

<!--
```agda
⋃-distrib′ : ∀ {I : Type ℓ} (F : I → ⌞ B ⌟) {x} → ⋃ F ∩ x ≡ ⋃ (λ i → F i ∩ x)
⋃-distrib′ F = ∩-commutative ·· ⋃-distrib _ F ·· ap ⋃ (funext λ _ → ∩-commutative)

⋃-commute
  : ∀ {I J : Type ℓ} (F : I → J → ⌞ B ⌟)
  → ⋃ (λ i → ⋃ λ j → F i j)
  ≡ ⋃ (λ j → ⋃ λ i → F i j)
⋃-commute F = ≤-antisym
  (⋃-universal _ (λ i → ⋃-universal _
    (λ j → ≤-trans (⋃-colimiting _ λ i → F i j) (⋃-colimiting j _))))
  (⋃-universal _ (λ j → ⋃-universal _ (λ i →
    ≤-trans (⋃-colimiting j (F i)) (⋃-colimiting i _))))

⋃-monotone
  : ∀ {I} (F G : I → ⌞ B ⌟)
  → (∀ i → F i ≤ G i)
  → ⋃ F ≤ ⋃ G
⋃-monotone F G α = ⋃-universal F λ i → ≤-trans (α i) (⋃-colimiting i G)
```
-->

Using this ordering, we can show that the underlying poset of a frame is
indeed cocomplete:

```agda
cocomplete : ∀ {I : Type ℓ} (F : I → ⌞ B ⌟) → Lub po F
cocomplete F .fst = ⋃ F
cocomplete F .snd .is-lub.fam≤lub i = ⋃-colimiting i F
cocomplete F .snd .is-lub.least ub′ fam≤ub′ = ⋃-universal F fam≤ub′
```

This module also has further lemmas about the interplay between meets
and arbitrary joins. The following result holds in any cocomplete
lattice:

```agda
⋃-product
  : ∀ {I J : Type ℓ} (F : I → ⌞ B ⌟) (G : J → ⌞ B ⌟)
  → ⋃ (λ i → ⋃ λ j → G i ∩ F j)
  ≡ ⋃ {I = I × J} (λ p → F (p .fst) ∩ G (p .snd))
⋃-product {I} {J} F G = ≤-antisym
  (⋃-universal _ λ j → ⋃-universal _ λ i →
    G j ∩ F i                                       =⟨ ∩-commutative ⟩
    F i ∩ G j                                       ≤⟨ ⋃-colimiting (i , j) _ ⟩
    ⋃ {I = I × J} (λ v → F (v .fst) ∩ G (v .snd)) ≤∎)
  (⋃-universal _ λ { (i , j) →
    F i ∩ G j                   ≤⟨ ⋃-colimiting i (λ i → F i ∩ G j) ⟩
    ⋃ (λ i → F i ∩ G j)         ≤⟨ ⋃-colimiting j (λ j → ⋃ λ i → F i ∩ G j) ⟩
    ⋃ (λ i → ⋃ λ j → F j ∩ G i) =⟨ ap ⋃ (funext λ i → ap ⋃ $ funext λ j → ∩-commutative) ⟩
    ⋃ (λ i → ⋃ λ j → G i ∩ F j) ≤∎ })
```

But this result relies on the cocontinuity of meets.

```agda
⋃-∩-product
  : ∀ {I J : Type ℓ} (F : I → ⌞ B ⌟) (G : J → ⌞ B ⌟)
  → ⋃ F ∩ ⋃ G
  ≡ ⋃ {I = I × J} (λ i → F (i .fst) ∩ G (i .snd))
⋃-∩-product F G =
  ⋃ F ∩ ⋃ G                         ≡⟨ ⋃-distrib (⋃ F) G ⟩
  ⋃ (λ i → ⋃ F ∩ G i)               ≡⟨ ap ⋃ (funext λ i → ∩-commutative ∙ ⋃-distrib (G i) F) ⟩
  ⋃ (λ i → ⋃ λ j → G i ∩ F j)       ≡⟨ ⋃-product F G ⟩
  ⋃ (λ i → F (i .fst) ∩ G (i .snd)) ∎
```
