<!--
```agda
open import Cat.Prelude

open import Order.Diagram.Glb
open import Order.Diagram.Lub
open import Order.Semilattice
open import Order.Frame
open import Order.Base
```
-->

```agda
module Order.Frame.Reasoning {o ℓ} (B : Frame o ℓ) where
```

```agda
open Frame B public
```


# Reasoning about frames

This module exposes tools to think about frames as semilattices (their
meet semilattices) and as posets. The poset which underlies a frame is
given by the meet ordering of its finite meets, i.e. $x \le y$ in the
frame $B$ iff $x = x \cap y$.

```agda
meets : Meet-semilattice o ℓ
meets = B .fst , has-meet-slat

joins : Join-semilattice o ℓ
joins = B .fst , has-join-slat
```

Using this ordering, we can show that the underlying poset of a frame is
indeed cocomplete:

This module also has further lemmas about the interplay between meets
and arbitrary joins. The following result holds in any cocomplete
lattice:

```agda
⋃-product
  : ∀ {I J : Type o} (F : I → ⌞ B ⌟) (G : J → ⌞ B ⌟)
  → ⋃ (λ i → ⋃ λ j → G i ∩ F j)
  ≡ ⋃ {I = I × J} (λ p → F (p .fst) ∩ G (p .snd))
⋃-product {I} {J} F G =
  ≤-antisym
    (⋃-universal _ λ j → ⋃-universal _ λ i →
      G j ∩ F i                                       =⟨ ∩-comm _ _ ⟩
      F i ∩ G j                                       ≤⟨ fam≤⋃ (i , j) ⟩
      ⋃ {I = I × J} (λ v → F (v .fst) ∩ G (v .snd)) ≤∎)
    (⋃-universal _ λ where
      (i , j) →
        F i ∩ G j                   ≤⟨ fam≤⋃ i ⟩
        ⋃ (λ i → F i ∩ G j)         ≤⟨ fam≤⋃ j ⟩
        ⋃ (λ i → ⋃ λ j → F j ∩ G i) =⟨ ap ⋃ (funext λ i → ap ⋃ $ funext λ j → ∩-comm (F j) (G i)) ⟩
        ⋃ (λ i → ⋃ λ j → G i ∩ F j) ≤∎)
```

But this result relies on the cocontinuity of meets.

```agda
⋃-∩-product
  : ∀ {I J : Type o} (F : I → ⌞ B ⌟) (G : J → ⌞ B ⌟)
  → ⋃ F ∩ ⋃ G
  ≡ ⋃ {I = I × J} (λ i → F (i .fst) ∩ G (i .snd))
⋃-∩-product F G =
  ⋃ F ∩ ⋃ G                         ≡⟨ ⋃-distribl (⋃ F) G ⟩
  ⋃ (λ i → ⋃ F ∩ G i)               ≡⟨ ap ⋃ (funext λ i → ∩-comm _ _ ∙ ⋃-distribl (G i) F) ⟩
  ⋃ (λ i → ⋃ λ j → G i ∩ F j)       ≡⟨ ⋃-product F G ⟩
  ⋃ (λ i → F (i .fst) ∩ G (i .snd)) ∎

⋃-twice
  : ∀ {I : Type o} {J : I → Type o} (F : (i : I) → J i → ⌞ B ⌟)
  → ⋃ (λ i → ⋃ λ j → F i j)
  ≡ ⋃ {I = Σ I J} (λ p → F (p .fst) (p .snd))
⋃-twice F = ≤-antisym
  (⋃-universal _ (λ i → ⋃-universal _ (λ j → fam≤⋃ _)))
  (⋃-universal _ λ (i , j) → ≤-trans (fam≤⋃ j) (fam≤⋃ i))

⋃-ap
  : ∀ {I I' : Type o} {f : I → ⌞ B ⌟} {g : I' → ⌞ B ⌟}
  → (e : I ≃ I')
  → (∀ i → f i ≡ g (e .fst i))
  → ⋃ f ≡ ⋃ g
⋃-ap e p = ap₂ (λ I f → ⋃ {I = I} f) (ua e) (ua→ p)

-- raised i for "index", raised f for "family"
⋃-apⁱ : ∀ {I I' : Type o} {f : I' → ⌞ B ⌟} (e : I ≃ I') → ⋃ (λ i → f (e .fst i)) ≡ ⋃ f
⋃-apᶠ : ∀ {I : Type o} {f g : I → ⌞ B ⌟} → (∀ i → f i ≡ g i) → ⋃ f ≡ ⋃ g

⋃-apⁱ e = ⋃-ap e (λ i → refl)
⋃-apᶠ p = ⋃-ap (_ , id-equiv) p

⋃-singleton
  : ∀ {I : Type o} {f : I → ⌞ B ⌟}
  → (p : is-contr I)
  → ⋃ f ≡ f (p .centre)
⋃-singleton {f = f} p = ≤-antisym
  (⋃-universal _ λ i → path→≥ $ ap f (p .paths i))
  (fam≤⋃ _)

⋃≤⋃
  : ∀ {I : Type o} {f g : I → ⌞ B ⌟}
  → (∀ i → f i ≤ g i)
  → ⋃ f ≤ ⋃ g
⋃≤⋃ p = ⋃-universal _ (λ i → ≤-trans (p i) (fam≤⋃ _))

-- FIXME: this ought to live somewhere else
∩≤∩
  : ∀ {x y x' y'}
  → x ≤ x'
  → y ≤ y'
  → (x ∩ y) ≤ (x' ∩ y')
∩≤∩ p q = ∩-universal _ (≤-trans ∩-≤l p) (≤-trans ∩-≤r q)
```
