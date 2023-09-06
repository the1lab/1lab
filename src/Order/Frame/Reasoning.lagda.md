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

Using this ordering, we can show that the underlying poset of a frame is
indeed cocomplete:

```agda
cocomplete : ∀ {I : Type ℓ} (F : I → ⌞ B ⌟) → Σ _ (is-lub po F)
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

⋃-twice
  : ∀ {I : Type ℓ} {J : I → Type ℓ} (F : (i : I) → J i → ⌞ B ⌟)
  → ⋃ (λ i → ⋃ λ j → F i j)
  ≡ ⋃ {I = Σ I J} (λ p → F (p .fst) (p .snd))
⋃-twice F = ≤-antisym
  (⋃-universal _ (λ i → ⋃-universal _ (λ j → ⋃-colimiting _ _)))
  (⋃-universal _ λ (i , j) → ≤-trans (⋃-colimiting j _) (⋃-colimiting i _))

⋃-ap
  : ∀ {I I′ : Type ℓ} {f : I → ⌞ B ⌟} {g : I′ → ⌞ B ⌟}
  → (e : I ≃ I′)
  → (∀ i → f i ≡ g (e .fst i))
  → ⋃ f ≡ ⋃ g
⋃-ap e p = ap₂ (λ I f → ⋃ {I = I} f) (ua e) (ua→ p)

-- raised i for "index", raised f for "family"
⋃-apⁱ : ∀ {I I′ : Type ℓ} {f : I′ → ⌞ B ⌟} (e : I ≃ I′) → ⋃ (λ i → f (e .fst i)) ≡ ⋃ f
⋃-apᶠ : ∀ {I : Type ℓ} {f g : I → ⌞ B ⌟} → (∀ i → f i ≡ g i) → ⋃ f ≡ ⋃ g

⋃-apⁱ e = ⋃-ap e (λ i → refl)
⋃-apᶠ p = ⋃-ap (_ , id-equiv) p

⋃-singleton
  : ∀ {I : Type ℓ} {f : I → ⌞ B ⌟}
  → (p : is-contr I)
  → ⋃ f ≡ f (p .centre)
⋃-singleton {f = f} p = ≤-antisym
  (⋃-universal _ (λ i → sym ∩-idempotent ∙ ap₂ _∩_ refl (ap f (sym (p .paths _)))))
  (⋃-colimiting _ _)

⋃-distribʳ
  : ∀ {I : Type ℓ} {f : I → ⌞ B ⌟} {x}
  → ⋃ f ∩ x ≡ ⋃ (λ i → f i ∩ x)
⋃-distribʳ = ∩-commutative ∙ ⋃-distrib _ _ ∙ ap ⋃ (funext λ _ → ∩-commutative)

⋃≤⋃
  : ∀ {I : Type ℓ} {f g : I → ⌞ B ⌟}
  → (∀ i → f i ≤ g i)
  → ⋃ f ≤ ⋃ g
⋃≤⋃ p = ⋃-universal _ (λ i → ≤-trans (p i) (⋃-colimiting _ _))

∩≤∩
  : ∀ {x y x' y'}
  → x ≤ x'
  → y ≤ y'
  → (x ∩ y) ≤ (x' ∩ y')
∩≤∩ p q = ∩-univ _ (≤-trans ∩≤l p) (≤-trans ∩≤r q)
```
