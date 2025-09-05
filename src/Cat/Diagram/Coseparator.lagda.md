<!--
```agda
open import Cat.Diagram.Product.Indexed
open import Cat.Diagram.Product.Power
open import Cat.Functor.Properties
open import Cat.Functor.Hom
open import Cat.Prelude

import Cat.Reasoning
import Cat.Morphism
```
-->

```agda
module Cat.Diagram.Coseparator {o ℓ} (C : Precategory o ℓ) where
```

<!--
```agda
open Cat.Reasoning C
open _=>_
```
-->
# Coseparating objects {defines="coseparating-object cogenerating-object coseparator"}


A coseparating (or cogenerating) object is formally the dual of a
[[separator]].


```agda
is-coseparator : Ob → Type _
is-coseparator c =
  ∀ {x y} {f g : Hom x y}
  → (∀ (m : Hom y c) → m ∘ f ≡ m ∘ g)
  → f ≡ g
```

Equivalently, an object $S$ is a coseparator if the hom functor $\cC(-,S)$
is [[faithful]].

```agda
coseparator→faithful : ∀ {s} → is-coseparator s → is-faithful (よ₀ C s)
coseparator→faithful cos p = cos (happly p)

faithful→coseparator : ∀ {s} → is-faithful (よ₀ C s) → is-coseparator s
faithful→coseparator faithful p = faithful (ext p)
```

# Coseparating families {defines="coseparating-family"}


Likewise, a coseparating family is dual to a [[separating family]].

```agda
is-coseparating-family : ∀ {ℓi} {Idx : Type ℓi} → (Idx → Ob) → Type _
is-coseparating-family s =
  ∀ {x y} {f g : Hom x y}
  → (∀ {i} (mᵢ : Hom y (s i)) → mᵢ ∘ f  ≡ mᵢ ∘ g )
  → f ≡ g
```

## Coseparators and powers

Equivalently to approximating objects with [[separators and copowers]], we
may approximate them with coseparators and powers.

```agda
module _
  (powers : (I : Set ℓ) → has-products-indexed-by C ∣ I ∣)
  where
  open Powers powers

  coseparator→mono : ∀ {s x} → is-coseparator s → is-monic (⋔!.tuple (Hom x s) s λ f → f)
  coseparator→mono {s} {x} cosep f g p =  cosep λ m →
    m ∘ f                                   ≡⟨ pushl (sym $ ⋔!.commute _ _) ⟩
    ⋔!.π _ _ m ∘ (⋔!.tuple _ _ λ f → f) ∘ f ≡⟨ refl⟩∘⟨ p ⟩
    ⋔!.π _ _ m ∘ (⋔!.tuple _ _ λ f → f) ∘ g ≡⟨ pulll $ ⋔!.commute _ _ ⟩
    m ∘ g                                   ∎

  mono→coseparator : ∀ {s} → (∀ {x} → is-monic (⋔!.tuple (Hom x s) s λ f → f)) → is-coseparator s
  mono→coseparator monic {f = f} {g = g} p = monic f g $ ⋔!.unique₂ _ _ λ m →
      assoc _ _ _ ∙ p _ ∙ sym (assoc _ _ _)

  coseparating-family→mono
    : ∀ (Idx : Set ℓ) (sᵢ : ∣ Idx ∣ → Ob)
    → is-coseparating-family sᵢ
    → ∀ {x} → is-monic (∏!.tuple (Σ[ i ∈ ∣ Idx ∣ ] Hom x (sᵢ i)) (sᵢ ⊙ fst) snd )
  coseparating-family→mono Idx sᵢ cosep f g p = cosep λ {i} mᵢ →
      mᵢ ∘ f                                     ≡⟨ pushl (sym $ ∏!.commute _ _) ⟩
      ∏!.π _ _ (i , mᵢ) ∘ (∏!.tuple _ _ snd) ∘ f ≡⟨ refl⟩∘⟨ p ⟩
      ∏!.π _ _ (i , mᵢ) ∘ (∏!.tuple _ _ snd) ∘ g ≡⟨ pulll $ ∏!.commute _ _ ⟩
      mᵢ ∘ g                                     ∎

  coseparating-family→make-mono
    : ∀ (Idx : Set ℓ) (sᵢ : ∣ Idx ∣ → Ob)
    → is-coseparating-family sᵢ
    → ∀ {x} → x ↪ ∏!.ΠF (Σ[ i ∈ ∣ Idx ∣ ] Hom x (sᵢ i)) (sᵢ ⊙ fst)
  coseparating-family→make-mono Idx sᵢ cosep = make-mono _ $ coseparating-family→mono Idx sᵢ cosep

  mono→coseparating-family
    : ∀ (Idx : Set ℓ)
    → (sᵢ : ∣ Idx ∣ → Ob)
    → (∀ {x} → is-monic (∏!.tuple (Σ[ i ∈ ∣ Idx ∣ ] Hom x (sᵢ i)) (sᵢ ⊙ fst) snd))
    → is-coseparating-family sᵢ
  mono→coseparating-family Idx sᵢ monic {f = f} {g = g} p =
    monic f g $ ∏!.unique₂ _ _ λ (i , mᵢ) →
      assoc _ _ _ ∙ p _ ∙ sym (assoc _ _ _)
```
