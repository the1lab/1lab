---
description: |
  Regular separators.
---
<!--
```agda
open import Cat.Diagram.Coequaliser.RegularEpi
open import Cat.Diagram.Coproduct.Copower
open import Cat.Diagram.Coproduct.Indexed
open import Cat.Diagram.Coequaliser
open import Cat.Prelude

import Cat.Morphism.StrongEpi
import Cat.Diagram.Separator
import Cat.Reasoning
```
-->
```agda
module Cat.Diagram.Separator.Regular {o ℓ} (C : Precategory o ℓ) where
```

<!--
```agda
open Cat.Morphism.StrongEpi
open Cat.Diagram.Separator C
open Cat.Reasoning C
```
-->

# Regular separators

```agda
module _
  (copowers : (I : Set ℓ) → has-coproducts-indexed-by C ∣ I ∣)
  where
  open Copowers copowers

  is-regular-separator : Ob → Type (o ⊔ ℓ)
  is-regular-separator s = ∀ {x} → is-regular-epi C (⊗!.match (Hom s x) s λ e → e)

  is-regular-separating-family
    : ∀ (Idx : Set ℓ)
    → (sᵢ : ∣ Idx ∣ → Ob)
    → Type (o ⊔ ℓ)
  is-regular-separating-family Idx sᵢ =
    ∀ {x} → is-regular-epi C (∐!.match (Σ[ i ∈ ∣ Idx ∣ ] (Hom (sᵢ i) x)) (sᵢ ⊙ fst) snd)
```

```agda
  regular-separator→separator
    : ∀ {s}
    → is-regular-separator s
    → is-separator s
  regular-separator→separator regular =
    epi→separator copowers $
    is-regular-epi→is-epic regular

  regular-separating-family→separating-family
    : ∀ (Idx : Set ℓ) (sᵢ : ∣ Idx ∣ → Ob)
    → is-regular-separating-family Idx sᵢ
    → is-separating-family sᵢ
  regular-separating-family→separating-family Idx sᵢ regular =
    epi→separating-family copowers Idx sᵢ $
    is-regular-epi→is-epic regular
```

```agda
module _
  (copowers : (I : Set ℓ) → has-coproducts-indexed-by C ∣ I ∣)
  where
  open Copowers copowers

  dense-separator→regular-separator
    : ∀ {s}
    → is-dense-separator s
    → is-regular-separator copowers s
  dense-separator→regular-separator {s = s} dense {x} = regular where
    module dense = is-dense-separator dense
    open is-regular-epi
    open is-coequaliser

    regular : is-regular-epi C (⊗!.match (Hom s x) s λ e → e)
    regular .r = Hom s x ⊗! s
    regular .arr₁ = id
    regular .arr₂ = id
    regular .has-is-coeq .coequal = refl
    regular .has-is-coeq .universal {e' = e'} _ =
      dense.universal λ e → e' ∘ ⊗!.ι (Hom s x) s e
    regular .has-is-coeq .factors {e' = e'} {p = p} =
      ⊗!.unique₂ (Hom s x) s λ e →
        (dense.universal _ ∘ ⊗!.match _ _ _) ∘ ⊗!.ι _ _ e ≡⟨ pullr (⊗!.commute _ _) ⟩
        dense.universal _ ∘ e                             ≡⟨ dense.commute ⟩
        e' ∘ ⊗!.ι _ _ e                                   ∎
    regular .has-is-coeq .unique {e' = e'} {colim = h} p =
      dense.unique _ λ e →
        h ∘ e                           ≡˘⟨ ap (h ∘_) (⊗!.commute (Hom s x) s) ⟩
        h ∘ ⊗!.match _ _ _ ∘ ⊗!.ι _ _ e ≡⟨ pulll p ⟩
        e' ∘ ⊗!.ι _ _ e                 ∎
```

```agda
  regular-separator→strong-separator
    : ∀ {s}
    → is-regular-separator copowers s
    → is-strong-separator copowers s
  regular-separator→strong-separator {s} regular {x} =
    is-regular-epi→is-strong-epi C _ regular
```
