<!--
```agda
open import Cat.CartesianClosed.Instances.PSh
open import Cat.Diagram.Sieve
open import Cat.Functor.Base
open import Cat.Site.Closure
open import Cat.Site.Base
open import Cat.Prelude

import Cat.Functor.Reasoning.Presheaf as PSh
import Cat.Reasoning as Cat

open Functor
open _=>_
```
-->

```agda
module Cat.Instances.Sheaves.Exponentials where
```

# Exponentials of sheaves {defines="exponentials-of-sheaves"}

```agda
is-sheaf-exponential
  : ∀ {ℓ ℓs} {C : Precategory ℓ ℓ} (J : Coverage C ℓs) (A B : Functor (C ^op) (Sets ℓ))
  → is-sheaf J B
  → is-sheaf J (PSh[_,_] {C = C} A B)
is-sheaf-exponential {C = C} J A B bshf = from-is-sheaf₁ λ c → done where
  open Cat C
  module bshf = sat bshf

  psh = PSh[_,_] {C = C} A B

  abstract
    sep : ∀ {U} {c : J .covers U} → is-separated₁ psh (J .cover c)
    sep {c = c} {x} {y} loc = ext λ i f z → bshf.separate (pull f (inc c)) λ g hg →
      B ⟪ g ⟫ x .η i (f , z)             ≡˘⟨ x .is-natural _ _ _ $ₚ _ ⟩
      x .η _ (f ∘ g , A ⟪ g ⟫ z)         ≡⟨ ap (x .η _) (Σ-pathp (intror refl) refl) ⟩
      x .η _ ((f ∘ g) ∘ id , A ⟪ g ⟫ z)  ≡⟨ loc (f ∘ g) hg ηₚ _ $ₚ _ ⟩
      y .η _ ((f ∘ g) ∘ id , A ⟪ g ⟫ z)  ≡˘⟨ ap (y .η _) (Σ-pathp (intror refl) refl) ⟩
      y .η _ (f ∘ g , A ⟪ g ⟫ z)         ≡⟨ y .is-natural _ _ _ $ₚ _ ⟩
      B ⟪ g ⟫ y .η i (f , z)             ∎

  module _ {U} {c : J .covers U} (p : Patch psh (J .cover c)) where
    p' : ∀ {x} (e : A ʻ x) (f : Hom x U) → Patch B (pullback f (J .cover c))
    p' e f .part g hg = p .part (f ∘ g) hg .η _ (id , A ⟪ g ⟫ e)
    p' e f .patch g hg h hh =
      B ⟪ h ⟫ p .part (f ∘ g) _ .η _ (id , A ⟪ g ⟫ e)          ≡˘⟨ p .part (f ∘ g) hg .is-natural _ _ _ $ₚ (id , A ⟪ g ⟫ e) ⟩
      p .part (f ∘ g) _ .η _ (id ∘ h , A ⟪ h ⟫ (A ⟪ g ⟫ e))    ≡⟨ ap (λ it → p .part (f ∘ g) hg .η _ (it , A ⟪ h ⟫ (A ⟪ g ⟫ e))) id-comm-sym ⟩
      p .part (f ∘ g) _ .η _ (h ∘ id , A ⟪ h ⟫ (A ⟪ g ⟫ e))    ≡⟨ p .patch (f ∘ g) hg h (subst (_∈ J .cover c) (assoc _ _ _) hh) ηₚ _ $ₚ (id , _) ⟩
      p .part ((f ∘ g) ∘ h) _ .η _ (id , A ⟪ h ⟫ (A ⟪ g ⟫ e))  ≡⟨ app p (sym (assoc f g h)) ηₚ _ $ₚ _ ⟩
      p .part (f ∘ g ∘ h) _ .η _ (id , A ⟪ h ⟫ (A ⟪ g ⟫ e))    ≡⟨ ap (λ e → p .part (f ∘ g ∘ h) hh .η _ (id , e)) (sym (A .F-∘ _ _ # _)) ⟩
      p .part (f ∘ g ∘ h) _ .η _ (id , A ⟪ g ∘ h ⟫ e)          ∎

    s' : Section (PSh[_,_] {C = C} A B) p
    s' .part .η x (f , e) = it .part module s' where
      it : Section B (p' e f)
      it = bshf.split (pull f (inc c)) (p' e f)

    s' .part .is-natural x y f = ext λ g e → bshf.separate (pull (g ∘ f) (inc c)) λ h hh →
      let clo = subst (_∈ J .cover c) (sym (assoc _ _ _)) hh in
      B ⟪ h ⟫ (s'.it y (g ∘ f) (A ⟪ f ⟫ e) .part)             ≡⟨ s'.it y (g ∘ f) (A ⟪ f ⟫ e) .patch _ hh ⟩
      p .part ((g ∘ f) ∘ h) _ .η _ (id , A ⟪ h ⟫ (A ⟪ f ⟫ e)) ≡˘⟨ (λ i → p .part (assoc g f h i) (coe1→i (λ i → assoc g f h i ∈ J .cover c) i hh) .η _ (id , A .F-∘ h f i e)) ⟩
      p .part (g ∘ f ∘ h) _ .η _ (id , A ⟪ f ∘ h ⟫ e)         ≡˘⟨ sym (B .F-∘ _ _ # _) ∙ s'.it x g e .patch (f ∘ h) clo ⟩
      B ⟪ h ⟫ (B ⟪ f ⟫ (s'.it x g e .part))                   ∎

    s' .patch f hf = ext λ x g e →
      let clo = J .cover c .closed (J .cover c .closed hf g) id in
      s'.it x (f ∘ g) e .part                          ≡˘⟨ B .F-id # _ ⟩
      (B ⟪ id ⟫ s'.it x (f ∘ g) e .part)               ≡⟨ s'.it x (f ∘ g) e .patch id clo ⟩
      p .part ((f ∘ g) ∘ id) _ .η x (id , A ⟪ id ⟫ e)  ≡⟨ ap₂ (λ i1 i2 → p .part i1 i2 .η x (id , A ⟪ id ⟫ e)) (idr (f ∘ g)) prop! ⟩
      p .part (f ∘ g) _ .η x (id , A ⟪ id ⟫ e)         ≡⟨ sym (p .patch f hf g (J .cover c .closed hf g) ηₚ _ $ₚ (id , A ⟪ id ⟫ e)) ⟩
      p .part f hf .η x (g ∘ id , A ⟪ id ⟫ e)          ≡⟨ ap (p .part f hf .η x) (Σ-pathp (idr g) (A .F-id # _)) ⟩
      p .part f hf .η x (g , e)                        ∎

    done = from-is-separated₁ psh sep s'
```
