<!--
```agda
open import Cat.Diagram.Pullback.Properties
open import Cat.Functor.Adjoint.Continuous
open import Cat.Diagram.Pullback.Along
open import Cat.Functor.Adjoint.Hom
open import Cat.Diagram.Subobject
open import Cat.Instances.Functor
open import Cat.Diagram.Pullback
open import Cat.Diagram.Terminal
open import Cat.Functor.Adjoint
open import Cat.Instances.Sets
open import Cat.Diagram.Sieve
open import Cat.Prelude

import Cat.Displayed.Instances.Subobjects.Reasoning as Sub
import Cat.Functor.Reasoning.Presheaf as PSh
import Cat.Instances.Presheaf.Limits as Lim
import Cat.Reasoning as Cat

open Subobject-classifier
open is-generic-subobject
open is-pullback-along
open is-pullback
```
-->

```agda
module Cat.Instances.Presheaf.Subobjects where
```

# The subobject classifier presheaf

```agda
module _ {o ℓ} {C : Precategory o ℓ} where
```

<!--
```agda
module _ {ℓ} (C : Precategory ℓ ℓ) where
  open Lim ℓ C
  open Sub {C = PSh ℓ C} PSh-pullbacks
  open Functor
  open Cat C
  open _=>_
```
-->

```agda
  tru : Terminal.top PSh-terminal => Sieves {C = C}
  tru .η x _            = maximal'
  tru .is-natural x y f = ext λ a {V} f → Ω-ua _ _
```

```agda
  psh-name : ∀ {X : ⌞ PSh ℓ C ⌟} → Subobject X → X => Sieves {C = C}
  psh-name {X} so .η x e .arrows h = elΩ (fibre (so .map .η _) (X ⟪ h ⟫ e))
  psh-name {X} so .η x e .closed {f = f} = elim! λ x p g →
    let
      q =
        so .map .η _ (so .domain ⟪ g ⟫ x) ≡⟨ so .map .is-natural _ _ _ $ₚ _ ⟩
        X ⟪ g ⟫ (so .map .η _ x)          ≡⟨ ap₂ (X .F₁) refl p ⟩
        X ⟪ g ⟫ (X ⟪ f ⟫ e)               ≡⟨ PSh.collapse X refl ⟩
        X ⟪ f ∘ g ⟫ e                     ∎
    in inc (_ , q)
  psh-name {X} so .is-natural x y f = ext λ x {V} f → Ω-ua
    (□-map λ (e , p) → e , p ∙ PSh.collapse X refl)
    (□-map λ (e , p) → e , p ∙ PSh.expand X refl)
```


```agda
  done : Subobject-classifier (PSh ℓ C)
  done .Subobject-classifier.Ω = Sieves {C = C}

  done .Subobject-classifier.true .Sub.domain      = _
  done .Subobject-classifier.true .Sub.map         = tru
  done .Subobject-classifier.true .Sub.monic _ _ _ = trivial!

  done .generic .name = psh-name
  done .generic .classifies {X} m = record { has-is-pb = pb } where
    emb = is-monic→is-embedding-at (m .monic)

    square→pt
      : ∀ {P'} {p₁' : P' => X} {p₂' : P' => _}
      → psh-name m ∘nt p₁' ≡ tru ∘nt p₂'
      → ∀ {a} (b : P' ʻ a) → fibre (m .map .η a) (p₁' .η a b)
    square→pt {p₁' = p₁'} p b =
      let
        (elt , q) = □-out (emb _) (subst (id ∈_) (sym (p ηₚ _ $ₚ b)) tt)
      in elt , q ∙ PSh.F-id X

    pb : is-pullback (PSh ℓ C) _ _ (NT (λ _ _ → _) (λ x y f → refl)) _
    pb .square = ext λ i x {V} f → to-is-true (inc (_ , m .map .is-natural _ _ _ $ₚ _))

    pb .universal path .η i e = square→pt path e .fst
    pb .universal {P' = P'} {p₁'} p .is-natural x y f = ext λ a → ap fst $
      let
        (pt , q) = square→pt p a
        r =
          m .map .η y (m .domain ⟪ f ⟫ pt) ≡⟨ m .map .is-natural _ _ _ $ₚ _ ⟩
          X ⟪ f ⟫ m .map .η x pt           ≡⟨ ap₂ (X .F₁) refl q ⟩
          X ⟪ f ⟫ (p₁' .η x a)             ≡˘⟨ p₁' .is-natural _ _ _ $ₚ _ ⟩
          p₁' .η y (P' ⟪ f ⟫ a)            ∎
      in emb _ (square→pt p _) (_ , r)

    pb .p₁∘universal {p = p} = ext λ a b → square→pt p b .snd
    pb .p₂∘universal = trivial!
    pb .unique {p = p} q r = ext λ a b → ap fst $
      emb _ (_ , q ηₚ a $ₚ b) (square→pt p _)

  done .generic .unique {X} {m = m} {nm} pb = ext λ i x {U} f →
    let
      emb = is-monic→is-embedding-at (m .monic)

      to : f ∈ nm .η i x → □ (fibre (m .map .η U) (X ⟪ f ⟫ x))
      to wit =
        let
          fold-memb : to-presheaf (nm .η i x) => X
          fold-memb = λ where
            .η i (h , p) → X ⟪ h ⟫ x
            .is-natural x y f → ext λ g e → PSh.expand X refl

          includes : nm ∘nt fold-memb ≡ tru ∘nt Terminal.! PSh-terminal
          includes = ext λ j g hg {U} h →
            nm .η j (X ⟪ g ⟫ x) .arrows h ≡⟨ ap (λ e → e .arrows h) (nm .is-natural _ _ _ $ₚ _) ⟩
            nm .η i x .arrows (g ∘ h)     ≡⟨ to-is-true (nm .η i x .closed hg h) ⟩
            ⊤Ω                            ∎

          members→names : to-presheaf (nm .η i x) => m .domain
          members→names = pb .universal includes

          it = members→names .η U (f , wit)
        in inc (it , pb .p₁∘universal ηₚ _ $ₚ _)

      from : □ (fibre (m .map .η U) (X ⟪ f ⟫ x)) → f ∈ nm .η i x
      from fib =
        let
          (a , prf) = □-out (emb _) fib

          proof =
            maximal'                ≡˘⟨ pb .square ηₚ U $ₚ a ⟩
            nm .η U (m .map .η U a) ≡⟨ ap (nm .η U) prf ⟩
            nm .η U (X ⟪ f ⟫ x)     ≡⟨ nm .is-natural _ _ _ $ₚ _ ⟩
            pullback f (nm .η i x)  ∎
        in subst (_∈ nm .η i x) (idr f) (subst (id ∈_) proof tt)
    in Ω-ua to from
```
