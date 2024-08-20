---
description: |
  Algebraic weak factorisation systems.
---
<!--
```agda
open import Cat.Displayed.Instances.Factorisations
open import Cat.Morphism.Factorisation.Functorial
open import Cat.Displayed.Instances.Lifting
open import Cat.Displayed.Instances.Comma
open import Cat.Diagram.Comonad
open import Cat.Displayed.Total
open import Cat.Diagram.Monad
open import Cat.Prelude

import Cat.Reasoning
```
-->
```agda
module Cat.Morphism.Factorisation.Algebraic where
```

# Algebraic weak factorisation systems

<!--
```agda
module _ {o ℓ} (C : Precategory o ℓ) where
  open Cat.Reasoning C
  open Total-hom
  open Functor
  open _=>_
```
-->

```agda
  record AWFS : Type (o ⊔ ℓ) where
    no-eta-equality
    field
      functorial : Functorial-factorisation C

    open Functorial-factorisation functorial public

    field
      comult : Left => Left F∘ Left
      mult : Right F∘ Right => Right
      left-comonad : is-comonad (∫ (Arrows C)) Left counit comult
      right-monad : is-monad (∫ (Arrows C)) Right unit mult

    open is-monad right-monad public
    open is-comonad left-comonad
      renaming (left-ident to left-coident; right-ident to right-coident)
      public

    -- Let's compute exactly what data we get out of an AWFS.
    -- This should probably *be* the definition, rather than something
    -- we recover after the fact.

    μ : ∀ {x y} (f : Hom x y) → Hom (fac (right f)) (fac f)
    μ {x} {y} f = mult .η ((x , y) , f) .hom .fst

    δ : ∀ {x y} (f : Hom x y) → Hom (fac f) (fac (left f))
    δ {x} {y} f = comult .η ((x , y) , f) .hom .snd

    μ-right : ∀ {x y} (f : Hom x y) → right f ∘ μ f ≡ right (right f)
    μ-right f =
      mult .η (_ , f) .preserves
      ∙ eliml (sym (idr _) ∙ ap (snd ⊙ hom) (right-ident {_ , f}))

    δ-left : ∀ {x y} (f : Hom x y) → left (left f) ≡ δ f ∘ left f
    δ-left f =
      intror (sym (idl _) ∙ ap (fst ⊙ hom) (left-coident {_ , f}))
      ∙ comult .η (_ , f) .preserves

    μ-left : ∀ {x y} (f : Hom x y) → μ f ∘ left (right f) ≡ id
    μ-left f =
      ap (fst ⊙ hom) (right-ident {_ , f})

    δ-right : ∀ {x y} (f : Hom x y) → right (left f) ∘ δ f ≡ id
    δ-right f =
      ap (snd ⊙ hom) (right-coident {_ , f})

    μ-split-left
      : ∀ {x y} (f : Hom x y)
      → (p : id ∘ f ≡ right f ∘ left f)
      → μ f ∘ split id (left f) p ≡ id
    μ-split-left f p =
      ap (λ p → μ f ∘ split id (left f) p) prop!
      ∙ ap (fst ⊙ hom) (left-ident {_ , f})

    δ-split-left
      : ∀ {x y} (f : Hom x y)
      → (p : right f ∘ left f ≡ f ∘ id)
      → split (right f) id p ∘ η comult ((x , y) , f) .hom .snd
         ≡ id
    δ-split-left f p =
      ap (λ p → split (right f) id p ∘ δ f) prop!
      ∙ ap (snd ⊙ hom) (left-coident {_ , f})

    μ-split-μ
      : ∀ {x y} (f : Hom x y)
      → (p : id ∘ right (right f) ≡ right f ∘ μ f)
      → μ f ∘ split id (μ f) p ≡ μ f ∘ μ (right f)
    μ-split-μ f p i = hcomp (∂ i) λ where
        j (i = i0) → μ f ∘ split (q j) (μ f) (r j)
        j (i = i1) → μ f ∘ μ (right f)
        j (j = i0) → mult-assoc {_ , f} i .hom .fst
      where
        q : mult .η (_ , f) .hom .snd ≡ id
        q = sym (idr _) ∙ ap (snd ⊙ hom) (right-ident {_ , f})

        r : (i : I) → q i ∘ right (right f) ≡ right f ∘ μ f
        r i =
          is-prop→pathp (λ i → Hom-set _ _ (q i ∘ right (right f)) (right f ∘ μ f))
          (sym (mult .η (_ , f) .preserves))
          p i

    δ-split-δ
      : ∀ {x y} (f : Hom x y)
      → (p : δ f ∘ left f ≡ left (left f) ∘ id)
      → split (δ f) id p ∘ δ f ≡ δ (left f) ∘ δ f
    δ-split-δ f p i = hcomp (∂ i) λ where
        j (i = i0) → split (δ f) (q j) (r j) ∘ δ f
        j (i = i1) → δ (left f) ∘ δ f
        j (j = i0) → comult-assoc {_ , f} i .hom .snd
      where
        q : comult .η (_ , f) .hom .fst ≡ id
        q = sym (idl _) ∙ ap (fst ⊙ hom) (left-coident {_ , f})

        r : (i : I) → δ f ∘ left f ≡ left (left f) ∘ q i
        r i =
          is-prop→pathp (λ i → Hom-set _ _ (δ f ∘ left f) (left (left f) ∘ q i))
            (sym (comult .η (_ , f) .preserves))
            p i
```
