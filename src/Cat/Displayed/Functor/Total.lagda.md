<!--
```agda
open import Cat.Displayed.Functor
open import Cat.Displayed.Total
open import Cat.Displayed.Base
open import Cat.Functor.Base
open import Cat.Prelude
```
-->

```agda
module Cat.Displayed.Functor.Total where
```

# Total functor

Given [[displayed categories]] $\cE \liesover \cA$ and $\cF \liesover
\cB$, and a [[displayed functor]] $F' : \cE \to \cF$ over $F : \cA \to
\cB$, we can recover an ordinary [[functor]] $\int F : \int \cE \to \int
\cF$ between [[total categories]].

<!--
```agda
module _
  {oa ℓa ob ℓb oe ℓe of ℓf}
  {A : Precategory oa ℓa} {B : Precategory ob ℓb}
  {ℰ : Displayed A oe ℓe} {ℱ : Displayed B of ℓf}
  {F : Functor A B} (F' : Displayed-functor F ℰ ℱ)
  where
```
-->

```agda
  ∫ᶠ : Functor (∫ ℰ) (∫ ℱ)
  ∫ᶠ = record where
    open Functor F
    open Displayed-functor F'

    F₀ (x , x') = F₀ x , F₀' x'
    F₁ (∫hom f f') = ∫hom (F₁ f) (F₁' f')
    F-id = ∫Hom-path ℱ F-id F-id'
    F-∘ (∫hom f f') (∫hom g g') = ∫Hom-path ℱ (F-∘ f g) F-∘'
```

The total functor respects the projection `πᶠ`{.Agda} to the base category
in the following sense:

```agda
  ∫ᶠ-preserves-base : F F∘ (πᶠ ℰ) ≡ (πᶠ ℱ) F∘ ∫ᶠ
  ∫ᶠ-preserves-base = Functor-path (λ x → refl) (λ f → refl)
```