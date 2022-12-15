```agda
open import Cat.Diagram.Pullback.Properties
open import Cat.Instances.Sets.Complete
open import Cat.Morphism.Factorisation
open import Cat.Morphism.StrongEpi
open import Cat.Diagram.Pullback
open import Cat.Instances.Sets
open import Cat.Regular
open import Cat.Prelude

open import Data.Set.Surjection

module Cat.Regular.Instances.Sets where
```

# Sets is regular

<!--
```agda
open Factorisation
open is-regular
```
-->

We can prove that the category of $\sets$ is regular by investigating
the relationship between [surjections], regular epimorphisms, and
arbitrary epimorphisms. Fortunately, they _all_ coincide, and we already
[know] that $\sets$ is finitely complete, so it only remains to show
that morphisms have an epi-mono factorisation, and that epimorphy is
stable under pullbacks.

[surjections]: Data.Set.Surjection.html#surjections-are-epic
[know]: Cat.Instances.Sets.Complete.html#finite-set-limits

```agda
Sets-regular : ∀ {ℓ} → is-regular (Sets ℓ)
Sets-regular .has-is-lex = Sets-finitely-complete
```

For the factorisation, we go with the pre-existing notion of
`image`{.Agda}, not only because we're trying to compute an _image_
factorisation, but because there is a natural surjection $a \epi \im(f)$
and an embedding $\im(f) \mono b$.

```agda
Sets-regular .factor {a} {b} f = λ where
  .mediating → el! (image f)
  .mediate x → (f x) , inc (x , refl)
  .forget    → fst

  .mediate∈E → inc (is-regular-epi→is-strong-epi (Sets _) {a} {el! (image f)} _
    (surjective→regular-epi _ _ _ λ {
      (x , y) → ∥-∥-rec squash (λ { (pre , p) → inc (pre , Σ-prop-path! p) }) y }))

  .forget∈M  → inc (embedding→monic (Subset-proj-embedding (λ _ → squash)))
  .factors   → refl
```

It additionally suffices to verify this only for our choice of pullbacks
(rather than arbitrary pullback squares), for which the following
calculation does perfectly:

```agda
Sets-regular .stable =
  canonically-stable
    (λ {a} {b} → is-strong-epi (Sets _) {a} {b}) Sets-is-category Sets-pullbacks
    λ {a} {b} {c} f g (f-epi , _) →
    let
      rem₁ : ∀ x → ∥ fibre f x ∥
      rem₁ = epi→surjective a b f λ {c} → f-epi {c}

      T : Set _
      T = Sets-pullbacks {A = c} {a} {b} g f .Pullback.apex

      pb : ∣ T ∣ → ∣ c ∣
      pb = Sets-pullbacks {A = c} {a} {b} g f .Pullback.p₁

      rem₂ : ∀ x → ∥ fibre pb x ∥
      rem₂ x = do
        (f^*fx , p) ← rem₁ (g x)
        pure ((x , f^*fx , sym p) , refl)
    in
      is-regular-epi→is-strong-epi (Sets _) {a = el! _} {c} _
        (surjective→regular-epi _ _ _ rem₂)
```
