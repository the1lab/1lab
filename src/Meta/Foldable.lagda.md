<!--
```agda
open import 1Lab.Type

open import Meta.Idiom
open import Meta.Alt
```
-->

```agda
module Meta.Foldable where
```

# Meta: Foldable effects

```agda
record Foldable (F : Effect) : Typeω where
  private module F = Effect F
  field
    foldr : ∀ {ℓ ℓ'} {a : Type ℓ} {b : Type ℓ'} → (a → b → b) → b → F.₀ a → b

open Foldable ⦃ ... ⦄ public

asum
  : ∀ {F M : Effect} ⦃ f : Foldable F ⦄ ⦃ a : Alt M ⦄ {ℓ} {A : Type ℓ}
    (let module F = Effect F) (let module M = Effect M)
  → F.₀ (M.₀ A) → M.₀ A
asum = foldr _<|>_ fail

nondet
  : ∀ (F : Effect) {M} ⦃ f : Foldable F ⦄ ⦃ t : Map F ⦄
      ⦃ a : Alt M ⦄ ⦃ i : Idiom M ⦄
      {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → (let module F = Effect F)
  → (let module M = Effect M)
  → F.₀ A → (A → M.₀ B) → M.₀ B
nondet F ⦃ f = f ⦄ xs k = asum ⦃ f = f ⦄ (k <$> xs)
```
