<!--
```agda
open import 1Lab.Path
open import 1Lab.Type

open import Meta.Idiom
```
-->

```agda
module Meta.Traversable where
```

# Meta: Traversable

The `Traverse`{.Agda} class captures the idea that some containers
"commute with effects", where an effect is anything implementing
`Idiom`{.Agda}:

```agda
record Traversable (F : Effect) : Typeω where
  private module F = Effect F
  field
    traverse
      : ∀ {ℓ₀ ℓ₁} {M : Effect} ⦃ i : Idiom M ⦄ (let module M = Effect M)
          {a : Type ℓ₀} {b : Type ℓ₁}
      → (a → M.₀ b) → F.₀ a → M.₀ (F.₀ b)

  for
    : ∀ {ℓ₀ ℓ₁} {M : Effect} ⦃ i : Idiom M ⦄ (let module M = Effect M)
        {a : Type ℓ₀} {b : Type ℓ₁}
    → F.₀ a → (a → M.₀ b) → M.₀ (F.₀ b)
  for x f = traverse f x

open Traversable ⦃ ... ⦄ public

sequence
  : ∀ {M F : Effect} ⦃ _ : Idiom M ⦄ ⦃ _ : Traversable F ⦄
      (let module M = Effect M ; module F = Effect F) {ℓ}
      {a : Type ℓ}
  → F.₀ (M.₀ a) → M.₀ (F.₀ a)
sequence = traverse id
```
