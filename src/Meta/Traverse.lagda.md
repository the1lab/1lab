<!--
```agda
open import 1Lab.Path
open import 1Lab.Type

open import Data.List.Base

open import Meta.Idiom

open import Prim.Data.Maybe
```
-->

```agda
module Meta.Traverse where
```

# Meta: Traverse

The `Traverse`{.Agda} class captures the idea that some containers
"commute with effects", where an effect is anything implementing
`Idiom`{.Agda}:

```agda
record Traverse (F : Effect) : Typeω where
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

open Traverse ⦃ ... ⦄ public

instance
  Traverse-List : Traverse (eff List)
  Traverse-List .Traverse.traverse {M = M} {a = a} {b = b} = go where
    private module M = Effect M
    go : (a → M.₀ b) → List a → M.₀ (List b)
    go f []       = pure []
    go f (x ∷ xs) = ⦇ f x ∷ go f xs ⦈

  Traverse-Maybe : Traverse (eff Maybe)
  Traverse-Maybe .Traverse.traverse f (just x) = just <$> f x
  Traverse-Maybe .Traverse.traverse f nothing  = pure nothing
```
