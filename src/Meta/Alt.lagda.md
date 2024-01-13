<!--
```agda
open import 1Lab.Type

open import Meta.Idiom
open import Meta.Bind
```
-->

```agda
module Meta.Alt where
```

```agda
record Alt (M : Effect) : Typeω where
  private module M = Effect M
  field
    fail  : ∀ {ℓ} {A : Type ℓ} → M.₀ A
    _<|>_ : ∀ {ℓ} {A : Type ℓ} → M.₀ A → M.₀ A → M.₀ A

  infixl 3 _<|>_

open Alt ⦃ ... ⦄ public

guard
  : ∀ {M : Effect} (let module M = Effect M) ⦃ appl : Idiom M ⦄ ⦃ alt : Alt M ⦄
  → Bool → M.₀ ⊤
guard true = pure tt
guard false = fail

guardM
  : ∀ {M : Effect} (let module M = Effect M) ⦃ mon : Bind M ⦄ ⦃ alt : Alt M ⦄
  → M.₀ Bool → M.₀ ⊤
guardM M = M >>= guard
```
