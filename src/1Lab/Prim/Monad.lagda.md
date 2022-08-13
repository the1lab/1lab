```agda
open import 1Lab.Type

module 1Lab.Prim.Monad where
```

# Primitive: `do` syntax

```agda
record Do-syntax (M : ∀ {ℓ} → Type ℓ → Type ℓ) : Typeω where
  field
    _>>=_ : ∀ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′} → M A → (A → M B) → M B

  _>>_ : ∀ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′} → M A → M B → M B
  _>>_ f g = f >>= λ _ → g

open Do-syntax {{...}} public

record Idiom-syntax (M : ∀ {ℓ} → Type ℓ → Type ℓ) : Typeω where
  field
    pure  : ∀ {ℓ} {A : Type ℓ} → A → M A
    _<*>_ : ∀ {ℓ} {ℓ′} {A : Type ℓ} {B : Type ℓ′} → M (A → B) → M A → M B

  _<$>_ : ∀ {ℓ} {ℓ′} {A : Type ℓ} {B : Type ℓ′} → (A → B) → M A → M B
  f <$> x = ⦇ f x ⦈
  infixl 4 _<*>_ _<$>_

open Idiom-syntax {{...}} public

record Alt-syntax (M : ∀ {ℓ} → Type ℓ → Type ℓ) : Typeω where
  field
    _<|>_ : ∀ {ℓ} {A : Type ℓ} → M A → M A → M A
  infixl 3 _<|>_

open Alt-syntax {{...}} public
```
