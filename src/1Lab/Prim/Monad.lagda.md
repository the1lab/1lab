```agda
open import 1Lab.Type

module 1Lab.Prim.Monad where
```

# Primitive: `do` syntax

```agda
record
  Do-syntax (f : Level → Level) (M : ∀ {ℓ} → Type ℓ → Type (f ℓ)) : Typeω where
  field
    _>>=_ : ∀ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′} → M A → (A → M B) → M B

  _>>_ : ∀ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′} → M A → M B → M B
  _>>_ f g = f >>= λ _ → g

  _=<<_ : ∀ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′} → (A → M B) → M A → M B
  _=<<_ f x = x >>= f

open Do-syntax ⦃ ... ⦄ public

record Idiom-syntax (f : Level → Level) (M : ∀ {ℓ} → Type ℓ → Type (f ℓ)) : Typeω where
  field
    pure  : ∀ {ℓ} {A : Type ℓ} → A → M A
    _<*>_ : ∀ {ℓ} {ℓ′} {A : Type ℓ} {B : Type ℓ′} → M (A → B) → M A → M B

  _<$>_ : ∀ {ℓ} {ℓ′} {A : Type ℓ} {B : Type ℓ′} → (A → B) → M A → M B
  f <$> x = ⦇ f x ⦈
  infixl 4 _<*>_ _<$>_

  _<&>_ : ∀ {ℓ} {ℓ′} {A : Type ℓ} {B : Type ℓ′} → M A → (A → B) → M B
  x <&> f = ⦇ f x ⦈

open Idiom-syntax ⦃ ... ⦄ public

record Alt-syntax (f : Level → Level) (M : ∀ {ℓ} → Type ℓ → Type (f ℓ)) : Typeω where
  field
    fail : ∀ {ℓ} {A : Type ℓ} → M A
    _<|>_ : ∀ {ℓ} {A : Type ℓ} → M A → M A → M A
  infixl 3 _<|>_

open Alt-syntax ⦃ ... ⦄ public

guard
  : ∀ {f : Level → Level} {M : ∀ {ℓ} → Type ℓ → Type (f ℓ)}
    ⦃ appl : Idiom-syntax f M ⦄
    ⦃ alt : Alt-syntax f M ⦄
  → Bool → M ⊤
guard true = pure tt
guard false = fail

guardM
  : ∀ {f : Level → Level} {M : ∀ {ℓ} → Type ℓ → Type (f ℓ)}
    ⦃ appl : Idiom-syntax f M ⦄
    ⦃ mon : Do-syntax f M ⦄
    ⦃ alt : Alt-syntax f M ⦄
  → M Bool → M ⊤
guardM M = M >>= guard
```
