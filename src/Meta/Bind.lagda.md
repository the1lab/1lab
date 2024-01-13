<!--
```agda
open import 1Lab.Type

open import Meta.Idiom
```
-->

```agda
module Meta.Bind where
```

# Primitive: `do` syntax

```agda
record Bind (M : Effect) : Typeω where
  private module M = Effect M
  field
    _>>=_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → M.₀ A → (A → M.₀ B) → M.₀ B
    ⦃ Idiom-bind ⦄ : Idiom M

  _>>_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → M.₀ A → M.₀ B → M.₀ B
  _>>_ f g = f >>= λ _ → g

  infixl 1 _>>=_

  _=<<_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (A → M.₀ B) → M.₀ A → M.₀ B
  _=<<_ f x = x >>= f

  infixr 1 _=<<_

open Bind ⦃ ... ⦄ public
```
