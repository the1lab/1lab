```agda
open import 1Lab.Type

open import Data.List.Base

module Meta.Idiom where
```

# Meta: Idiom

The `Idiom`{.Agda} class, probably better known as `Applicative` (from
languages like Haskell and the Agda standard library), captures the
"effects with parallel composition", where an "effect" is simply a
mapping from types to types, with an arbitrary adjustment of universe
levels:

```agda
record Effect : Typeω where
  constructor eff
  field
    {adj} : Level → Level
    ₀     : ∀ {ℓ} → Type ℓ → Type (adj ℓ)
```

The adjustment of universe levels lets us consider, for example, a
"power set" effect, where the adjustment is given by `lsuc`. In most
cases, Agda can infer the adjustment, so we can use the `eff`{.Agda}
constructor.

```agda
record Map (M : Effect) : Typeω where
  private module M = Effect M
  field
    _<$>_ : ∀ {ℓ} {ℓ′} {A : Type ℓ} {B : Type ℓ′} → (A → B) → M.₀ A → M.₀ B

  infixl 4 _<$>_ _<&>_

  _<&>_ : ∀ {ℓ} {ℓ′} {A : Type ℓ} {B : Type ℓ′} → M.₀ A → (A → B) → M.₀ B
  x <&> f = f <$> x

instance
  Map-List : Map (eff List)
  Map-List .Map._<$>_ = map

record Idiom (M : Effect) : Typeω where
  private module M = Effect M
  field
    ⦃ Map-idiom ⦄ : Map M
    pure  : ∀ {ℓ} {A : Type ℓ} → A → M.₀ A
    _<*>_ : ∀ {ℓ} {ℓ′} {A : Type ℓ} {B : Type ℓ′} → M.₀ (A → B) → M.₀ A → M.₀ B

  infixl 4 _<*>_


open Map ⦃ ... ⦄ public
open Idiom ⦃ ... ⦄ public
```
