<!--
```agda
open import 1Lab.Type
```
-->

```agda
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
    map : ∀ {ℓ} {ℓ'} {A : Type ℓ} {B : Type ℓ'} → (A → B) → M.₀ A → M.₀ B

record Idiom (M : Effect) : Typeω where
  private module M = Effect M
  field
    ⦃ Map-idiom ⦄ : Map M
    pure  : ∀ {ℓ} {A : Type ℓ} → A → M.₀ A
    _<*>_ : ∀ {ℓ} {ℓ'} {A : Type ℓ} {B : Type ℓ'} → M.₀ (A → B) → M.₀ A → M.₀ B

  infixl 4 _<*>_

open Idiom ⦃ ... ⦄ public
open Map   ⦃ ... ⦄ public

infixl 4 _<$>_ _<&>_

_<$>_ : ∀ {ℓ ℓ'} {M : Effect} ⦃ _ : Map M ⦄ {A : Type ℓ} {B : Type ℓ'}
      → (A → B) → M .Effect.₀ A → M .Effect.₀ B
f <$> x = map f x

_<$_ : ∀ {ℓ ℓ'} {M : Effect} ⦃ _ : Map M ⦄ {A : Type ℓ} {B : Type ℓ'}
      → B → M .Effect.₀ A → M .Effect.₀ B
c <$ x = map (λ _ → c) x

_<&>_ : ∀ {ℓ ℓ'} {M : Effect} ⦃ _ : Map M ⦄ {A : Type ℓ} {B : Type ℓ'}
      → M .Effect.₀ A → (A → B) → M .Effect.₀ B
x <&> f = map f x

module _
  {M N : Effect} (let module M = Effect M; module N = Effect N) ⦃ _ : Map M ⦄ ⦃ _ : Map N ⦄
  {ℓ} {ℓ'} {A : Type ℓ} {B : Type ℓ'}
  where

  _<<$>>_ : (A → B) → M.₀ (N.₀ A) → M.₀ (N.₀ B)
  f <<$>> a = (f <$>_) <$> a

  _<<&>>_ : M.₀ (N.₀ A) → (A → B) → M.₀ (N.₀ B)
  x <<&>> f = f <<$>> x

when : ∀ {M : Effect} (let module M = Effect M) ⦃ app : Idiom M ⦄
     → Bool → M.₀ ⊤ → M.₀ ⊤
when true  t = t
when false _ = pure tt

unless : ∀ {M : Effect} (let module M = Effect M) ⦃ app : Idiom M ⦄
       → Bool → M.₀ ⊤ → M.₀ ⊤
unless false t = t
unless true  _ = pure tt
```
