<!--
```agda
open import 1Lab.Type

open import Meta.Idiom
open import Meta.Bind
open import Meta.Alt
```
-->

```agda
module Data.Maybe.Base where

open import Prim.Data.Maybe public
```

# The Maybe type

<!--
```agda
private variable
  ℓ ℓ' : Level
  A B C : Type ℓ
```
-->

<!-- TODO [Amy 2022-12-14]
Write something informative here
-->


```agda
map : (A → B) → Maybe A → Maybe B
map f (just x) = just (f x)
map f nothing  = nothing

extend : Maybe A → (A → Maybe B) → Maybe B
extend (just x) k = k x
extend nothing k  = nothing

Maybe-rec : (A → B) → B → Maybe A → B
Maybe-rec f b (just x) = f x
Maybe-rec f b nothing = b
```

<!--
```agda
instance
  Map-Maybe : Map (eff Maybe)
  Map-Maybe .Map._<$>_ = map

  Idiom-Maybe : Idiom (eff Maybe)
  Idiom-Maybe .Idiom.pure = just
  Idiom-Maybe .Idiom._<*>_ = λ where
    (just f) (just x) → just (f x)
    _ _ → nothing

  Bind-Maybe : Bind (eff Maybe)
  Bind-Maybe .Bind._>>=_ = extend
```
-->

## Pointed types as Maybe-algebras

```agda
maybe→alt : ∀ {M : Effect} {ℓ} {A : Type ℓ}
          → ⦃ _ : Alt M ⦄ ⦃ _ : Idiom M ⦄ → Maybe A → M .Effect.₀ A
maybe→alt (just x) = pure x
maybe→alt nothing  = fail
```
