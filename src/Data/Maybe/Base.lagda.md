<!--
```agda
open import 1Lab.Path
open import 1Lab.Type

open import Data.Dec.Base

open import Meta.Traversable
open import Meta.Invariant
open import Meta.Idiom
open import Meta.Bind
open import Meta.Alt
```
-->

```agda
module Data.Maybe.Base where
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
data Maybe {ℓ} (A : Type ℓ) : Type ℓ where
  nothing : Maybe A
  just    : A → Maybe A

{-# BUILTIN MAYBE Maybe #-}
```

```agda
instance
  Map-Maybe : Map (eff Maybe)
  Map-Maybe .map f (just x) = just (f x)
  Map-Maybe .map f nothing  = nothing

  Idiom-Maybe : Idiom (eff Maybe)
  Idiom-Maybe .Idiom.Map-idiom = Map-Maybe

  Idiom-Maybe .Idiom.pure  = just

  Idiom-Maybe .Idiom._<*>_ (just f) (just x) = just (f x)
  Idiom-Maybe .Idiom._<*>_ (just f) nothing  = nothing
  Idiom-Maybe .Idiom._<*>_ nothing  _        = nothing

  Bind-Maybe : Bind (eff Maybe)
  Bind-Maybe .Bind.Idiom-bind = Idiom-Maybe

  Bind-Maybe ._>>=_ (just x) f = f x
  Bind-Maybe ._>>=_ nothing  f = nothing

  Alt-Maybe : Alt (eff Maybe)
  Alt-Maybe .Alt.fail = nothing
  Alt-Maybe .Alt._<|>_ (just x) y = just x
  Alt-Maybe .Alt._<|>_ nothing y = y

  Traversable-Maybe : Traversable (eff Maybe)
  Traversable-Maybe .Traversable.traverse f nothing  = pure nothing
  Traversable-Maybe .Traversable.traverse f (just x) = just <$> f x

Maybe-rec : (A → B) → B → Maybe A → B
Maybe-rec f b (just x) = f x
Maybe-rec f b nothing = b
```

```agda
from-just : A → Maybe A → A
from-just def (just x) = x
from-just def nothing = def
```

<!--
```agda
is-just : Maybe A → Type
is-just (just _) = ⊤
is-just nothing = ⊥

is-nothing : Maybe A → Type
is-nothing (just _) = ⊥
is-nothing nothing = ⊤

nothing≠just : {x : A} → ¬ (nothing ≡ just x)
nothing≠just p = subst is-nothing p tt

just≠nothing : {x : A} → ¬ (just x ≡ nothing)
just≠nothing p = subst is-just p tt

just-inj : ∀ {x y : A} → just x ≡ just y → x ≡ y
just-inj {x = x} = ap (from-just x)

instance
  Discrete-Maybe : ⦃ d : Discrete A ⦄ → Discrete (Maybe A)
  Discrete-Maybe {x = just x} {just y}   = invmap (ap just) just-inj (x ≡? y)
  Discrete-Maybe {x = just x} {nothing}  = no just≠nothing
  Discrete-Maybe {x = nothing} {just x}  = no nothing≠just
  Discrete-Maybe {x = nothing} {nothing} = yes refl
```
-->

## Pointed types as Maybe-algebras

```agda
maybe→alt : ∀ {M : Effect} {ℓ} {A : Type ℓ}
          → ⦃ _ : Alt M ⦄ ⦃ _ : Idiom M ⦄ → Maybe A → M .Effect.₀ A
maybe→alt (just x) = pure x
maybe→alt nothing  = fail
```
