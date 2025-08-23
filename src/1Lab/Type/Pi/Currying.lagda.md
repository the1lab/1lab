---
description: |
  Currying pi types.
---
<!--
```agda
open import 1Lab.Type.Sigma
open import 1Lab.Type.Pi
open import 1Lab.Equiv
open import 1Lab.Type
```
-->
```agda
module 1Lab.Type.Pi.Currying where
```

# Currying and uncurrying automation

This module contains proof automation for passing between curried and
uncurried Π types.

## Currying

The core of our currying automation is the following typeclass, which
decomposes a type $A$ into a Π type.

```agda
record Curried {ℓ} (A : Type ℓ) (ℓd ℓf : Level) : Type (ℓ ⊔ lsuc ℓd ⊔ lsuc ℓf) where
  no-eta-equality
  field
    Dom : Type ℓd
    Cod : Dom → Type ℓf
    eqv : ((d : Dom) → Cod d) ≃ A
```

The only interesting instances of `Curried` check to see if $A$
is an iterated Π type, and shuffle over elements of the codomain into
a Σ in the domain.

```agda
instance
  Curried-Π
    : ∀ {ℓ ℓ' ℓ'' ℓd ℓf} {A : Type ℓ} {B : A → Type ℓ'} {C : (a : A) → B a → Type ℓ''}
    → ⦃ _ : ∀ {a} → Curried ((b : B a) → C a b) ℓd ℓf ⦄
    → Curried ((a : A) (b : B a) → C a b) (ℓd ⊔ ℓ) ℓf
  Curried-Π {A = A} ⦃ c ⦄ .Curried.Dom = Σ[ a ∈ A ] (Curried.Dom (c {a}))
  Curried-Π {A = A} ⦃ c ⦄ .Curried.Cod (a , d) = Curried.Cod c d
  Curried-Π {A = A} ⦃ c ⦄ .Curried.eqv = curry≃ ∙e Π-ap-cod λ a → Curried.eqv c

  Curried-Π'
    : ∀ {ℓ ℓ' ℓ'' ℓd ℓf} {A : Type ℓ} {B : A → Type ℓ'} {C : (a : A) → B a → Type ℓ''}
    → ⦃ _ : ∀ {a} → Curried ((b : B a) → C a b) ℓd ℓf ⦄
    → Curried ({a : A} (b : B a) → C a b) (ℓd ⊔ ℓ) ℓf
  Curried-Π' {A = A} ⦃ c ⦄ .Curried.Dom = Σ[ a ∈ A ] (Curried.Dom (c {a}))
  Curried-Π' {A = A} ⦃ c ⦄ .Curried.Cod (a , d) = Curried.Cod c d
  Curried-Π' {A = A} ⦃ c ⦄ .Curried.eqv = curry≃ ∙e Π-impl≃ ∙e Π'-ap-cod λ a → Curried.eqv c
```

Finally, we have an `INCOHERENT` base case that will match only when
we have run out of iterated Π types.

```agda
  Curried-default
    : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
    → Curried ((a : A) → B a) ℓ ℓ'
  Curried-default {A = A} {B = B} .Curried.Dom = A
  Curried-default {A = A} {B = B} .Curried.Cod = B
  Curried-default {A = A} {B = B} .Curried.eqv = id≃
  {-# INCOHERENT Curried-default #-}
```

Now that we've got our instances in place, we can use instance arguments
to compute the fully curried version of a type.

```agda
Curry : ∀ {ℓ ℓd ℓf} → (A : Type ℓ) → ⦃ C : Curried A ℓd ℓf ⦄ → Type (ℓd ⊔ ℓf)
Curry A ⦃ C ⦄ = (x : Curried.Dom C) → Curried.Cod C x
{-# NOINLINE Curry #-}
```

We also expose the equivlance between the original type and it's
curried form.

```agda
curry!
  : ∀ {ℓ ℓd ℓf}
  → {A : Type ℓ}
  → ⦃ C : Curried A ℓd ℓf ⦄
  → A ≃ Curry A
curry! ⦃ C ⦄ = Curried.eqv C e⁻¹
{-# NOINLINE curry! #-}
```

## Uncurrying

The uncurrying typeclass is identical to the currying typeclass in
all but name.

```agda
record Uncurried {ℓ} (A : Type ℓ) (ℓd ℓf : Level) : Type (ℓ ⊔ lsuc ℓd ⊔ lsuc ℓf) where
  no-eta-equality
  field
    Dom : Type ℓd
    Cod : Dom → Type ℓf
    eqv : ((d : Dom) → Cod d) ≃ A
```

However, the instances for `Uncurried` go in the opposite direction.

```agda
instance
  Uncurried-Π
    : ∀ {ℓ ℓ' ℓ'' ℓd ℓf} {A : Type ℓ} {B : A → Type ℓ'} {C : Σ A B → Type ℓ''}
    → ⦃ _ : ∀ {a} → Uncurried ((b : B a) → C (a , b)) ℓd ℓf ⦄
    → Uncurried ((ab : Σ A B) → C ab) ℓ (ℓd ⊔ ℓf)
  Uncurried-Π {A = A} ⦃ c ⦄ .Uncurried.Dom = A
  Uncurried-Π {A = A} ⦃ c ⦄ .Uncurried.Cod a = (d : Uncurried.Dom (c {a})) → Uncurried.Cod (c {a}) d
  Uncurried-Π {A = A} ⦃ c ⦄ .Uncurried.eqv = Π-ap-cod (λ a → Uncurried.eqv c) ∙e curry≃ e⁻¹

  Uncurried-default
    : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
    → Uncurried ((a : A) → B a) ℓ ℓ'
  Uncurried-default {A = A} {B = B} .Uncurried.Dom = A
  Uncurried-default {A = A} {B = B} .Uncurried.Cod = B
  Uncurried-default {A = A} {B = B} .Uncurried.eqv = id≃
```

We expose a similar API for uncurrying.

```agda
Uncurry : ∀ {ℓ ℓd ℓf} → (A : Type ℓ) → ⦃ C : Uncurried A ℓd ℓf ⦄ → Type (ℓd ⊔ ℓf)
Uncurry A ⦃ C ⦄ = (x : Uncurried.Dom C) → Uncurried.Cod C x
{-# NOINLINE Uncurry #-}

uncurry!
  : ∀ {ℓ ℓd ℓf}
  → {A : Type ℓ}
  → ⦃ C : Uncurried A ℓd ℓf ⦄
  → A ≃ Uncurry A
uncurry! ⦃ C ⦄ = Uncurried.eqv C e⁻¹
{-# NOINLINE uncurry! #-}
```
