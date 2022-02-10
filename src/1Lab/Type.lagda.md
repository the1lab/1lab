```agda
module 1Lab.Type where
```

# Universes

A **universe** is a type whose inhabitants are types. In Agda, there is
a family of universes, which, by default, is called `Set`. Rather
recently, Agda gained [a flag] to make `Set` not act like a keyword, and
allow renaming it in an import declaration from the `Agda.Primitive`
module.


```agda
open import Agda.Primitive
  renaming (Set to Type ; Setω to Typeω)
  hiding (Prop)
  public
```

`Type`{.Agda} is a type itself, so it's a natural question to ask: does
it belong to a universe? The answer is _yes_. However, Type can not
belong to itself, or we could reproduce Russell's Paradox, as is done
[in this module].

[in this module]: agda://1Lab.Counterexamples.Russell

To prevent this, the universes are parametrised by a _`Level`{.Agda}_,
where the collection of all `ℓ`-sized types is `Type (lsuc ℓ)`:

```agda
_ : (ℓ : Level) → Type (lsuc ℓ)
_ = λ ℓ → Type ℓ

level-of : {ℓ : Level} → Type ℓ → Level
level-of {ℓ} _ = ℓ
```

## Built-in Types

Agda comes with built-in definitions for a bunch of types:

```agda
open import Agda.Builtin.Sigma hiding (Σ) public
open import Agda.Builtin.Unit public
open import Agda.Builtin.Bool public
open import Agda.Builtin.Nat public
```

It does not, however, come with a built-in definition of the empty type:

```agda
data ⊥ : Type where

absurd : ∀ {ℓ} {A : Type ℓ} → ⊥ → A
absurd ()
```

The dependent sum of a family of types is notated by `Σ`{.Agda}. The
domain of the family is left implicit. We use a notation for when it
must be made explicit.

```agda
Σ : ∀ {a b} {A : Type a} (B : A → Type b) → Type _
Σ = Agda.Builtin.Sigma.Σ _

module Σ = Agda.Builtin.Sigma.Σ

syntax Σ {A = A} (λ x → B) = Σ[ x ∈ A ] B
infix 5 Σ
```

The non-dependent product type `_×_`{.Agda} can be defined in terms of
the dependent sum type:

```agda
_×_ : ∀ {a b} → Type a → Type b → Type _
A × B = Σ[ _ ∈ A ] B

infixr 4 _×_
```

## Lifting

There is a function which lifts a type to a higher universe:

```agda
record Lift {a} ℓ (A : Type a) : Type (a ⊔ ℓ) where
  constructor lift
  field
    lower : A
```

## Function composition

Since the following definitions are fundamental, they deserve a place in
this module:

```agda
_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
    → (B → C) → (A → B) → A → C
f ∘ g = λ z → f (g z)

infixr 40 _∘_

id : ∀ {ℓ} {A : Type ℓ} → A → A
id x = x
```

<!--
```
open import Agda.Builtin.FromNat public
open import Agda.Builtin.FromNeg public

instance
  Number-Nat : Number Nat
  Number-Nat .Number.Constraint _ = ⊤
  Number-Nat .Number.fromNat n = n

Type∙ : ∀ ℓ → Type (lsuc ℓ)
Type∙ _ = Σ id
```
-->
