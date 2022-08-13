```agda
open import 1Lab.Prim.Data.Sigma
open import 1Lab.Prim.Data.Nat
open import 1Lab.Prim.Type

module 1Lab.Prim.Numerals where
```

# Primitive: Overloaded numerals

We define the records `Number`{.Agda} and `Negative`{.Agda} to allow
overloading of the numeric literals.

```agda
record Number {a} (A : Type a) : Type (lsuc a) where
  field
    Constraint : Nat → Type a
    fromNat : ∀ n → {{_ : Constraint n}} → A

open Number {{...}} public using (fromNat)

record Negative {a} (A : Type a) : Type (lsuc a) where
  field
    Constraint : Nat → Type a
    fromNeg : ∀ n → {{_ : Constraint n}} → A

open Negative {{...}} public using (fromNeg)

{-# BUILTIN FROMNAT fromNat #-}
{-# DISPLAY Number.fromNat _ n = fromNat n #-}
{-# BUILTIN FROMNEG fromNeg #-}
{-# DISPLAY Negative.fromNeg _ n = fromNeg n #-}

instance
  Number-Nat : Number Nat
  Number-Nat .Number.Constraint _ = ⊤
  Number-Nat .Number.fromNat n = n
```
