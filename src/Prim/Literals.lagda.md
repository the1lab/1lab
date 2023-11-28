<!--
```agda
open import Prim.Data.Sigma
open import Prim.Data.Nat
open import Prim.Type
```
-->

```agda
module Prim.Literals where
```

# Primitive: Overloaded literals

We define the records `Number`{.Agda}, `Negative`{.Agda} and
`String`{.Agda} to allow overloading of the numeric literals.

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

{-# DISPLAY Number.fromNat _ n = fromNat n #-}
{-# DISPLAY Negative.fromNeg _ n = fromNeg n #-}

instance
  Number-Nat : Number Nat
  Number-Nat .Number.Constraint _ = ⊤
  Number-Nat .Number.fromNat n = n
```
