```agda
open import 1Lab.Prim.Data.Sigma
open import 1Lab.Prim.Data.Nat
open import 1Lab.Prim.Type

module 1Lab.Prim.Literals where
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

postulate String : Type
{-# BUILTIN STRING String #-}

record IsString {a} (A : Type a) : Type (lsuc a) where
  field
    Constraint : String → Type a
    fromString : (s : String) {{_ : Constraint s}} → A

open IsString {{...}} public using (fromString)

{-# BUILTIN FROMSTRING fromString #-}
{-# DISPLAY Number.fromNat _ n = fromNat n #-}
{-# DISPLAY IsString.fromString _ s = fromString s #-}
{-# DISPLAY Negative.fromNeg _ n = fromNeg n #-}

instance
  Number-Nat : Number Nat
  Number-Nat .Number.Constraint _ = ⊤
  Number-Nat .Number.fromNat n = n

  IsString-String : IsString String
  IsString-String .IsString.Constraint _ = ⊤
  IsString-String .IsString.fromString s = s
```
