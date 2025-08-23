<!--
```agda
open import 1Lab.Type

open import Data.Dec.Base
open import Data.Nat.Base
open import Data.Id.Base
```
-->

```agda
module Data.Char.Base where
```

# The type of characters

```agda
postulate Char : Type
{-# BUILTIN CHAR Char #-}

private module P where primitive
  primIsLower primIsDigit primIsAlpha primIsSpace primIsAscii
    primIsLatin1 primIsPrint primIsHexDigit : Char → Bool

  primToUpper primToLower : Char → Char
  primCharToNat : Char → Nat
  primNatToChar : Nat → Char

  primCharToNatInjective : ∀ a b → primCharToNat a ≡ᵢ primCharToNat b → a ≡ᵢ b

open P public renaming
  ( primIsLower    to is-lower?
  ; primIsDigit    to is-digit?
  ; primIsAlpha    to is-alpha?
  ; primIsSpace    to is-space?
  ; primIsAscii    to is-ascii?
  ; primIsLatin1   to is-latin1?
  ; primIsPrint    to is-printable?
  ; primIsHexDigit to is-hex-digit?

  ; primToUpper    to to-upper
  ; primToLower    to to-lower
  ; primNatToChar  to nat→char
  ; primCharToNat  to char→nat
  )

instance
  Discrete-Char : Discrete Char
  Discrete-Char = Discrete-inj' _ (primCharToNatInjective _ _)
```
