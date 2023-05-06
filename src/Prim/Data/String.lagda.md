<!--
```agda
open import 1Lab.Type

open import Data.List

open import Prim.Data.Maybe
open import Prim.Literals
```
-->

```agda
module Prim.Data.String where
```

# Primitive: Characters and strings

We bind the big list of Agda primitives for interacting with characters
and strings.

```agda
postulate Char : Type
{-# BUILTIN CHAR Char #-}

primitive
  primIsLower primIsDigit primIsAlpha primIsSpace primIsAscii
    primIsLatin1 primIsPrint primIsHexDigit : Char → Bool
  primToUpper primToLower : Char → Char
  primCharToNat : Char → Nat
  primNatToChar : Nat → Char
  primCharEquality : Char → Char → Bool

primitive
  primStringUncons   : String → Maybe (Char × String)
  primStringToList   : String → List Char
  primStringFromList : List Char → String
  primStringAppend   : String → String → String
  primStringEquality : String → String → Bool
  primShowChar       : Char → String
  primShowString     : String → String
  primShowNat        : Nat → String
```
