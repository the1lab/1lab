<!--
```agda
open import 1Lab.Type
```
-->

```agda
module Prim.Data.Word where
```

# Primitive: Machine integers

```agda
postulate Word64 : Type
{-# BUILTIN WORD64 Word64 #-}

primitive
  primWord64ToNat   : Word64 → Nat
  primWord64FromNat : Nat → Word64
```
