<!--
```agda
open import Prim.Type
open import Prim.Kan
```
-->

```agda
module Prim.Data.Maybe where
```

# Primitive: The Maybe type

The `Maybe`{.Agda} is the free pointed type on a given type. It is used
by Agda's primitives to represent failure.

```agda
data Maybe {a} (A : Type a) : Type a where
  just : A → Maybe A
  nothing : Maybe A

{-# BUILTIN MAYBE Maybe #-}
```
