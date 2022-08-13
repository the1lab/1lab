```agda
open import 1Lab.Prim.Extension
open import 1Lab.Prim.Interval
open import 1Lab.Prim.Type
open import 1Lab.Prim.Kan

module 1Lab.Prim.Data.Bool where
```

# Primitive: Booleans

The [booleans](Data.Bool.html) are the h-initial type with two inhabitants.

```agda
data Bool : Type where
  true false : Bool
{-# BUILTIN BOOL Bool #-}

{-# BUILTIN FALSE false #-}
{-# BUILTIN TRUE true #-}
```
