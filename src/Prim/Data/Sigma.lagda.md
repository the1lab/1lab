<!--
```agda
open import Prim.Extension
open import Prim.Interval
open import Prim.Type
open import Prim.Kan
```
-->

```agda
module Prim.Data.Sigma where
```

# Primitives: Sigma types

The dependent sum type, total space, or type of dependent pairs, is
defined as a record, so that it enjoys definitional η.

```agda
record Σ {ℓ ℓ′} (A : Type ℓ) (B : A → Type ℓ′) : Type (ℓ ⊔ ℓ′) where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ public

{-# BUILTIN SIGMA Σ #-}

syntax Σ A (λ x → B) = Σ[ x ∈ A ] B

infixr 4 _,_
infix 5 Σ
```

Similarly, for the unit type:

```agda
record ⊤ : Type where
  instance constructor tt
{-# BUILTIN UNIT ⊤ #-}
```
