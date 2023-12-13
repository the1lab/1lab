```agda
module Data.Nat where

open import Data.Nat.Properties public
open import Data.Nat.Order public
open import Data.Nat.Base public
open import Data.Nat.Divisible public
open import Data.Nat.Divisible.GCD public
open import Data.Nat.DivMod public
open import Prim.Data.Nat
  using (Nat ; _+_ ; _-_) public
```

# Natural numbers - index

The natural numbers are constructed in the module
[`Data.Nat.Base`]. Their arithmetical properties are proved in
[`Data.Nat.Properties`].

[`Data.Nat.Base`]: Data.Nat.Base.html
[`Data.Nat.Properties`]: Data.Nat.Properties.html
