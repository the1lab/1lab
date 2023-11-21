<!--
```agda
open import 1Lab.Type

open import Data.Dec.Base
open import Data.Nat.Base
open import Data.Id.Base
```
-->

```agda
module Data.Word.Base where
```

# Machine words

```agda
postulate Word64 : Type

{-# BUILTIN WORD64 Word64 #-}

private module P where primitive
  primWord64ToNat          : Word64 → Nat
  primWord64FromNat        : Nat → Word64
  primWord64ToNatInjective : ∀ a b → primWord64ToNat a ≡ᵢ primWord64ToNat b → a ≡ᵢ b

open P public renaming
  ( primWord64FromNat to nat→word64
  ; primWord64ToNat   to word64→nat
  )
  using ()

instance
  Discrete-Word64 : Discrete Word64
  Discrete-Word64 = Discrete-inj' _ (P.primWord64ToNatInjective _ _)
```
