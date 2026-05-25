<!--
```agda
open import 1Lab.Type

open import Data.Maybe.Base
open import Data.Dec.Base
open import Data.Int.Base
open import Data.Id.Base
```
-->

```agda
module Data.Float.Base where
```

# header

```agda
postulate Float : Type
{-# BUILTIN FLOAT Float #-}

private module P where primitive
  -- Relations
  primFloatInequality        : Float → Float → Bool
  primFloatEquality          : Float → Float → Bool
  primFloatLess              : Float → Float → Bool
  primFloatIsInfinite        : Float → Bool
  primFloatIsNaN             : Float → Bool
  primFloatIsNegativeZero    : Float → Bool
  primFloatIsSafeInteger     : Float → Bool
  -- Conversions
  primNatToFloat             : Nat → Float
  primIntToFloat             : Int → Float
  primFloatRound             : Float → Maybe Int
  primFloatFloor             : Float → Maybe Int
  primFloatCeiling           : Float → Maybe Int
  primFloatToRatio           : Float → (Σ Int λ _ → Int)
  primRatioToFloat           : Int → Int → Float
  primFloatDecode            : Float → Maybe (Σ Int λ _ → Int)
  primFloatEncode            : Int → Int → Maybe Float
  -- Operations
  primFloatPlus              : Float → Float → Float
  primFloatMinus             : Float → Float → Float
  primFloatTimes             : Float → Float → Float
  primFloatDiv               : Float → Float → Float
  primFloatPow               : Float → Float → Float
  primFloatNegate            : Float → Float
  primFloatSqrt              : Float → Float
  primFloatExp               : Float → Float
  primFloatLog               : Float → Float
  primFloatSin               : Float → Float
  primFloatCos               : Float → Float
  primFloatTan               : Float → Float
  primFloatASin              : Float → Float
  primFloatACos              : Float → Float
  primFloatATan              : Float → Float
  primFloatATan2             : Float → Float → Float
  primFloatSinh              : Float → Float
  primFloatCosh              : Float → Float
  primFloatTanh              : Float → Float
  primFloatASinh             : Float → Float
  primFloatACosh             : Float → Float
  primFloatATanh             : Float → Float

open P public renaming
  ( primFloatInequality to _float≠_
  ; primFloatEquality   to _float=_
  ; primFloatLess       to _float<_

  ; primFloatIsInfinite     to is-infinite?
  ; primFloatIsNaN          to is-nan?
  ; primFloatIsNegativeZero to is-neg0?
  ; primFloatIsSafeInteger  to is-integer?

  ; primNatToFloat          to nat→float
  ; primIntToFloat          to int→float
  ; primFloatRound          to round
  ; primFloatFloor          to floor
  ; primFloatCeiling        to ceiling
  ; primFloatToRatio        to float→ratio
  ; primRatioToFloat        to ratio→float

  ; primFloatDecode         to decode-float
  ; primFloatEncode         to encode-float

  ; primFloatPlus           to _+,_
  ; primFloatMinus          to _-,_
  ; primFloatTimes          to _*,_
  ; primFloatDiv            to _/,_
  )
  using ()

-- TODO: this needs to be a primitive upstream.
private postulate primFloatToRatioInjective : ∀ a b → float→ratio a ≡ᵢ float→ratio b → a ≡ᵢ b

instance
  Discrete-Float : Discrete Float
  Discrete-Float  = Discrete-inj' _ (primFloatToRatioInjective _ _)

  Number-Float : Number Float
  Number-Float .Number.Constraint _ = ⊤
  Number-Float .Number.fromNat s = nat→float s
```
