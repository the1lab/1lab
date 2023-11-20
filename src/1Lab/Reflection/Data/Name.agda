open import 1Lab.Path.IdentitySystem
open import 1Lab.Path
open import 1Lab.Type

open import Data.Dec.Base
open import Data.Id.Base

open import Prim.Data.Word

open import 1Lab.Reflection.Data.Fixity

module 1Lab.Reflection.Data.Name where

postulate Name : Type
{-# BUILTIN QNAME Name #-}

primitive
  primQNameEquality           : Name → Name → Bool
  primQNameLess               : Name → Name → Bool
  primShowQName               : Name → String
  primQNameToWord64s          : Name → Σ Word64 (λ _ → Word64)
  primQNameToWord64sInjective : ∀ x y → primQNameToWord64s x ≡ᵢ primQNameToWord64s y → x ≡ᵢ y
  primQNameFixity             : Name → Fixity

instance
  Discrete-Name : Discrete Name
  Discrete-Name = Discrete-inj' _ (primQNameToWord64sInjective _ _)
