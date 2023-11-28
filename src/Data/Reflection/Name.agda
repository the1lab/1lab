open import 1Lab.Path.IdentitySystem
open import 1Lab.Path
open import 1Lab.Type

open import Data.Reflection.Fixity
open import Data.String.Base
open import Data.String.Show
open import Data.Word.Base
open import Data.Dec.Base
open import Data.Id.Base

module Data.Reflection.Name where

postulate Name : Type
{-# BUILTIN QNAME Name #-}

private module P where primitive
  primQNameEquality           : Name → Name → Bool
  primQNameLess               : Name → Name → Bool
  primShowQName               : Name → String
  primQNameToWord64s          : Name → Σ Word64 (λ _ → Word64)
  primQNameToWord64sInjective : ∀ x y → primQNameToWord64s x ≡ᵢ primQNameToWord64s y → x ≡ᵢ y
  primQNameFixity             : Name → Fixity

open P
  renaming (primQNameFixity to name→fixity)
  using ()
  public

instance
  Discrete-Name : Discrete Name
  Discrete-Name = Discrete-inj' _ (P.primQNameToWord64sInjective _ _)

  Show-Name : Show Name
  Show-Name = default-show P.primShowQName
