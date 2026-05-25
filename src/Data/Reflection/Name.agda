open import 1Lab.Path.IdentitySystem
open import 1Lab.Path
open import 1Lab.Type

open import Data.Reflection.Fixity
open import Data.String.Base
open import Data.String.Show
open import Data.Dec.Base
open import Data.Id.Base

module Data.Reflection.Name where

postulate Name : Type
{-# BUILTIN QNAME Name #-}

private module P where
  primitive
    primQNameEquality           : Name → Name → Bool
    primQNameLess               : Name → Name → Bool
    primShowQName               : Name → String
    primQNameFixity             : Name → Fixity
  postulate
    primQNameEqualityRefl  : ∀ x → primQNameEquality x x ≡ᵢ true
    primQNameEqualitySound : ∀ x y → primQNameEquality x y ≡ᵢ true → x ≡ᵢ y

open P
  renaming (primQNameFixity to name→fixity)
  using ()
  public

instance
  Discrete-Name : Discrete Name
  Discrete-Name .decide x y with P.primQNameEquality x y in q
  ... | true  = yes (Id≃path.to (P.primQNameEqualitySound x y q))
  ... | false = no λ p → work (Id≃path.from p) q where
    work : ∀ {x y} → x ≡ᵢ y → P.primQNameEquality x y ≡ᵢ false → ⊥
    work {x} reflᵢ p rewrite P.primQNameEqualityRefl x with () ← p

  Show-Name : Show Name
  Show-Name = default-show P.primShowQName
