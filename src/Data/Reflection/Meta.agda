open import 1Lab.Path
open import 1Lab.Type

open import Data.String.Base
open import Data.String.Show
open import Data.List.Base
open import Data.Dec.Base
open import Data.Nat.Base
open import Data.Id.Base
open import Data.Bool

module Data.Reflection.Meta where

postulate Meta : Type
{-# BUILTIN AGDAMETA Meta #-}

private module P where primitive
  primMetaEquality : Meta → Meta → Bool
  primMetaLess     : Meta → Meta → Bool
  primShowMeta     : Meta → String
  primMetaToNat    : Meta → Nat
  primMetaToNatInjective : ∀ x y → primMetaToNat x ≡ᵢ primMetaToNat y → x ≡ᵢ y

instance
  Discrete-Meta : Discrete Meta
  Discrete-Meta = Discrete-inj' _ (P.primMetaToNatInjective _ _)

  Show-Meta : Show Meta
  Show-Meta = default-show P.primShowMeta

data Blocker : Type where
  blocker-any  : List Blocker → Blocker
  blocker-all  : List Blocker → Blocker
  blocker-meta : Meta → Blocker

{-# BUILTIN AGDABLOCKER     Blocker #-}
{-# BUILTIN AGDABLOCKERANY  blocker-any #-}
{-# BUILTIN AGDABLOCKERALL  blocker-all #-}
{-# BUILTIN AGDABLOCKERMETA blocker-meta #-}
