open import 1Lab.Path
open import 1Lab.Type

open import Data.List.Base
open import Data.Dec.Base
open import Data.Nat.Base
open import Data.Id.Base
open import Data.Bool

open import Prim.Data.String

module 1Lab.Reflection.Data.Meta where

postulate Meta : Type
{-# BUILTIN AGDAMETA Meta #-}

primitive
  primMetaEquality : Meta → Meta → Bool
  primMetaLess     : Meta → Meta → Bool
  primShowMeta     : Meta → String
  primMetaToNat    : Meta → Nat
  primMetaToNatInjective : ∀ x y → primMetaToNat x ≡ᵢ primMetaToNat y → x ≡ᵢ y

instance
  Discrete-Meta : Discrete Meta
  Discrete-Meta = Discrete-inj' _ (primMetaToNatInjective _ _)

data Blocker : Type where
  blockerAny  : List Blocker → Blocker
  blockerAll  : List Blocker → Blocker
  blockerMeta : Meta → Blocker

{-# BUILTIN AGDABLOCKER     Blocker #-}
{-# BUILTIN AGDABLOCKERANY  blockerAny #-}
{-# BUILTIN AGDABLOCKERALL  blockerAll #-}
{-# BUILTIN AGDABLOCKERMETA blockerMeta #-}
