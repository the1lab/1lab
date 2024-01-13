open import 1Lab.Type

open import Data.Reflection.Name
open import Data.Reflection.Term
open import Data.String.Base
open import Data.List.Base

open import Meta.Append

module Data.Reflection.Error where

data ErrorPart : Type where
  strErr  : String  → ErrorPart
  termErr : Term    → ErrorPart
  pattErr : Pattern → ErrorPart
  nameErr : Name    → ErrorPart

{-# BUILTIN AGDAERRORPART       ErrorPart #-}
{-# BUILTIN AGDAERRORPARTSTRING strErr    #-}
{-# BUILTIN AGDAERRORPARTTERM   termErr   #-}
{-# BUILTIN AGDAERRORPARTPATT   pattErr   #-}
{-# BUILTIN AGDAERRORPARTNAME   nameErr   #-}

instance
  From-string-ErrorPart : From-string ErrorPart
  From-string-ErrorPart .From-string.Constraint _ = ⊤
  From-string-ErrorPart .from-string s = strErr s

instance
  From-string-error : From-string (List ErrorPart)
  From-string-error .From-string.Constraint _   = ⊤
  From-string-error .from-string s              = strErr s ∷ []
