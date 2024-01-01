-- This module doesn't have any text! That's because it's simply a bunch
-- of convenient re-exports for working outside of the 1Lab namespace.

module 1Lab.Prelude where

open import 1Lab.Type public

open import 1Lab.Path public
open import 1Lab.Path.Groupoid public

open import 1Lab.Path.IdentitySystem public
open import 1Lab.Path.IdentitySystem.Interface public

open import Meta.Append public
open import Meta.Idiom public
open import Meta.Bind public
open import Meta.Alt public

open import 1Lab.HLevel public
open import 1Lab.HLevel.Retracts public
open import 1Lab.HLevel.Universe public

open import 1Lab.Equiv public
open import 1Lab.Equiv.FromPath public
open import 1Lab.Equiv.Fibrewise public
open import 1Lab.Function.Embedding public
open import 1Lab.Function.Reasoning public
open import 1Lab.Equiv.HalfAdjoint public

open import 1Lab.Function.Surjection public

open import 1Lab.Univalence public
open import 1Lab.Univalence.SIP public

open import 1Lab.Type.Pi public
open import 1Lab.Type.Sigma public
open import 1Lab.Type.Pointed public

open import 1Lab.HIT.Truncation public

open import 1Lab.Reflection.Marker public
open import 1Lab.Reflection.Record
  using ( declare-record-iso ) public
open import 1Lab.Reflection.HLevel public
open import 1Lab.Reflection.Regularity public

open import 1Lab.Resizing public

open import 1Lab.Underlying public
open import 1Lab.Extensionality public

open import Data.Id.Base public
