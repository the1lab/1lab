-- This module doesn't have any text! That's because it's simply a bunch
-- of convenient re-exports for working outside of the 1Lab namespace.

module 1Lab.Prelude where

open import 1Lab.Type public

open import 1Lab.Path public
open import 1Lab.Path.Groupoid public

open import 1Lab.HLevel public
open import 1Lab.HLevel.Sets public
open import 1Lab.HLevel.Retracts public
open import 1Lab.HLevel.Universe public

open import 1Lab.Equiv public
open import 1Lab.Equiv.FromPath public
open import 1Lab.Equiv.Fibrewise public
open import 1Lab.Equiv.Embedding public
open import 1Lab.Equiv.HalfAdjoint public

open import 1Lab.Univalence public
open import 1Lab.Univalence.SIP public
open import 1Lab.Univalence.SIP.Auto
  using ( auto-str-term )
open import 1Lab.Univalence.SIP.Record public
open import 1Lab.Univalence.SIP.Record.Base public
  using ( record: ; _field[_by_] ; _axiom[_by_]
        ; record-desc
        )

open import 1Lab.Type.Pi public
open import 1Lab.Type.Dec public
open import 1Lab.Type.Sigma public

open import 1Lab.HIT.Truncation public

open import 1Lab.Reflection.Record
  using ( declare-record-iso ) public
