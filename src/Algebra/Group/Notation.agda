open import 1Lab.Prelude hiding (_+_ ; _*_)

open import Algebra.Group.Ab
open import Algebra.Group

module Algebra.Group.Notation where

module Additive-notation = Group-on renaming
  ( _⋆_         to infixl 20 _+_
  ; _⁻¹         to infixr 30 -_
  ; unit        to 0g
  ; associative to +-assoc
  ; inverser    to +-invr
  ; inversel    to +-invl
  ; idl         to +-idl
  ; idr         to +-idr
  ; inv-inv     to neg-neg
  ; inv-comm    to neg-comm
  ; inv-unit    to neg-0
  )
  hiding (magma-hlevel)

module Multiplicative-notation = Group-on renaming
  ( _⋆_         to infixl 20 _*_
  ; _⁻¹         to infixl 30 _⁻¹
  ; unit        to 1g
  ; associative to *-assoc
  ; inverser    to *-invr
  ; inversel    to *-invl
  ; idl         to *-idl
  ; idr         to *-idr
  ; inv-unit    to inv-1
  )
  hiding (magma-hlevel)

instance
  Abelian-group-on→Group-on
    : ∀ {ℓ} {T : Type ℓ} ⦃ A : Abelian-group-on T ⦄
    → Group-on T
  Abelian-group-on→Group-on ⦃ A ⦄ = record {
    has-is-group = is-abelian-group.has-is-group (A .Abelian-group-on.has-is-ab) }
