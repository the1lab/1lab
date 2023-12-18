open import 1Lab.Path.IdentitySystem
open import 1Lab.Path
open import 1Lab.Type

open import Data.String.Base
open import Data.Dec.Base
open import Data.Id.Base

module Data.Reflection.Abs where

record Abs {a} (A : Type a) : Type a where
  constructor abs
  field
    abs-name : String
    abs-binder : A

{-# BUILTIN ABS    Abs #-}
{-# BUILTIN ABSABS abs #-}

instance
  Discrete-Abs : ∀ {ℓ} {A : Type ℓ} ⦃ _ : Discrete A ⦄ → Discrete (Abs A)
  Discrete-Abs = Discrete-inj (λ (abs n b) → n , b) (λ p → ap₂ abs (ap fst p) (ap snd p)) auto
