-- This module doesn't have any text! That's because it's simply a bunch
-- of convenient re-exports for working in the Cat namespace.

module Cat.Prelude where

open import 1Lab.Prelude
  hiding (_∘_ ; id)
  renaming (_↪_ to _↣_)
  public

open import Data.Set.Truncation public
open import Data.Set.Coequaliser public

open import Cat.Base public
open import Cat.Solver public
