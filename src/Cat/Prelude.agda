-- This module doesn't have any text! That's because it's simply a bunch
-- of convenient re-exports for working in the Cat namespace.

module Cat.Prelude where

open import 1Lab.Prelude
  renaming ( _↪_ to _↣_
           ; _∘_ to _⊙_ -- \o.
           )
  hiding (id)
  public

open import Data.Set.Truncation public
open import Data.Set.Coequaliser public

open import Cat.Base public
open import Cat.Solver public
open import Cat.Univalent
  using ( is-category )
  public
