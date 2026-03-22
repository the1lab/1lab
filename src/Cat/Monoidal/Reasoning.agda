open import Cat.Functor.Naturality
open import Cat.Functor.Bifunctor
open import Cat.Monoidal.Base
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Functor.Reasoning
import Cat.Bi.Reasoning
import Cat.Reasoning

open _=>_

module Cat.Monoidal.Reasoning {o ℓ} {C : Precategory o ℓ} (Cᵐ : Monoidal-category C) where

open Cat.Reasoning C public
open Monoidal Cᵐ public

open Cat.Bi.Reasoning (Deloop Cᵐ)
  using
    ( ▶-assoc ; ◀-assoc ; ◀-▶-comm
    ; module λ≅ ; module ρ≅ ; module α≅
    ; λ←nat
    ; λ→nat
    ; ρ←nat
    ; ρ→nat
    ; α←nat
    ; α→nat
    )
  public
