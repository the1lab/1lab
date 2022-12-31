module Algebra.Prelude where

open import Cat.Instances.Shape.Terminal public
open import Cat.Functor.FullSubcategory public
open import Cat.Instances.Product public
open import Cat.Instances.Functor public
open import Cat.Instances.Comma public
open import Cat.Instances.Slice public
open import Cat.Functor.Adjoint public
open import Cat.Functor.Base public
open import Cat.Functor.Hom public
open import Cat.Univalent public
open import Cat.Prelude hiding (_+_ ; _-_ ; _*_) public

import Cat.Diagram.Coequaliser
import Cat.Diagram.Coproduct
import Cat.Diagram.Equaliser
import Cat.Diagram.Pullback
import Cat.Diagram.Terminal
import Cat.Diagram.Initial
import Cat.Diagram.Pushout
import Cat.Diagram.Product
import Cat.Diagram.Image
import Cat.Diagram.Zero
import Cat.Reasoning

open import Cat.Displayed.Univalence.Thin public

module Cat {o ℓ} (C : Precategory o ℓ) where
  open Cat.Diagram.Coequaliser C public
  open Cat.Diagram.Coproduct C public
  open Cat.Diagram.Equaliser C public
  open Cat.Diagram.Pullback C public
  open Cat.Diagram.Terminal C public
  open Cat.Diagram.Initial C public
  open Cat.Diagram.Pushout C public
  open Cat.Diagram.Product C public
  open Cat.Diagram.Image C public
  open Cat.Diagram.Zero C public
  open Cat.Reasoning C public
