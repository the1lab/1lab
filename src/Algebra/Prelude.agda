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

open import Cat.Diagram.Coequaliser public
open import Cat.Diagram.Coproduct public
open import Cat.Diagram.Equaliser public
open import Cat.Diagram.Pullback public
open import Cat.Diagram.Terminal public
open import Cat.Diagram.Initial public
open import Cat.Diagram.Pushout public
open import Cat.Diagram.Product public
open import Cat.Diagram.Image public
open import Cat.Diagram.Zero public

import Cat.Reasoning

open import Cat.Displayed.Univalence.Thin public

module Cat {o ℓ} (C : Precategory o ℓ) where
  open Cat.Reasoning C public
