open import Cat.Functor.Naturality
open import Cat.Functor.Bifunctor
open import Cat.Instances.Product
open import Cat.Functor.Base
open import Cat.Bi.Solver
open import Cat.Bi.Base
open import Cat.Prelude

import Cat.Bi.Reasoning as Br
import Cat.Reasoning as Cr

module Cat.Bi.Lax-functor.Hom {o h ℓ} (C : Prebicategory o h ℓ) where

open Br C
open Hom hiding (id)

open Functor
open _=>_

private
  module Cat = Prebicategory (Cat h ℓ)
  module Lf  = Lax-functor
  module Pf  = Pseudofunctor

module _ (X : Ob) where

  Hom-from-bi : Pseudofunctor C (Cat h ℓ)
  Hom-from-bi = pf module Hom-from-bi where
    compositor
      : ∀ {A B C}
      → Uncurry Cat.compose F∘ (compose {X} {B} {C} F× compose {X} {A} {B})
      => compose F∘ Uncurry compose
    compositor .η (f , g)              = ▶-assoc.from
    compositor .is-natural _ _ (α , β) = ext λ h →
         extendl (◀-assoc.to .is-natural _ _ _)
      ∙∙ cdr (◀-▶-comm.from .is-natural _ _ _) ∙∙ ◀.pulll refl

    lf : Lax-functor C (Cat h ℓ)
    lf .Lf.P₀            = Hom X
    lf .Lf.P₁            = compose
    lf .Lf.compositor    = compositor
    lf .Lf.unitor        = unitor-l.to
    lf .Lf.hexagon f g h = ext λ _ → bicat! C
    lf .Lf.right-unit f  = ext λ _ → bicat! C
    lf .Lf.left-unit f   = ext λ _ → bicat! C

    pf : Pseudofunctor _ _
    pf .Pf.lax              = lf
    pf .Pf.unitor-inv       = Cr.iso→invertible Cat[ _ , _ ] unitor-l
    pf .Pf.compositor-inv _ = Cr.iso→invertible Cat[ _ , _ ] (▶-assoc ni⁻¹)
