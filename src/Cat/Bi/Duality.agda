open import Cat.Functor.Bifunctor.Duality
open import Cat.Functor.Naturality
open import Cat.Functor.Bifunctor
open import Cat.Bi.Lax-functor
open import Cat.Bi.Base
open import Cat.Prelude renaming (_^op to _^opᶜ)

import Cat.Bi.Reasoning as Br
import Cat.Reasoning as Cr

module Cat.Bi.Duality where

private
  module Pb = Prebicategory
  variable
    o o' h h' ℓ ℓ' : Level

open Cr.is-invertible hiding (op)
open Pseudofunctor
open Cr.Inverses
open Lax-functor
open Functor
open Cr._≅_
open _=>_ hiding (op)

module _ (C : Prebicategory o h ℓ) where
  open Prebicategory C
  private
    module C  = Br C
    module CH = C.Hom

  infixl 60 _^op
  {-# TERMINATING #-}
  _^op : Prebicategory o h ℓ
  _^op .Pb.Ob      = Ob
  _^op .Pb.Hom x y = Hom y x
  _^op .Pb.id      = id
  _^op .Pb.compose = Flip compose
  _^op .Pb.unitor-l = to-natural-iso ni where
    ni : make-natural-iso _ _
    ni .make-natural-iso.eta           = ρ→
    ni .make-natural-iso.inv           = ρ←
    ni .make-natural-iso.eta∘inv _     = C.ρ≅ .invl
    ni .make-natural-iso.inv∘eta _     = C.ρ≅ .invr
    ni .make-natural-iso.natural _ _ _ = sym $ ρ→nat _
  _^op .Pb.unitor-r = to-natural-iso ni where
    ni : make-natural-iso _ _
    ni .make-natural-iso.eta           = λ→
    ni .make-natural-iso.inv           = λ←
    ni .make-natural-iso.eta∘inv _     = C.λ≅ .invl
    ni .make-natural-iso.inv∘eta _     = C.λ≅ .invr
    ni .make-natural-iso.natural _ _ _ = sym $ λ→nat _
  _^op .Pb.associator = to-natural-iso ni where
    ni : make-natural-iso _ _
    ni .make-natural-iso.eta _         = α← _
    ni .make-natural-iso.inv _         = α→ _
    ni .make-natural-iso.eta∘inv _     = C.α≅ .invr
    ni .make-natural-iso.inv∘eta _     = C.α≅ .invl
    ni .make-natural-iso.natural _ _ _ =
         CH.car (CH.cdr (ap (C._◀ _) (compose.rlmap _ _)) ∙ compose.rlmap _ _)
      ∙∙ sym (α←nat _ _ _)
      ∙∙ CH.cdr (CH.cdr (ap (_ C.▶_) (compose.lrmap _ _)) ∙ compose.lrmap _ _)
  _^op .Pb.triangle f g     = C.triangle-α→
  _^op .Pb.pentagon f g h i = C.pentagon-α→

  infixl 60 _^co
  _^co : Prebicategory o h ℓ
  _^co .Pb.Ob       = Ob
  _^co .Pb.Hom x y  = Hom x y ^opᶜ
  _^co .Pb.id       = id
  _^co .Pb.compose  = bop compose
  _^co .Pb.unitor-l = to-natural-iso ni where
    ni : make-natural-iso _ _
    ni .make-natural-iso.eta           = λ←
    ni .make-natural-iso.inv           = λ→
    ni .make-natural-iso.eta∘inv _     = C.λ≅ .invl
    ni .make-natural-iso.inv∘eta _     = C.λ≅ .invr
    ni .make-natural-iso.natural _ _ _ = λ←nat _
  _^co .Pb.unitor-r = to-natural-iso ni where
    ni : make-natural-iso _ _
    ni .make-natural-iso.eta           = ρ←
    ni .make-natural-iso.inv           = ρ→
    ni .make-natural-iso.eta∘inv _     = C.ρ≅ .invl
    ni .make-natural-iso.inv∘eta _     = C.ρ≅ .invr
    ni .make-natural-iso.natural _ _ _ = ρ←nat _
  _^co .Pb.associator = to-natural-iso ni where
    ni : make-natural-iso _ _
    ni .make-natural-iso.eta           = α←
    ni .make-natural-iso.inv           = α→
    ni .make-natural-iso.eta∘inv _     = C.α≅ .invl
    ni .make-natural-iso.inv∘eta _     = C.α≅ .invr
    ni .make-natural-iso.natural _ _ _ =
         CH.cdr (CH.car (ap (_ C.▶_) (compose.rlmap _ _)) ∙ compose.rlmap _ _)
      ∙∙ α←nat _ _ _
      ∙∙ CH.car (CH.car (ap (C._◀ _) (compose.lrmap _ _)) ∙ compose.lrmap _ _)
  _^co .Pb.triangle f g     = C.Hom.lswizzle (sym C.triangle-inv) (C.α≅ .invl)
  _^co .Pb.pentagon _ _ _ _ = sym (Hom.assoc _ _ _) ∙ C.pentagon-α→


Oplax-functor : Prebicategory o h ℓ → Prebicategory o' h' ℓ' → Type _
Oplax-functor B C = Lax-functor (B ^co) (C ^co)

module _
  {B : Prebicategory o h ℓ} {C : Prebicategory o' h' ℓ'} (F : Pseudofunctor B C)
  where
  private
    module B = Br B
    module C = Br C
    module F = Pf-reasoning F

    open C.Hom

  co : Pseudofunctor (B ^co) (C ^co)
  co .lax .P₀                           = F.P₀
  co .lax .P₁                           = F.P₁.op
  co .lax .compositor .η                = F.γ←
  co .lax .compositor .is-natural _ _ _ = car (C.compose.rlmap _ _)
    ∙∙ sym (F.γ←nat _ _)
    ∙∙ cdr F.P₁.⟨ B.compose.lrmap _ _ ⟩
  co .lax .unitor                       = F.υ←
  co .lax .hexagon f g h = inverse-unique refl refl
    (F.P₁.F-map-iso B.α≅ ∘Iso F.γ≅ ∘Iso C.◀.F-map-iso F.γ≅)
    (F.γ≅ ∘Iso C.▶.F-map-iso F.γ≅ ∘Iso C.α≅)
    (F.hexagon f g h)
  co .lax .right-unit f = inverse-unique refl refl
    (F.P₁.F-map-iso B.ρ≅ Iso⁻¹ ∘Iso F.γ≅ ∘Iso C.▶.F-map-iso F.υ≅)
    (C.ρ≅ Iso⁻¹) (F.right-unit f)
  co .lax .left-unit f  = inverse-unique refl refl
    (F.P₁.F-map-iso B.λ≅ Iso⁻¹ ∘Iso F.γ≅ ∘Iso C.◀.F-map-iso F.υ≅)
    (C.λ≅ Iso⁻¹) (F.left-unit f)
  co .unitor-inv .inv                   = F.υ→
  co .unitor-inv .inverses .invl        = F.unitor-inv .inverses .invl
  co .unitor-inv .inverses .invr        = F.unitor-inv .inverses .invr
  co .compositor-inv fg .inv            = F.γ→ fg
  co .compositor-inv fg .inverses .invl = F.compositor-inv fg .inverses .invl
  co .compositor-inv fg .inverses .invr = F.compositor-inv fg .inverses .invr
