open import Cat.Functor.Bifunctor.Duality
open import Cat.Bi.Lax-functor.Base
open import Cat.Functor.Bifunctor
open import Cat.Instances.Product
open import Cat.Functor.Constant
open import Cat.Bi.Lax-transfor
open import Cat.Bi.Modification
open import Cat.Bi.Duality
open import Cat.Bi.Solver
open import Cat.Bi.Base
open import Cat.Prelude

import Cat.Bi.Reasoning as Br
import Cat.Reasoning as Cr

module Cat.Bi.Lax-functor.Constant where

private
  variable
    o o' h h' ℓ ℓ' : Level
    B C : Prebicategory o h ℓ

  module Pf = Pseudofunctor
  module Lf = Lax-functor

open Cr.is-invertible
open Lax-transfor
open Modification
open Cr.Inverses
open Functor
open _=>_

module _ (C : Prebicategory o h ℓ) (X : Prebicategory.Ob C) where
  open Prebicategory C
  private module CH {A} {B} = Cr (Hom A B)

  Constᵖ : Pseudofunctor B C
  Constᵖ .Pf.lax .Lf.P₀ _                         = X
  Constᵖ .Pf.lax .Lf.P₁                           = Const id
  Constᵖ .Pf.lax .Lf.compositor .η _              = λ← id
  Constᵖ .Pf.lax .Lf.compositor .is-natural _ _ _ =
    CH.cdr (compose.◆-id) ∙ CH.id-comm
  Constᵖ .Pf.lax .Lf.unitor        = Hom.id
  Constᵖ .Pf.lax .Lf.hexagon f g h = bicat! C
  Constᵖ .Pf.lax .Lf.right-unit f  = bicat! C
  Constᵖ .Pf.lax .Lf.left-unit f   = bicat! C
  Constᵖ .Pf.unitor-inv            = CH.id-invertible
  Constᵖ .Pf.compositor-inv _      = CH.iso→invertible (Br.λ≅ C CH.Iso⁻¹)

Const-pseudoₒ : Pseudofunctor C (Pseudoₒ B C)
Const-pseudoₒ {C = C} {B = B} = pf module Const-pseudoₒ where
  open Prebicategory C
  private module CH {A} {B} = Cr (Hom A B)
  Const₁ : ∀ {X Y} → Functor (Hom X Y) Pseudoₒ[ Constᵖ C X {B = B} , Constᵖ C Y ]
  Const₁ .F₀ f .σ A                         = f
  Const₁ .F₀ f .naturator .η _              = λ→ _ ∘ ρ← _
  Const₁ .F₀ f .naturator .is-natural _ _ _ = bicat! C
  Const₁ .F₀ f .ν-compositor g h            = bicat! C
  Const₁ .F₀ f .ν-unitor                    = bicat! C
  Const₁ .F₁ α .Γ a                         = α
  Const₁ .F₁ α .is-natural                  = bicat! C
  Const₁ .F-id                              = ext λ _ → refl
  Const₁ .F-∘ f g                           = ext λ _ → refl

  compositor
    : ∀ {X Y Z}
    → Uncurry (bop (Lax.compose (B ^co) (C ^co))) F∘ (Const₁ {Y} {Z} F× Const₁ {X} {Y})
    => Const₁ F∘ Uncurry compose
  compositor .η _ .Γ _               = CH.id
  compositor .η (x , y) .is-natural  = bicat! C
  compositor .is-natural _ _ (f , g) = ext λ _ → CH.idl _
    ∙∙ ap₂ _∘_  (CH.eliml compose.▶.F-id) (CH.elimr compose.◀.F-id)
    ∙∙ sym (CH.idr _)

  compositor-inv
    : ∀ {X Y Z} fg
    → Cr.is-invertible Pseudoₒ[ _ , _ ] (compositor {X} {Y} {Z} .η fg)
  compositor-inv (f , g) .inv .Γ _        = Hom.id
  compositor-inv (f , g) .inv .is-natural = bicat! C
  compositor-inv (f , g) .inverses .invl  = ext λ _ → Hom.idl _
  compositor-inv (f , g) .inverses .invr  = ext λ _ → Hom.idr _

  unitor : ∀ {X} → Modification (Const₁ .F₀ (id {X})) idlx
  unitor .Γ _        = Hom.id
  unitor .is-natural = bicat! C

  unitor-inv : ∀ {X} → Cr.is-invertible Pseudoₒ[ _ , _ ] (unitor {X})
  unitor-inv .inv .Γ _        = Hom.id
  unitor-inv .inv .is-natural = bicat! C
  unitor-inv .inverses .invl  = ext λ _ → Hom.idl _
  unitor-inv .inverses .invr  = ext λ _ → Hom.idr _

  lf : Lax-functor C (Pseudoₒ B C)
  lf .Lf.P₀ X          = co (Constᵖ C X)
  lf .Lf.P₁            = Const₁
  lf .Lf.compositor    = compositor
  lf .Lf.unitor        = unitor
  lf .Lf.hexagon f g h = ext λ _ →
      CH.elimr   (CH.idl _ ∙∙ CH.eliml compose.▶.F-id ∙∙ compose.◀.F-id)
    ∙ CH.insertl (CH.idl _ ∙∙ CH.eliml compose.▶.F-id ∙∙ compose.◀.F-id)
  lf .Lf.right-unit f = ext λ _ →
    CH.elimr (Hom.idl _ ∙∙ CH.eliml compose.▶.F-id ∙∙ compose.◀.F-id)
  lf .Lf.left-unit f = ext λ _ →
    CH.elimr (Hom.idl _ ∙∙ CH.eliml compose.▶.F-id ∙∙ compose.◀.F-id)

  pf : Pseudofunctor _ _
  pf .Pf.lax            = lf
  pf .Pf.unitor-inv     = unitor-inv
  pf .Pf.compositor-inv = compositor-inv
