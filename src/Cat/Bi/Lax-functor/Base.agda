open import Cat.Functor.Naturality
open import Cat.Functor.Bifunctor
open import Cat.Instances.Product
open import Cat.Bi.Lax-transfor
open import Cat.Bi.Modification
open import Cat.Bi.Duality hiding (_^op)
open import Cat.Bi.Solver
open import Cat.Bi.Base
open import Cat.Prelude

import Cat.Bi.Reasoning as Br
import Cat.Reasoning as Cr

module Cat.Bi.Lax-functor.Base where

open Pseudofunctor
open Cr.Inverses
open Functor
open Cr._≅_
open _=>_

private
  module Pc = Precategory
  module Pb = Prebicategory
  variable
    o o' h h' ℓ ℓ' : Level
    B C : Prebicategory o h ℓ

Laxₗ[_,_] : Lax-functor B C → Lax-functor B C → Precategory _ _
Laxₗ[_,_] F G .Pc.Ob                  = F =>ₗ G
Laxₗ[_,_] F G .Pc.Hom                 = Modification
Laxₗ[_,_] F G .Pc.Hom-set _ _         = Mod-is-set
Laxₗ[_,_] F G .Pc.id                  = idmd
Laxₗ[_,_] F G .Pc._∘_                 = _∘md_
Laxₗ[_,_] {C = C} F G .Pc.idr _       = ext λ _ → Pb.Hom.idr C _
Laxₗ[_,_] {C = C} F G .Pc.idl _       = ext λ _ → Pb.Hom.idl C _
Laxₗ[_,_] {C = C} F G .Pc.assoc _ _ _ = ext λ _ → Pb.Hom.assoc C _ _ _

Laxₒ[_,_] : Oplax-functor B C → Oplax-functor B C → Precategory _ _
Laxₒ[ F , G ] = Laxₗ[ F , G ] ^op

Pseudoₗ[_,_] : Pseudofunctor B C → Pseudofunctor B C → Precategory _ _
Pseudoₗ[ F , G ] = Laxₗ[ F .lax , G .lax ]

Pseudoₒ[_,_] : Pseudofunctor B C → Pseudofunctor B C → Precategory _ _
Pseudoₒ[ F , G ] = Laxₒ[ co F .lax , co G .lax ]

Laxₗ : Prebicategory o h ℓ → Prebicategory o' h' ℓ' → Prebicategory _ _ _
Laxₗ B C = pb module Lax where
  private
    module C  = Br C
    module CH = C.Hom
  open Make-bifunctor
  open Lax-transfor
  open Modification
  compose
    : {F G H : Lax-functor B C}
    → Bifunctor Laxₗ[ G , H ] Laxₗ[ F , G ] Laxₗ[ F , H ]
  compose = make-bifunctor mk where
    mk : Make-bifunctor
    mk .F₀ α β     = α ∘lx β
    mk .lmap f     = f ◆md idmd
    mk .rmap g     = idmd ◆md g
    mk .lmap-id    = ext λ _ → C.compose.◆-id
    mk .rmap-id    = ext λ _ → C.compose.◆-id
    mk .lmap-∘ f g = ext λ _ → CH.pushl C.◀-distribl ∙ CH.car (CH.intror C.▶.F-id)
    mk .rmap-∘ f g = ext λ _ → CH.pushr C.▶-distribr ∙ CH.cdr (CH.introl C.◀.F-id)
    mk .lrmap f g  = ext λ _ →
         ap₂ C._∘_ (sym (C.compose.lmap-◆ _)) (sym (C.compose.rmap-◆ _))
      ∙∙ C.compose.lrmap _ _
      ∙∙ ap₂ C._∘_ (C.compose.rmap-◆ _) (C.compose.lmap-◆ _)

  unitor-l : ∀ {F G} → Id ≅ⁿ Bifunctor.Right (compose {F = F} {G}) idlx
  unitor-l = to-natural-iso ni where
    ni : make-natural-iso _ _
    ni .make-natural-iso.eta x .Γ a        = C.λ→ (σ x a)
    ni .make-natural-iso.eta x .is-natural = bicat! C
    ni .make-natural-iso.inv x .Γ a        = C.λ← (σ x a)
    ni .make-natural-iso.inv x .is-natural = bicat! C
    ni .make-natural-iso.eta∘inv x         = ext λ _ → C.λ≅ .invl
    ni .make-natural-iso.inv∘eta x         = ext λ _ → C.λ≅ .invr
    ni .make-natural-iso.natural _ _ _     = ext λ _ →
      CH.car (sym (C.compose.rmap-◆ _)) ∙ sym (C.λ→nat _)

  unitor-r : ∀ {F G} → Id ≅ⁿ Bifunctor.Left (compose {G = F} {G}) idlx
  unitor-r = to-natural-iso ni where
    ni : make-natural-iso _ _
    ni .make-natural-iso.eta x .Γ a        = C.ρ→ (σ x a)
    ni .make-natural-iso.eta x .is-natural = bicat! C
    ni .make-natural-iso.inv x .Γ a        = C.ρ← (σ x a)
    ni .make-natural-iso.inv x .is-natural = bicat! C
    ni .make-natural-iso.eta∘inv x         = ext λ _ → C.ρ≅ .invl
    ni .make-natural-iso.inv∘eta x         = ext λ _ → C.ρ≅ .invr
    ni .make-natural-iso.natural _ _ _     = ext λ _ →
      CH.car (sym (C.compose.lmap-◆ _)) ∙ sym (C.ρ→nat _)

  associator : Associator-for Laxₗ[_,_] compose
  associator = to-natural-iso ni where
    ni : make-natural-iso _ _
    ni .make-natural-iso.eta x .Γ a        = C.α→ _
    ni .make-natural-iso.eta x .is-natural = bicat! C
    ni .make-natural-iso.inv x .Γ a        = C.α← _
    ni .make-natural-iso.inv x .is-natural = bicat! C
    ni .make-natural-iso.eta∘inv x         = ext λ _ → C.α≅ .invl
    ni .make-natural-iso.inv∘eta x         = ext λ _ → C.α≅ .invr
    ni .make-natural-iso.natural _ _ _     = ext λ _ → bicat! C

  pb : Prebicategory _ _ _
  pb .Pb.Ob               = Lax-functor B C
  pb .Pb.Hom              = Laxₗ[_,_]
  pb .Pb.id               = idlx
  pb .Pb.compose          = compose
  pb .Pb.unitor-l         = unitor-l
  pb .Pb.unitor-r         = unitor-r
  pb .Pb.associator       = associator
  pb .Pb.triangle f g     = ext λ _ → CH.car (sym (C.compose.lmap-◆ _))
    ∙∙ C.triangle (σ f _) (σ g _)
    ∙∙ C.compose.rmap-◆ _
  pb .Pb.pentagon f g h i = ext λ _ → CH.car (sym (C.compose.lmap-◆ _))
    ∙∙ CH.cddr (sym (C.compose.rmap-◆ _))
    ∙∙ C.pentagon (σ f _) (σ g _) (σ h _) (σ i _)

Laxₒ : Prebicategory o h ℓ → Prebicategory o' h' ℓ' → Prebicategory _ _ _
Laxₒ B C = Laxₗ (B ^co) (C ^co) ^co

Pseudoₗ : Prebicategory o h ℓ → Prebicategory o' h' ℓ' → Prebicategory _ _ _
Pseudoₗ B C .Pb.Ob         = Pseudofunctor B C
Pseudoₗ B C .Pb.Hom F G    = Pseudoₗ[ F , G ]
Pseudoₗ B C .Pb.id         = idlx
Pseudoₗ B C .Pb.compose    = Lax.compose B C
Pseudoₗ B C .Pb.unitor-l   = Lax.unitor-l B C
Pseudoₗ B C .Pb.unitor-r   = Lax.unitor-r B C
Pseudoₗ B C .Pb.associator = to-natural-iso ni where
  ni : make-natural-iso _ _
  ni .make-natural-iso.eta           = Lax.associator B C .to .η
  ni .make-natural-iso.inv           = Lax.associator B C .from .η
  ni .make-natural-iso.eta∘inv _     = ext λ _ → Br.α≅ C .invl
  ni .make-natural-iso.inv∘eta _     = ext λ _ → Br.α≅ C .invr
  ni .make-natural-iso.natural _ _ _ = ext λ _ → bicat! C
Pseudoₗ B C .Pb.triangle f g     = Lax.pb B C .Pb.triangle f g
Pseudoₗ B C .Pb.pentagon f g h i = Lax.pb B C .Pb.pentagon f g h i

Pseudoₒ : Prebicategory o h ℓ → Prebicategory o' h' ℓ' → Prebicategory _ _ _
Pseudoₒ B C = Pseudoₗ (B ^co) (C ^co) ^co
