open import Cat.Bi.Lax-functor.IndexedCategory
open import Cat.Bi.Lax-functor.Modification
open import Cat.Bi.Instances.Lax-functor
open import Cat.Bi.Lax-functor.Constant
open import Cat.Bi.Instances.Discrete
open import Cat.Bi.Lax-functor.Base
open import Cat.Functor.Equivalence
open import Cat.Bi.Lax-functor.Hom
open import Cat.Functor.Naturality
open import Cat.Functor.Bifunctor
open import Cat.Functor.Coherence
open import Cat.Displayed.Total
open import Cat.Functor.Adjoint
open import Cat.Bi.Equivalence hiding (is-equivalence)
open import Cat.Functor.Solver
open import Cat.Functor.Base
open import Cat.Bi.Duality hiding (_^op)
open import Cat.Bi.Base
open import Cat.Prelude

import Cat.Displayed.Reasoning as Dr
import Cat.Functor.Reasoning as Fr
import Cat.Bi.Reasoning as Br
import Cat.Reasoning as Cr

module Cat.Bi.Diagram.Colimit where

private variable
  o h ℓ o' h' ℓ' : Level

module _
  {I : Prebicategory o h ℓ}
  {C : Prebicategory o' (o ⊔ h ⊔ ℓ ⊔ h' ⊔ ℓ') (o ⊔ h ⊔ ℓ ⊔ ℓ')}
  where
  open Prebicategory C
  open Pseudofunctor

  is-lax-colim : Pseudofunctor I C → Ob → Type _
  is-lax-colim F L = Equivalenceᵖ (lhs .lax) (rhs .lax) where
    lhs = Hom-from-bi (Pseudoₒ I C) (opᵖ F) P∘ Const-pseudoₒ
    rhs = Hom-from-bi C L

module CatLaxColim
  {I : Precategory o h}
  (F : Pseudofunctor (Locally-discrete (I ^op)) (Cat (o ⊔ o') (h ⊔ h')))
  where

  open Pseudofunctor
  open Pseudonatural
  open Equivalenceᵖ
  open Modification
  open Lax-transfor
  open Cr.Inverses
  open Functor
  open Cr._≅_
  open _=>_

  private
    module I      = Precategory I
    module F      = IndexedCategory F
    module F₀ {x} = Cr (F.₀ x)
    module G      = Cr (∫ F.displayed)
    module Cat    = Br (Cat (o ⊔ o') (h ⊔ h'))

    open Dr F.displayed

  univ-cocone : opᵖ F .lax =>ₒ ConstP F.∫ .lax
  univ-cocone .σ a                       = F.ιᶠ a
  univ-cocone .naturator .η f            = nat-unidl-to (F.ιᶠ-base-change f)
  univ-cocone .naturator .is-natural f g =
    J (λ g p → nat-unidl-to (F.ιᶠ-base-change g) ∘nt (_ ▸ F.₂ p)
             ≡ (idnt ◂ _) ∘nt nat-unidl-to (F.ιᶠ-base-change f)) $
    nat-unidl-to (F.ιᶠ-base-change f) ∘nt (_ ▸ F.₂ refl) ≡⟨ Cat.Hom.elimr (Fr.elim (postaction (Cat _ _) _) F.P₁.F-id) ⟩
    nat-unidl-to (F.ιᶠ-base-change f)                    ≡⟨ Cat.Hom.introl Cat.◀.F-id ⟩
    (idnt ◂ _) ∘nt nat-unidl-to (F.ιᶠ-base-change f)     ∎
  univ-cocone .ν-compositor f g = ext λ _ → sym $
    let
      p : id' ∘' id' ≡ (id' F₀.∘ F.γ← _ .η _) ∘' id' F₀.∘ F.γ→ _ .η _
      p = cast[] (idr' _ ∙[] F₀.insertr (F.γ≅' .invr) ∙[] symP F.cancel-id')
    in
       G.eliml (G.idl _) ∙ G.idl _
    ∙∙ G.cdr (G.idl _ ∙ G.cdr (sym (G.idr _) ∙ Fr.weave (ιᶠ _ _) (F₀.cdr p)))
    ∙∙ sym (G.pushl3 (F.ιᶠ-base-change-comp f g ηₚ _))
  univ-cocone .ν-unitor = ext λ _ →
    Fr.weave (ιᶠ _ _)
      (F₀.cdr (cast[] (F.cancel-id' ∙[] F₀.idl _ ∙[] symP (idr' _))))
    ∙ G.introl (G.idl _)

  module _ (X : Precategory (o ⊔ o') (h ⊔ h')) where
    open Cr X hiding (invl ; invr)
    private
      module Ox = IndexedOplax {F = opᵖ F} {ConstP X}
      ν-unitor'
        : ∀ (α : ⌞ Pseudoₒ[ opᵖ F , ConstP X ] ⌟ ) {i} y
        → α .ν→ I.id .η y ∘ α .σ i .F₁ (F.υ→ .η _) ≡ id
      ν-unitor' α y = Ox.ν-unitor α y ∙ idr _

    cocone→mediator₀ : opᵖ F .lax =>ₒ ConstP X .lax → Functor F.∫ X
    cocone→mediator₀ α = funct where
      module α = Lax-transfor α
      funct : Functor F.∫ X
      funct .F₀ (x , Fx)                      = α.σ x .F₀ Fx
      funct .F₁ {x , Fx} {y , Fy} (∫hom f Ff) = α.ν→ f .η Fy ∘ α.σ x .F₁ Ff
      funct .F-id {x , Fx}                    = ν-unitor' α Fx
      funct .F-∘ {x , Fx} {y , Fy} {z , Fz} (∫hom f Ff) (∫hom g Fg) =
        α.ν→ (f I.∘ g) .η Fz ∘ α.σ x .F₁ (Ff ∘' Fg)                          ≡⟨ cdr (sym $ Fr.collapse3 (α.σ x) refl) ⟩
        α.ν→ (f I.∘ g) .η Fz ∘ α.σ x .F₁ (F.γ→ (g , f) .η Fz) ∘ _            ≡⟨ extendl (Ox.ν-compositor α f g Fz ∙ eliml (idl _)) ⟩
        α.ν→ f .η Fz ∘ α.ν→ g .η _ ∘ α.σ x .F₁ (F.₁ g .F₁ Ff) ∘ α.σ x .F₁ Fg ≡⟨ cdr (extendl (α.ν→ g .is-natural _ _ _)) ∙ assoc _ _ _ ⟩
        (α.ν→ f .η Fz ∘ α.σ y .F₁ Ff) ∘ α.ν→ g .η Fy ∘ α.σ x .F₁ Fg          ∎

    cocone→mediator : Functor Pseudoₒ[ opᵖ F , ConstP X ] Cat[ F.∫ , X ]
    cocone→mediator .F₀               = cocone→mediator₀
    cocone→mediator .F₁ γ .η (x , Fx) = γ .Γ x .η Fx
    cocone→mediator .F₁ {α} {β} γ .is-natural (x , Fx) (y , Fy) (∫hom f Ff) =
      γ .Γ y .η Fy ∘ α .ν→ f .η Fy ∘ α .σ x .F₁ Ff             ≡˘⟨ extendl (γ .is-natural ηₚ Fy) ⟩
      β .ν→ f .η Fy ∘ γ .Γ x .η (F.₁ f .F₀ Fy) ∘ α .σ x .F₁ Ff ≡⟨ pushr (γ .Γ x .is-natural _ _ _) ⟩
      (β .ν→ f .η Fy ∘ β .σ x .F₁ Ff) ∘ γ .Γ x .η Fx           ∎
    cocone→mediator .F-id    = ext λ _ → refl
    cocone→mediator .F-∘ γ δ = ext λ _ → refl

    cocone→mediator⁻¹ : Functor Cat[ F.∫ , X ] Pseudoₒ[ opᵖ F , ConstP X ]
    cocone→mediator⁻¹ =
         preaction (Pseudoₒ _ _) {opᵖ F} {ConstP F.∫} {ConstP X} univ-cocone
      F∘ Const-pseudoₒ.Const₁

    cocone→mediator-unit : Id ≅ⁿ cocone→mediator⁻¹ F∘ cocone→mediator
    cocone→mediator-unit = to-natural-iso ni where
      abstract
        cocone-factors
          : ∀ (α : ⌞ Pseudoₒ[ opᵖ F , ConstP X ] ⌟ ) {a b} {f : I.Hom b a} i
          → α .ν→ f .η i ≡ (cocone→mediator⁻¹ F∘ cocone→mediator) .F₀ α .ν→ f .η i
        cocone-factors α i =
          sym $ idl _ ∙∙ eliml (idl _) ∙∙ idl _ ∙∙ idr _ ∙∙ elimr (α .σ _ .F-id)

      ni : make-natural-iso _ _
      ni .make-natural-iso.eta α .Γ a .η _              = id
      ni .make-natural-iso.eta α .Γ a .is-natural _ _ _ =
        pushl (sym (ν-unitor' α _)) ∙∙ sym (cdr (α .σ a .F-∘ _ _)) ∙∙ sym (idr _)
      ni .make-natural-iso.eta α .is-natural = ext λ i →
        idr _ ∙∙ sym (cocone-factors α i) ∙∙ sym (idl _)
      ni .make-natural-iso.inv α .Γ a .η _              = id
      ni .make-natural-iso.inv α .Γ a .is-natural _ _ _ =
        idl _ ∙ cdr (α .σ a .F-∘ _ _) ∙∙ cancell (ν-unitor' α _) ∙∙ sym (idr _)
      ni .make-natural-iso.inv α .is-natural {b = b} = ext λ i →
        idr _ ∙∙ cocone-factors α i ∙∙ sym (idl _)
      ni .make-natural-iso.eta∘inv _     = ext λ _ _ → idl _
      ni .make-natural-iso.inv∘eta _     = ext λ _ _ → idl _
      ni .make-natural-iso.natural _ α f = ext λ _ _ → idr _ ∙ car (ν-unitor' α _)

    cocone→mediator-counit : cocone→mediator F∘ cocone→mediator⁻¹ ≅ⁿ Id
    cocone→mediator-counit = to-natural-iso ni where
      mediator-stable
        : ∀ (G : Functor F.∫ X) {a b} (f : G.Hom a b)
        → (cocone→mediator F∘ cocone→mediator⁻¹) .F₀ G .F₁ f ≡ G .F₁ f
      mediator-stable G (∫hom f Ff) =
          car (idl _ ∙ eliml (idl _) ∙∙ idl _ ∙∙ idr _)
        ∙ Fr.collapse G (∫Hom-path _ (I.idr _) $ cast[] $ F.cancel-id' ∙[] F₀.idl _)

      ni : make-natural-iso _ _
      ni .make-natural-iso.eta G .η _              = id
      ni .make-natural-iso.eta G .is-natural _ _ f =
        idl _ ∙∙ mediator-stable G f ∙∙ sym (idr _)
      ni .make-natural-iso.inv G .η _              = id
      ni .make-natural-iso.inv G .is-natural _ _ f =
        idl _ ∙∙ sym (mediator-stable G f) ∙∙ sym (idr _)
      ni .make-natural-iso.eta∘inv _ = ext λ _ → idl _
      ni .make-natural-iso.inv∘eta _ = ext λ _ → idl _
      ni .make-natural-iso.natural G H α = ext λ _ →
        idr _ ∙ introl (H .F-id) ∙ sym (idl _)

    cocone→mediator⊣ : cocone→mediator ⊣ cocone→mediator⁻¹
    cocone→mediator⊣ ._⊣_.unit    = cocone→mediator-unit .to
    cocone→mediator⊣ ._⊣_.counit  = cocone→mediator-counit .to
    cocone→mediator⊣ ._⊣_.zig     = ext λ _   → idl _
    cocone→mediator⊣ ._⊣_.zag {G} = ext λ _ _ → idr _ ∙ eliml (G .F-id)

    cocone→mediator-equiv : is-equivalence cocone→mediator
    cocone→mediator-equiv .is-equivalence.F⁻¹        = cocone→mediator⁻¹
    cocone→mediator-equiv .is-equivalence.F⊣F⁻¹      = cocone→mediator⊣
    cocone→mediator-equiv .is-equivalence.unit-iso α =
      Cr.iso→invertible Laxₒ[ _ , _ ] (isoⁿ→iso cocone→mediator-unit α)
    cocone→mediator-equiv .is-equivalence.counit-iso G =
      Cr.iso→invertible Cat[ _ , _ ] (isoⁿ→iso cocone→mediator-counit G)

  module _ {X Y : Precategory (o ⊔ o') (h ⊔ h')} where
    open Precategory X

    cocone→mediator-nat
      :  preaction (Cat _ _) (cocone→mediator Y) F∘ Cat.compose
      ≅ⁿ postaction (Cat _ _) (cocone→mediator X)
      F∘ Flip (Lax.compose _ _) F∘ Const-pseudoₒ.Const₁
    cocone→mediator-nat = to-natural-iso ni where
      ni : make-natural-iso _ _
      ni .make-natural-iso.eta G .η α .η _              = id
      ni .make-natural-iso.eta G .η α .is-natural _ _ _ = functor! X
      ni .make-natural-iso.eta G .is-natural _ _ _      =
        ext λ _ → Cr.id-comm-sym X ∙ sym (idr _)
      ni .make-natural-iso.inv G .η α .η _              = id
      ni .make-natural-iso.inv G .η α .is-natural _ _ _ = functor! X
      ni .make-natural-iso.inv G .is-natural _ _ _      = ext λ _ → idl _
      ni .make-natural-iso.eta∘inv x                    = ext λ _ _ → idr _
      ni .make-natural-iso.inv∘eta x                    = ext λ _ _ → idl _
      ni .make-natural-iso.natural _ G f                = ext λ _ _ →
        idr _ ∙ ap₂ _∘_ (G .F-id) refl

  ∫-is-colim : is-lax-colim {h' = lzero} {ℓ' = o' ⊔ h'} F F.∫
  ∫-is-colim .to .lax .σ                        = cocone→mediator
  ∫-is-colim .to .lax .naturator                = cocone→mediator-nat .to
  ∫-is-colim .to .lax .ν-compositor {c = X} f g = ext λ _ _ → functor! X
  ∫-is-colim .to .lax .ν-unitor {X}             = ext λ _ _ → cat! X
  ∫-is-colim .to .naturator-inv f               =
    Cr.iso→invertible Cat[ _ , _ ] (isoⁿ→iso cocone→mediator-nat f)
  ∫-is-colim .to-equiv X = is-equivalenceᶜ→is-equivalence (cocone→mediator-equiv X)
