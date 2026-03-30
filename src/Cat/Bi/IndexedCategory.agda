open import Cat.Bi.Instances.Discrete
open import Cat.Displayed.Cartesian
open import Cat.Functor.Equivalence
open import Cat.Functor.Naturality
open import Cat.Instances.Discrete
open import Cat.Functor.Coherence
open import Cat.Displayed.Fibre
open import Cat.Functor.Adjoint
open import Cat.Bi.Lax-functor
open import Cat.Displayed.Base
open import Cat.Functor.Base
open import Cat.Bi.Duality hiding (_^op)
open import Cat.Groupoid
open import Cat.Bi.Base
open import Cat.Prelude

import Cat.Displayed.Cartesian.Indexing as Idx
import Cat.Displayed.Reasoning as Dr
import Cat.Functor.Reasoning as Fr
import Cat.Displayed.Total as Total
import Cat.Reasoning as Cr

module Cat.Bi.IndexedCategory where

module IndexedCategory
  {o h o' h'}
  {I : Precategory o h}
  (F : Pseudofunctor (Locally-discrete (I ^op)) (Cat o' h'))
  where

  open Cartesian-lift
  open is-cartesian
  open Cr.Inverses
  open Functor hiding (₀ ; ₁)
  open Cr._≅_
  open _=>_

  private
    module I = Precategory I
    module F = Pf-reasoning F
    open module F₀ {x} = Cr (F.₀ x)

    module pg {x} {y} =
      is-pregroupoid {C = Disc' (el (I.Hom x y) (I.Hom-set x y))} Disc-is-groupoid

  open F public hiding (left-unit ; right-unit ; hexagon)

  υ≅' : ∀ {A : I.Ob} {x : Ob {A}} → x ≅ ₁ I.id .F₀ x
  υ≅' = isoⁿ→iso υ≅ _

  γ≅'
    : ∀ {A B C : I.Ob} {f : I.Hom B C} {g : I.Hom A B} {x : Ob {C}}
    → ₁ g .F₀ (₁ f .F₀ x) ≅ ₁ (f I.∘ g) .F₀ x
  γ≅' = isoⁿ→iso γ≅ _

  abstract
    P₁-path
      : ∀ {A B} {f g : I.Hom A B} {x y} {Ff Fg} (p : f ≡ g)
      → ₂ p .η y ∘ Ff ≡ Fg
      → PathP (λ i → Hom x (F₀ (₁ (p i)) y)) Ff Fg
    P₁-path {A} {y = y} {Ff} p q = Hom-pathp-reflr (₀ A) $
      ap (_∘ Ff) (
        sym Regularity.reduce!
        ∙ ap Cr._≅_.to (P₁.ap-F₀-iso Disc-is-category (pg.hom→iso p)) ηₚ y
      ) ∙ q

    left-unit
      : ∀ {A B} (f : I.Hom A B) Fy
      → ₂ (I.idr f) .η Fy ∘ γ→ (I.id , f) .η Fy ∘ υ→ .η (₁ f .F₀ Fy) ≡ id
    left-unit f Fy = F.left-unit f ηₚ Fy

    right-unit
      : ∀ {A B} (f : I.Hom A B) Fy
      → ₂ (I.idl f) .η Fy ∘ γ→ (f , I.id) .η Fy ∘ ₁ f .F₁ (υ→ .η Fy) ≡ id
    right-unit f Fy = F.right-unit f ηₚ Fy

    hexagon
      : ∀ {A B C D} (f : I.Hom C D) (g : I.Hom B C) (h : I.Hom A B) Fz
      → ₂ (I.assoc f g h) .η Fz ∘ γ→ ((g I.∘ h) , f) .η Fz ∘ γ→ (h , g) .η (₁ f .F₀ Fz)
      ≡ γ→ (h , (f I.∘ g)) .η Fz ∘ ₁ h .F₁ (γ→ (g , f) .η Fz)
    hexagon f g h Fz = F.hexagon h g f ηₚ Fz ∙ cdr (idr _)

    right-unit-υr
      : ∀ {A B} (f : I.Hom A B) Fy
      → ₂ (I.idl f) .η Fy ∘ γ→ (f , I.id) .η Fy ≡ ₁ f .F₁ (υ← .η Fy)
    right-unit-υr f Fy =
        ap₂ _∘_ refl (intror (F-iso.F-map-iso (₁ f) υ≅' .invl))
      ∙ cancell3 (right-unit f Fy)

    left-unit-υr-inv
      : ∀ {A B} (f : I.Hom A B) Fy
      → γ← (I.id , f) .η _ ∘ ₂ (sym (I.idr _)) .η _ ≡ υ→ .η (₁ f .F₀ Fy)
    left-unit-υr-inv f Fy =
         intror (left-unit f Fy)
      ∙∙ cancel-inner (P₁.F-map-iso (pg.hom→iso (I.idr _)) .invr ηₚ _)
      ∙∙ cancell (γ≅' .invr)


  displayed : Displayed I _ _
  displayed .Displayed.Ob[_] x              = F₀.Ob {x}
  displayed .Displayed.Hom[_] f Fx Fy       = F₀.Hom Fx (₁ f .F₀ Fy)
  displayed .Displayed.Hom[_]-set _ _ _     = hlevel 2
  displayed .Displayed.id'                  = υ→ .η _
  displayed .Displayed._∘'_ {g = g} Ff Fg   = γ→ _ .η _ ∘ ₁ g .F₁ Ff ∘ Fg
  displayed .Displayed.idr' {y = Fy} {f} Ff = P₁-path (I.idr f) $
    ₂ (I.idr f) .η Fy ∘ γ→ _ .η Fy ∘ ₁ I.id .F₁ Ff ∘ υ→ .η _ ≡⟨ refl⟩∘⟨ refl⟩∘⟨ sym (υ→ .is-natural _ _ _) ⟩
    ₂ (I.idr f) .η Fy ∘ γ→ _ .η Fy ∘ υ→ .η _ ∘ Ff            ≡⟨ cancell3 (left-unit f Fy) ⟩
    Ff                                                       ∎
  displayed .Displayed.idl' {y = Fy} {f} Ff = P₁-path (I.idl f)
    $ cancell3 (right-unit f Fy)
  displayed .Displayed.assoc' {z = Fz} {f} {g} {h} Ff Fg Fh = P₁-path (I.assoc f g h) $
      ₂ (I.assoc f g h) .η Fz ∘ γ→ _ .η Fz
    ∘ ₁ (g I.∘ h) .F₁ Ff ∘ γ→ _ .η _ ∘ ₁ h .F₁ Fg ∘ Fh
      ≡⟨ refl⟩∘⟨ refl⟩∘⟨ extendl (sym $ γ→ _ .is-natural _ _ _) ⟩
      ₂ (I.assoc f g h) .η Fz ∘ γ→ _ .η Fz
    ∘ γ→ _ .η (₁ f .F₀ Fz) ∘ ₁ h .F₁ (₁ g .F₁ Ff) ∘ ₁ h .F₁ Fg ∘ Fh
      ≡⟨ pulll3 (hexagon f g h Fz) ∙ sym (assoc _ _ _) ⟩
    γ→ _ .η Fz ∘ ₁ h .F₁ (γ→ _ .η Fz) ∘ ₁ h .F₁ (₁ g .F₁ Ff) ∘ ₁ h .F₁ Fg ∘ Fh
      ≡⟨ refl⟩∘⟨ Fr.pulll3 (₁ h) refl ⟩
    γ→ _ .η Fz ∘ ₁ h .F₁ (γ→ _ .η Fz ∘ ₁ g .F₁ Ff ∘ Fg) ∘ Fh
      ∎
  displayed .Displayed.hom[_] p Ff = ₂ p .η _ ∘ Ff
  displayed .Displayed.coh[_] p Ff = P₁-path p refl

  open Dr displayed

  fibration : Cartesian-fibration displayed
  fibration f y' .x'                        = F₀ (₁ f) y'
  fibration f y' .lifting                   = id
  fibration f y' .cartesian .universal m h' = γ← (m , f) .η y' ∘ h'
  fibration f y' .cartesian .commutes m h'  =
    ap₂ _∘_ refl (eliml (₁ m .F-id)) ∙ cancell (γ≅' .invl)
  fibration f y' .cartesian .unique {m = m} m' p =
    insertl3 (cancell (γ≅' .invr) ∙ ₁ m .F-id) ∙ ap₂ _∘_ refl p

  fibre-equiv-to : ∀ {x} → Functor (₀ x) (Fibre displayed x)
  fibre-equiv-to .F₀ z               = z
  fibre-equiv-to .F₁ Ff              = id' ∘ Ff
  fibre-equiv-to .F-id               = idr _
  fibre-equiv-to .F-∘ {z = Fz} Ff Fg = from-pathp[]⁻ $ begin[]
    id' ∘ Ff ∘ Fg                   ≡[]˘⟨ idl' _ ∙[] extendl (sym $ υ→ .is-natural _ _ _) ⟩
    id' ∘' ₁ I.id .F₁ Ff ∘ id' ∘ Fg ≡[]⟨ refl⟩∘⟨ Fr.pulll (₁ I.id) refl ⟩
    (id' ∘ Ff) ∘' id' ∘ Fg          ∎[]

  fibre-equiv-from : ∀ {x} → Functor (Fibre displayed x) (₀ x)
  fibre-equiv-from .F₀ z               = z
  fibre-equiv-from .F₁ Ff              = υ← .η _ ∘ Ff
  fibre-equiv-from .F-id               = isoⁿ→iso υ≅ _ .invr
  fibre-equiv-from .F-∘ {z = Fz} Ff Fg =
    υ← .η Fz ∘ ₂ (I.idl I.id) .η Fz ∘ Ff ∘' Fg           ≡⟨ refl⟩∘⟨ pulll (right-unit-υr I.id _) ⟩
    υ← .η Fz ∘ ₁ I.id .F₁ (υ← .η _) ∘ ₁ I.id .F₁ Ff ∘ Fg ≡⟨ ap (υ← .η _ ∘_) (Fr.pulll (₁ I.id) refl) ∙ extendl (υ← .is-natural _ _ _) ⟩
    (υ← .η Fz ∘ Ff) ∘ υ← .η _ ∘ Fg                       ∎

  fibre-equiv⊣ : ∀ {x} → fibre-equiv-to {x} ⊣ fibre-equiv-from
  fibre-equiv⊣ ._⊣_.unit .η _                = id
  fibre-equiv⊣ ._⊣_.unit .is-natural _ _ _   = idl _ ∙ insertl (υ≅' .invr) ∙ sym (idr _)
  fibre-equiv⊣ ._⊣_.counit .η _              = id'
  fibre-equiv⊣ ._⊣_.counit .is-natural _ _ f = from-pathp[] $ begin[]
    id' ∘' id' ∘ υ← .η _ ∘ f                  ≡[]⟨ idl' _ ∙[] υ→ .is-natural _ _ _ ∙ pushl (₁ I.id .F-∘ _ _) ⟩
    ₁ I.id .F₁ (υ← .η _) ∘ ₁ I.id .F₁ f ∘ id' ≡[]⟨ pushl (sym $ right-unit-υr I.id _) ⟩
    hom[] (f ∘' id')                          ∎[]
  fibre-equiv⊣ ._⊣_.zig = from-pathp[] (idl' _) ∙ idr _
  fibre-equiv⊣ ._⊣_.zag = eliml (υ≅' .invr)

  fibre-equiv : ∀ {x} → Equivalence (₀ x) (Fibre displayed x)
  fibre-equiv .Equivalence.To                                    = fibre-equiv-to
  fibre-equiv .Equivalence.To-equiv .is-equivalence.F⁻¹          = fibre-equiv-from
  fibre-equiv .Equivalence.To-equiv .is-equivalence.F⊣F⁻¹        = fibre-equiv⊣
  fibre-equiv .Equivalence.To-equiv .is-equivalence.unit-iso _   = id-invertible
  fibre-equiv .Equivalence.To-equiv .is-equivalence.counit-iso _ =
    Cr.id-invertible (Fibre displayed _)

  open Idx displayed fibration

  fibration-base-change
    : ∀ {a b} (f : I.Hom a b)
    → fibre-equiv-to F∘ F.₁ f ≅ⁿ base-change f F∘ fibre-equiv-to
  fibration-base-change f = to-natural-iso ni where
    ni : make-natural-iso _ _
    ni .make-natural-iso.eta x         = id'
    ni .make-natural-iso.inv x         = id'
    ni .make-natural-iso.eta∘inv x     = from-pathp[] $ idl' id'
    ni .make-natural-iso.inv∘eta x     = from-pathp[] $ idl' id'
    ni .make-natural-iso.natural _ y g = from-pathp[] $ begin[]
      (base-change f F∘ fibre-equiv-to) .F₁ g ∘' id'             ≡[]⟨ idr' _ ⟩
      (base-change f F∘ fibre-equiv-to) .F₁ g                    ≡[]⟨ p ⟩
      (fibre-equiv-to F∘ F.₁ f) .F₁ g                            ≡[]˘⟨ from-pathp[] (idl' _) ⟩
      hom[ I.idl I.id ] (id' ∘' (fibre-equiv-to F∘ F.₁ f) .F₁ g) ∎[]
      where
        p : (base-change f F∘ fibre-equiv-to) .F₁ g ≡ (fibre-equiv-to F∘ F.₁ f) .F₁ g
        p =
          γ← (I.id , f) .η y ∘ hom[ sym (Cr.id-comm I) ] (γ→ (f , I.id) .η y ∘ _) ≡⟨ refl⟩∘⟨ reindex _ _ ∙ pushl (P₁.F-∘ _ _ ηₚ y) ⟩
          γ← (I.id , f) .η y ∘ ₂ (sym (I.idr _)) .η _ ∘ hom[ I.idl _ ] _          ≡⟨ pulll (left-unit-υr-inv f y) ⟩
          υ→ .η _ ∘ hom[ I.idl _ ] (γ→ (f , I.id) .η _ ∘ ₁ f .F₁ (id' ∘ g) ∘ id)  ≡⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ idr _ ∙ ₁ f .F-∘ _ _ ⟩
          _ ∘ hom[ I.idl _ ] (id' ∘' ₁ f .F₁ g)                                   ≡⟨ refl⟩∘⟨ from-pathp[] (idl' _) ⟩
          υ→ .η _ ∘ ₁ f .F₁ g                                                     ∎

  private
    ιᶠ'                  = Total.ιᶠ displayed
    ιᶠ-base-change-comp' = Total.ιᶠ-base-change-comp displayed fibration

  ∫ : Precategory _ _
  ∫ = Total.∫ displayed

  ιᶠ : (x : I.Ob) → Functor (₀ x) ∫
  ιᶠ x = ιᶠ' x F∘ fibre-equiv-to

  -- We specialize the construction from Cat.Displayed.Total to avoid unnecessary
  -- identity morphisms.
  ιᶠ-base-change : ∀ {a b} (f : I.Hom a b) → ιᶠ a F∘ ₁ f => ιᶠ b
  ιᶠ-base-change f .η x              = Total.∫hom f id
  ιᶠ-base-change f .is-natural x y g =
    Total.∫Hom-path displayed (Cr.id-comm I) $ begin[]
      id ∘' id' ∘ ₁ f .F₁ g                           ≡[]⟨ apd (λ _ → F.γ→ (I.id , f) .η _ ∘_) (eliml (₁ I.id .F-id) ∙ F.υ→ .is-natural _ _ _) ⟩
      ₁ f .F₁ g ∘' id'                                ≡[]⟨ idr' _ ∙[] symP (idl' _) ⟩
      id' ∘' ₁ f .F₁ g                                ≡[]⟨ apd (λ _ → F.γ→ (f , I.id) .η _ ∘_) (sym (idr _ ∙ ₁ f .F-∘ _ _)) ⟩
      γ→ (f , I.id) .η y ∘ ₁ f .F₁ (υ→ .η y ∘ g) ∘ id ∎[]

  ιᶠ-base-change-comp
    : ∀ {a b c} (f : I.Hom b c) (g : I.Hom a b)
    → ιᶠ-base-change (f I.∘ g)
    ≡ ιᶠ-base-change f
    ∘nt nat-unassoc-from (ιᶠ-base-change g ◂ ₁ f)
    ∘nt (ιᶠ a ▸ γ← (g , f))
  ιᶠ-base-change-comp f g = ext λ i →
      ιᶠ-base-change-comp' f g ηₚ i
    ∙ (
      ap₂ G._∘_ refl $ ap₂ G._∘_ refl $ Total.∫Hom-path _ refl
    $ pulll (left-unit-υr-inv g _) ∙ ap₂ _∘_ refl (idr _)
    )
    where module G = Precategory ∫

open Pseudofunctor

module IndexedOplax
  {o h o' h'}
  {I : Precategory o h}
  {F G : Pseudofunctor (Locally-discrete (I ^op) ^co) (Cat o' h' ^co)}
  (α : F .lax =>ₗ G .lax)
  where

  open Functor
  open _=>_

  private
    module I = Precategory I
    module F = Pseudofunctor F
    module G = Pseudofunctor G
    module α = Lax-transfor α
    open module G₀ {x} = Cr (G.₀ x)

  open α hiding (ν-compositor ; ν-unitor) public

  ν-compositor
    : ∀ {a b c : I.Ob} (f : I.Hom b c) (g : I.Hom a b) Fx
    → G.γ→ (g , f) .η (σ c .F₀ Fx) ∘ ν→ (f I.∘ g) .η Fx
    ≡ G.₁ g .F₁ (ν→ f .η Fx) ∘ ν→ g .η _ ∘ σ a .F₁ (F.γ→ (g , f) .η _)
  ν-compositor f g Fx =
    α.ν-compositor g f ηₚ Fx ∙∙ car (idr _ ∙ car (idr _ ∙ idl _)) ∙∙ sym (assoc _ _ _)

  ν-unitor : ∀ {a : I.Ob} Fx → G.υ→ .η _ ∘ ν→ I.id .η Fx ≡ σ a .F₁ (F.υ→ .η Fx)
  ν-unitor Fx = α.ν-unitor ηₚ Fx ∙ eliml (idl _)
