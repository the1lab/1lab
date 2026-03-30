open import Cat.Functor.Adjoint renaming (_⊣_ to _⊣ᶜ_)
open import Cat.Bi.Base
open import Cat.Prelude

import Cat.Reasoning as Cr

module Cat.Bi.Adjoint where

private variable
  o o' h h' ℓ : Level

module Adjoint (C : Prebicategory o h ℓ) where

  open Prebicategory C

  record _⊣_ {A B} (l : A ↦ B) (r : B ↦ A) : Type ℓ where
    no-eta-equality
    field
      η : id ⇒ r ⊗ l
      ε : l ⊗ r ⇒ id

      zig : λ← _ ∘ ε ◀ l ∘ α← _ ∘ l ▶ η ∘ ρ→ _ ≡ Hom.id
      zag : ρ← _ ∘ r ▶ ε ∘ α→ _ ∘ η ◀ r ∘ λ→ _ ≡ Hom.id

  infixr 15 _⊣_

  module _ {A B} {l : A ↦ B} {r : B ↦ A} {adj adj' : l ⊣ r} where
    private
      module adj  = _⊣_ adj
      module adj' = _⊣_ adj'

    adjoint-path : adj.η ≡ adj'.η → adj.ε ≡ adj'.ε → adj ≡ adj'
    adjoint-path p q i ._⊣_.η   = p i
    adjoint-path p q i ._⊣_.ε   = q i
    adjoint-path p q i ._⊣_.zig = is-prop→pathp
      (λ i → Hom.Hom-set l l (λ← _ ∘ q i ◀ l ∘ α← _ ∘ l ▶ p i ∘ ρ→ _) Hom.id)
      adj.zig adj'.zig i
    adjoint-path p q i ._⊣_.zag = is-prop→pathp
      (λ i → Hom.Hom-set r r (ρ← _ ∘ r ▶ q i ∘ α→ _ ∘ p i ◀ r ∘ λ→ _) Hom.id)
      adj.zag adj'.zag i


module _
  {C : Precategory o h} {D : Precategory o h} {F : Functor C D} {G : Functor D C}
  where

  open Adjoint (Cat o h)
  open Functor

  adjointᶜ→adjoint : F ⊣ᶜ G → F ⊣ G
  adjointᶜ→adjoint F⊣G ._⊣_.η   = _⊣ᶜ_.unit F⊣G
  adjointᶜ→adjoint F⊣G ._⊣_.ε   = _⊣ᶜ_.counit F⊣G
  adjointᶜ→adjoint F⊣G ._⊣_.zig = ext λ _ →
    idl _ ∙∙ ap₂ _∘_ refl (idl _ ∙ idr _) ∙∙ _⊣ᶜ_.zig F⊣G
    where open Precategory D
  adjointᶜ→adjoint F⊣G ._⊣_.zag = ext λ _ →
    idl _ ∙∙ ap₂ _∘_ refl (idl _ ∙ idr _) ∙∙ _⊣ᶜ_.zag F⊣G
    where open Precategory C

  adjoint→adjointᶜ : F ⊣ G → F ⊣ᶜ G
  adjoint→adjointᶜ F⊣G ._⊣ᶜ_.unit   = _⊣_.η F⊣G
  adjoint→adjointᶜ F⊣G ._⊣ᶜ_.counit = _⊣_.ε F⊣G
  adjoint→adjointᶜ F⊣G ._⊣ᶜ_.zig    =
    sym (idl _ ∙ ap₂ _∘_ refl (idl _ ∙ idr _)) ∙ _⊣_.zig F⊣G ηₚ _
    where open Precategory D
  adjoint→adjointᶜ F⊣G ._⊣ᶜ_.zag =
    sym (idl _ ∙ ap₂ _∘_ refl (idl _ ∙ idr _)) ∙ _⊣_.zag F⊣G ηₚ _
    where open Precategory C

  adjoint≃adjointᶜ : (F ⊣ G) ≃ (F ⊣ᶜ G)
  adjoint≃adjointᶜ .fst = adjoint→adjointᶜ
  adjoint≃adjointᶜ .snd = is-iso→is-equiv $ iso
    adjointᶜ→adjoint
    (λ x → adjoint-pathp refl refl refl refl)
    (λ x → adjoint-path refl refl)
