open import Cat.Instances.Functor.Limits
open import Cat.Instances.Sets.Complete
open import Cat.Diagram.Exponential
open import Cat.Diagram.Everything
open import Cat.Instances.Functor
open import Cat.Functor.Adjoint
open import Cat.Instances.Sets
open import Cat.Functor.Hom
open import Cat.Prelude

open import Data.Sum

import Cat.Functor.Bifunctor as Bifunctor
import Cat.Reasoning

module Cat.CartesianClosed.Instances.PSh where

open Functor
open _=>_
open _⊣_


-- This module has explicit computational representations of a bunch of
-- stuff we know exists by abstract nonsense.

module _ {o ℓ κ} {C : Precategory o ℓ} where
  open Binary-coproducts
  open Binary-products
  open Coequalisers
  open Equalisers
  open Pushouts
  open Pullbacks

  private
    module C = Cat.Reasoning C
    module PSh = Cat.Reasoning (PSh κ C)

  PSh-terminal : Terminal (PSh κ C)
  PSh-terminal = record { top = top ; has⊤ = uniq } where
    top : Functor (C ^op) (Sets κ)
    top .F₀ x = el! (Lift κ ⊤)
    top .F₁ _ _ = lift tt
    top .F-id = refl
    top .F-∘ _ _ = refl

    uniq : is-terminal (PSh κ C) top
    uniq x .centre .η _ _ = lift tt
    uniq x .centre .is-natural _ _ _ = refl
    uniq x .paths f = trivial!

  {-# TERMINATING #-}
  PSh-pullbacks : Pullbacks (PSh κ C)
  PSh-pullbacks .Pb {X} {Y} f g .F₀ i =
    el! (Σ[ x ∈ X ʻ i ] Σ[ y ∈ Y ʻ i ] (f .η i x ≡ g .η i y))
  PSh-pullbacks .Pb {X} {Y} {Z} f g .F₁ {x} {y} h (a , b , p) =
    X .F₁ h a , Y .F₁ h b , path where abstract
      path : f .η y (X .F₁ h a) ≡ g .η y (Y .F₁ h b)
      path = happly (f .is-natural _ _ _) _
          ·· (λ i → Z .F₁ h (p i))
          ·· sym (happly (g .is-natural _ _ _) _)
  PSh-pullbacks .Pb {X} {Y} f g .F-id =
    ext λ a b p → X .F-id $ₚ a ,ₚ Y .F-id $ₚ b ,ₚ prop!
  PSh-pullbacks .Pb {X} {Y} f g .F-∘ h h' =
    ext λ a b p → X .F-∘ h h' $ₚ a ,ₚ Y .F-∘ h h' $ₚ b ,ₚ prop!
  PSh-pullbacks .p₁ f g .η idx (a , _ , _) = a
  PSh-pullbacks .p₁ f g .is-natural _ _ _ = refl
  PSh-pullbacks .p₂ f g .η idx (_ , b , _) = b
  PSh-pullbacks .p₂ f g .is-natural _ _ _ = refl
  PSh-pullbacks .square = ext λ i a b p → p
  PSh-pullbacks .pb f g p .η idx arg =
    f .η idx arg , g .η idx arg , unext p idx arg
  PSh-pullbacks .pb f g p .is-natural x y h =
    ext λ a → f .is-natural x y h $ₚ a ,ₚ g .is-natural x y h $ₚ a ,ₚ prop!
  PSh-pullbacks .p₁∘pb = trivial!
  PSh-pullbacks .p₂∘pb = trivial!
  PSh-pullbacks .pb-unique p q =
    ext λ i a → unext p i a ,ₚ unext q i a ,ₚ prop!

  {-# TERMINATING #-}
  PSh-products : Binary-products (PSh κ C)
  PSh-products ._⊗₀_ X Y .F₀ i = el! (X ʻ i × Y ʻ i)
  PSh-products ._⊗₀_ X Y .F₁ f (x , y) = X .F₁ f x , Y .F₁ f y
  PSh-products ._⊗₀_ X Y .F-id = ext λ x y → X .F-id $ₚ x , Y .F-id $ₚ y
  PSh-products ._⊗₀_ X Y .F-∘ f g = ext λ x y → X .F-∘ f g $ₚ x , Y .F-∘ f g $ₚ y
  PSh-products .π₁ .η i = fst
  PSh-products .π₁ .is-natural _ _ _ = refl
  PSh-products .π₂ .η i = snd
  PSh-products .π₂ .is-natural _ _ _ = refl
  PSh-products .⟨_,_⟩ f g .η i x = f .η i x , g .η i x
  PSh-products .⟨_,_⟩ f g .is-natural x y h =
    ext λ i → f .is-natural x y h $ₚ i , g .is-natural x y h $ₚ i
  PSh-products .π₁∘⟨⟩ = trivial!
  PSh-products .π₂∘⟨⟩ = trivial!
  PSh-products .⟨⟩-unique p q =
    ext λ i x → unext p i x , unext q i x

  {-# TERMINATING #-}
  PSh-coproducts : Binary-coproducts (PSh κ C)
  PSh-coproducts ._⊕₀_ X Y .F₀ i = el! (X ʻ i ⊎ Y ʻ i)
  PSh-coproducts ._⊕₀_ X Y .F₁ f = ⊎-map (X .F₁ f) (Y .F₁ f)
  PSh-coproducts ._⊕₀_ X Y .F-id =
    ext λ where
      (inl a) → ap inl (X .F-id $ₚ a)
      (inr b) → ap inr (Y .F-id $ₚ b)
  PSh-coproducts ._⊕₀_ X Y .F-∘ f g =
    ext λ where
      (inl a) → ap inl (X .F-∘ f g $ₚ a)
      (inr b) → ap inr (Y .F-∘ f g $ₚ b)
  PSh-coproducts .ι₁ .η i = inl
  PSh-coproducts .ι₁ .is-natural _ _ _ = refl
  PSh-coproducts .ι₂ .η i = inr
  PSh-coproducts .ι₂ .is-natural _ _ _ = refl
  PSh-coproducts .Binary-coproducts.[_,_] f g .η i (inl a) = f .η i a
  PSh-coproducts .Binary-coproducts.[_,_] f g .η i (inr b) = g .η i b
  PSh-coproducts .Binary-coproducts.[_,_] f g .is-natural x y h =
    ext λ where
      (inl a) → f .is-natural x y h $ₚ a
      (inr b) → g .is-natural x y h $ₚ b
  PSh-coproducts .[]∘ι₁ = trivial!
  PSh-coproducts .[]∘ι₂ = trivial!
  PSh-coproducts .Binary-coproducts.[]-unique p q =
    ext λ where
      i (inl a) → unext p i a
      i (inr b) → unext q i b


  {-# TERMINATING #-}
  PSh-coequalisers : Coequalisers (PSh κ C)
  PSh-coequalisers .Coequ {X} {Y} f g .F₀ i = el! (Coeq (f .η i) (g .η i))
  PSh-coequalisers .Coequ {X} {Y} f g .F₁ h =
    Coeq-rec (λ x → inc (Y .F₁ h x)) λ x →
      inc (Y .F₁ h (f .η _ x)) ≡˘⟨ ap Coeq.inc (happly (f .is-natural _ _ h) x) ⟩
      inc (f .η _ _)         ≡⟨ glue (X .F₁ h x) ⟩
      inc (g .η _ _)         ≡⟨ ap Coeq.inc (happly (g .is-natural _ _ h) x) ⟩
      inc (Y .F₁ h (g .η _ x)) ∎
  PSh-coequalisers .Coequ {X} {Y} f g .F-id = ext λ x → ap Coeq.inc (Y .F-id $ₚ x)
  PSh-coequalisers .Coequ {X} {Y} f g .F-∘ h h' = ext λ x → ap Coeq.inc (Y .F-∘ h h' $ₚ x)
  PSh-coequalisers .coequ f g .η i = inc
  PSh-coequalisers .coequ f g .is-natural _ _ _ = refl
  PSh-coequalisers .coequal = ext λ i x → glue x
  PSh-coequalisers .coequalise {E} e' p .η i =
    Coeq-rec (e' .η i) (unext p i)
  PSh-coequalisers .coequalise {E} e' p .is-natural x y h =
    ext λ i → e' .is-natural x y h $ₚ i
  PSh-coequalisers .coequalise∘coequ = trivial!
  PSh-coequalisers .coequalise-unique p = reext! p

module _ {κ} {C : Precategory κ κ} where
  private
    module C = Cat.Reasoning C
    module PSh = Cat.Reasoning (PSh κ C)

  open Binary-products (PSh-products {κ = κ} {C = C})

  PSh[_,_] : PSh.Ob → PSh.Ob → PSh.Ob
  PSh[ A , B ] = F module psh-exp where
    module A = Functor A
    module B = Functor B

    F : PSh.Ob
    F .F₀ c = el ((よ₀ C c ⊗₀ A) => B) Nat-is-set
    F .F₁ f nt .η i (g , x) = nt .η i (f C.∘ g , x)
    F .F₁ f nt .is-natural x y g = funext λ o →
      ap (nt .η y) (Σ-pathp (C.assoc _ _ _) refl) ∙ happly (nt .is-natural _ _ _) _
    F .F-id = ext λ f i g x →
      ap (f .η i) (Σ-pathp (C.idl _) refl)
    F .F-∘ f g = ext λ h i x a →
      ap (h .η i) (sym (C.assoc _ _ _) ,ₚ refl)

  {-# DISPLAY psh-exp.F A B = PSh[ A , B ] #-}

  PSh-closed : Cartesian-closed (PSh κ C) (PSh-products {C = C}) (PSh-terminal {C = C})
  PSh-closed = cc where
    cat = PSh κ C

    module _ (A : PSh.Ob) where
      func : Functor (PSh κ C) (PSh κ C)
      func .F₀ = PSh[ A ,_]
      func .F₁ f .η i g .η j (h , x) = f .η _ (g .η _ (h , x))
      func .F₁ f .η i g .is-natural x y h = funext λ x →
        ap (f .η _) (happly (g .is-natural _ _ _) _) ∙ happly (f .is-natural _ _ _) _
      func .F₁ nt .is-natural x y f = trivial!
      func .F-id = trivial!
      func .F-∘ f g = trivial!

      adj : Bifunctor.Left ×-functor A ⊣ func
      adj .unit .η x .η i a =
        NT (λ j (h , b) → x .F₁ h a , b) λ _ _ _ → funext λ _ →
          Σ-pathp (happly (x .F-∘ _ _) _) refl
      adj .unit .η x .is-natural _ _ _ = ext λ _ _ _ _ → sym (x .F-∘ _ _ # _) , refl
      adj .unit .is-natural x y f = ext λ _ _ _ _ _ → sym (f .is-natural _ _ _ $ₚ _) , refl
      adj .counit .η _ .η _ x = x .fst .η _ (C.id , x .snd)
      adj .counit .η _ .is-natural x y f = funext λ h →
        ap (h .fst .η _) (Σ-pathp C.id-comm refl) ∙ happly (h .fst .is-natural _ _ _) _
      adj .counit .is-natural x y f = trivial!
      adj .zig {A} = ext λ x _ _ → happly (F-id A) _ , refl
      adj .zag {A} = ext λ _ x i f g j → x .η i (C.idr f j , g)

    cc : Cartesian-closed (PSh κ C) (PSh-products {C = C}) (PSh-terminal {C = C})
    cc = product-adjoint→cartesian-closed (PSh κ C)
      (PSh-products {C = C}) (PSh-terminal {C = C}) func adj
