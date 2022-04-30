open import Cat.Instances.Functor.Limits
open import Cat.Instances.Sets.Complete
open import Cat.CartesianClosed.Base
open import Cat.Diagram.Limit.Finite
open import Cat.Diagram.Limit.Base
open import Cat.Instances.Functor
open import Cat.Diagram.Pullback
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Functor.Adjoint
open import Cat.Instances.Sets
open import Cat.Functor.Hom
open import Cat.Prelude

import Cat.Reasoning

module Cat.CartesianClosed.Instances.PSh where

open Functor
open _=>_
open _⊣_

module _ {o ℓ κ} {C : Precategory o ℓ} where
  private
    module C = Cat.Reasoning C
    module PSh = Cat.Reasoning (PSh κ C)

  PSh-terminal : Terminal (PSh κ C)
  PSh-terminal = record { top = top ; has⊤ = uniq } where
    top : Functor (C ^op) (Sets κ)
    top .F₀ x = Lift κ ⊤ , λ _ _ _ _ _ _ → lift tt
    top .F₁ _ _ = lift tt
    top .F-id = refl
    top .F-∘ _ _ = refl

    uniq : is-terminal (PSh κ C) top
    uniq x .centre .η _ _ = lift tt
    uniq x .centre .is-natural _ _ _ = refl
    uniq x .paths f = Nat-path λ _ → refl

  PSh-pullbacks
    : ∀ {X Y Z} (f : PSh.Hom X Z) (g : PSh.Hom Y Z)
    → Pullback (PSh κ C) f g
  PSh-pullbacks {X} {Y} {Z} f g = pb where
    module X = Functor X
    module Y = Functor Y
    module Z = Functor Z
    module f = _=>_ f
    module g = _=>_ g
    open Pullback
    open is-pullback

    pb-path
      : ∀ {i} {x y : Σ[ x ∈ ∣ X.₀ i ∣ ] Σ[ y ∈ ∣ Y.₀ i ∣ ] (f.η i x ≡ g.η i y)}
      → x .fst ≡ y .fst
      → x .snd .fst ≡ y .snd .fst
      → x ≡ y
    pb-path p q i .fst = p i
    pb-path p q i .snd .fst = q i
    pb-path {idx} {x} {y} p q i .snd .snd j =
      is-set→squarep (λ _ _ → Z.₀ idx .is-tr)
        (ap (f .η idx) p) (x .snd .snd) (y .snd .snd) (ap (g .η idx) q)
        i j

    pb : Pullback (PSh κ C) f g
    pb .apex .F₀ i =
        (Σ[ x ∈ ∣ X.₀ i ∣ ] Σ[ y ∈ ∣ Y.₀ i ∣ ] (f.η i x ≡ g.η i y))
      , Σ-is-hlevel 2 (X.₀ i .is-tr) λ _ → Σ-is-hlevel 2 (Y.₀ i .is-tr)
        λ _ → is-prop→is-set (Z.₀ i .is-tr _ _)
    pb .apex .F₁ {x} {y} h (a , b , p) = X.₁ h a , Y.₁ h b , path where abstract
      path : f.η y (X.₁ h a) ≡ g.η y (Y.₁ h b)
      path = happly (f.is-natural _ _ _) _
          ·· (λ i → Z.₁ h (p i))
          ·· sym (happly (g.is-natural _ _ _) _)
    pb .apex .F-id = funext λ (a , b , _) → pb-path (happly X.F-id a) (happly Y.F-id b)
    pb .apex .F-∘ f g = funext λ (a , b , _) → pb-path (happly (X.F-∘ f g) a) (happly (Y.F-∘ f g) b)
    pb .p₁ .η idx (a , b , _) = a
    pb .p₁ .is-natural _ _ _ = refl
    pb .p₂ .η x (a , b , _) = b
    pb .p₂ .is-natural _ _ _ = refl
    pb .has-is-pb .square = Nat-path λ _ → funext λ (_ , _ , p) → p
    pb .has-is-pb .limiting path .η idx arg = _ , _ , ap (λ e → e .η idx arg) path
    pb .has-is-pb .limiting {p₁' = p₁'} {p₂'} path .is-natural x y f =
      funext λ x → pb-path (happly (p₁' .is-natural _ _ _) _) (happly (p₂' .is-natural _ _ _) _)
    pb .has-is-pb .p₁∘limiting = Nat-path λ _ → refl
    pb .has-is-pb .p₂∘limiting = Nat-path λ _ → refl
    pb .has-is-pb .unique p q = Nat-path λ _ → funext λ _ →
      pb-path (ap (λ e → e .η _ _) p) (ap (λ e → e .η _ _) q)

  PSh-products : (A B : PSh.Ob) → Product (PSh κ C) A B
  PSh-products A B = prod where
    open Product
    open is-product
    module A = Functor A
    module B = Functor B

    prod : Product (PSh _ C) A B
    prod .apex .F₀ x = (∣ A.₀ x ∣ × ∣ B.₀ x ∣) , ×-is-hlevel 2 (A.₀ x .is-tr) (B.₀ x .is-tr)
    prod .apex .F₁ f (x , y) = A.₁ f x , B.₁ f y
    prod .apex .F-id i (x , y) = A.F-id i x , B.F-id i y
    prod .apex .F-∘ f g i (x , y) = A.F-∘ f g i x , B.F-∘ f g i y
    prod .π₁ = NT (λ x → fst) (λ _ _ _ → refl)
    prod .π₂ = NT (λ x → snd) (λ _ _ _ → refl)
    prod .has-is-product .⟨_,_⟩ f g =
      NT (λ i x → f .η i x , g .η i x) λ x y h i a →
        f .is-natural x y h i a , g .is-natural x y h i a
    prod .has-is-product .π₁∘factor = Nat-path λ x → refl
    prod .has-is-product .π₂∘factor = Nat-path λ x → refl
    prod .has-is-product .unique h p q = Nat-path (λ i j y → p j .η i y , q j .η i y)

module _ {κ} {C : Precategory κ κ} where
  private
    module C = Cat.Reasoning C
    module PSh = Cat.Reasoning (PSh κ C)

  PSh-closed : is-cc (PSh κ C)
  PSh-closed = cc where
    cat = PSh κ C

    open Cartesian cat (PSh-products {C = C}) public

    module _ (A : PSh.Ob) where
      module A = Functor A

      hom₀ : PSh.Ob → PSh.Ob
      hom₀ B = F where
        module B = Functor B
        F : PSh.Ob
        F .F₀ c = (よ₀ C c ⊗ A) => B , Nat-is-set
        F .F₁ f nt .η i (g , x) = nt .η i (f C.∘ g , x)
        F .F₁ f nt .is-natural x y g = funext λ o →
          ap (nt .η y) (Σ-pathp (C.assoc _ _ _) refl) ∙ happly (nt .is-natural _ _ _) _
        F .F-id = funext λ f → Nat-path $ λ i → funext $ λ (g , x) →
          ap (f .η i) (Σ-pathp (C.idl _) refl)
        F .F-∘ f g = funext λ h → Nat-path $ λ i → funext $ λ (j , x) →
          ap (h .η i) (Σ-pathp (sym (C.assoc _ _ _)) refl)

      func : Functor (PSh κ C) (PSh κ C)
      func .F₀ = hom₀
      func .F₁ f .η i g .η j (h , x) = f .η _ (g .η _ (h , x))
      func .F₁ f .η i g .is-natural x y h = funext λ x →
        ap (f .η _) (happly (g .is-natural _ _ _) _) ∙ happly (f .is-natural _ _ _) _
      func .F₁ nt .is-natural x y f = funext λ h → Nat-path λ _ → refl
      func .F-id = Nat-path λ x → funext λ _ → Nat-path λ _ → funext λ _ → refl
      func .F-∘ f g = Nat-path λ x → funext λ _ → Nat-path λ _ → funext λ _ → refl

      adj : _ ⊣ func
      adj .unit .η x .η i a =
        NT (λ j (h , b) → x .F₁ h a , b) λ _ _ _ →
          funext λ _ → Σ-pathp (happly (x .F-∘ _ _) _) refl
      adj .unit .η x .is-natural _ _ _ = funext λ _ → Nat-path λ _ → funext λ _ →
        Σ-pathp (sym (happly (x .F-∘ _ _) _)) refl
      adj .unit .is-natural x y f = Nat-path λ _ → funext λ _ → Nat-path λ _ → funext λ _ →
        Σ-pathp (sym (happly (f .is-natural _ _ _) _)) refl
      adj .counit .η _ .η _ x = x .fst .η _ (C.id , x .snd)
      adj .counit .η _ .is-natural x y f = funext λ h →
        ap (h .fst .η _) (Σ-pathp C.id-comm refl) ∙ happly (h .fst .is-natural _ _ _) _
      adj .counit .is-natural x y f = Nat-path λ x → refl
      adj .zig {A} = Nat-path λ x → funext λ _ → Σ-pathp (happly (F-id A) _) refl
      adj .zag {A} = Nat-path λ f → funext λ x → Nat-path λ g → funext λ y →
        ap (x .η _) (Σ-pathp (C.idr _) refl)

    cc : is-cc _
    cc .is-cc.cartesian = PSh-products {C = C}
    cc .is-cc.terminal = PSh-terminal {C = C}
    cc .is-cc.[_,-] = func
    cc .is-cc.tensor⊣hom = adj
