```agda
open import Cat.Instances.Functor.Limits
open import Cat.Instances.Sets.Complete
open import Cat.CartesianClosed.Base
open import Cat.Diagram.Limit.Finite
open import Cat.Diagram.Limit.Base
open import Cat.Instances.Functor
open import Cat.Functor.Adjoint
open import Cat.Diagram.Product
open import Cat.Instances.Sets
open import Cat.Functor.Hom
open import Cat.Prelude

import Cat.Reasoning

module Cat.CartesianClosed.Instances.PSh {ℓ} (C : Precategory ℓ ℓ) where
```

<!--
```agda
private
  module C = Cat.Reasoning C
  module PSh {κ} = Cat.Reasoning (PSh κ C)
open Functor
open _=>_
open _⊣_
```
-->

# Cartesian closed structure on presheaves

```agda
PSh-is-complete : ∀ {o ℓ} → is-complete o ℓ (PSh (o ⊔ ℓ) C)
PSh-is-complete {o} {ℓ} = Functor-cat-is-complete (Sets-is-complete {o} {ℓ} {lzero})

PSh-finitely-complete : ∀ {ℓ} → Finitely-complete (PSh ℓ C)
PSh-finitely-complete {ℓ} =
  is-complete→finitely (PSh ℓ C) (PSh-is-complete {lzero} {ℓ})

PSh-products : ∀ {ℓ} (A B : PSh.Ob) → Product (PSh ℓ C) A B
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

PSh-closed : is-cc (PSh ℓ C)
PSh-closed = cc where
  cat = PSh ℓ C

  open Cartesian cat PSh-products public

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

    func : Functor (PSh ℓ C) (PSh ℓ C)
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
  cc .is-cc.cartesian = PSh-products
  cc .is-cc.terminal = PSh-finitely-complete .Finitely-complete.terminal
  cc .is-cc.[_,-] = func
  cc .is-cc.tensor⊣hom = adj