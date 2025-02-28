<!--
```agda
open import Cat.Diagram.Exponential
open import Cat.Instances.Functor
open import Cat.Diagram.Product
open import Cat.Functor.Adjoint
open import Cat.Functor.Hom
open import Cat.Prelude

open import Data.Sum

import Cat.Instances.Presheaf.Limits as Lim
import Cat.Functor.Bifunctor as Bifunctor
import Cat.Reasoning as Cat
```
-->

```agda
module Cat.Instances.Presheaf.Exponentials {ℓ} (C : Precategory ℓ ℓ) where
```

<!--
```agda
private
  module C = Cat C
  module PSh = Cat (PSh ℓ C)

open Lim ℓ C

open Binary-products (PSh ℓ C) PSh-products
open Functor
open _=>_
open _⊣_
```
-->

<!--
```agda
module _ (A B : ⌞ PSh.Ob ⌟) where
  private
    module A = Functor A
    module B = Functor B
```
-->

```agda
  PSh[_,_] : PSh.Ob
  PSh[_,_] .F₀ c = el ((よ₀ C c ⊗₀ A) => B) Nat-is-set
  PSh[_,_] .F₁ f nt .η i (g , x) = nt .η i (f C.∘ g , x)
  PSh[_,_] .F₁ f nt .is-natural x y g = funext λ o →
    ap (nt .η y) (Σ-pathp (C.assoc _ _ _) refl) ∙ happly (nt .is-natural _ _ _) _
  PSh[_,_] .F-id = ext λ f i g x →
    ap (f .η i) (Σ-pathp (C.idl _) refl)
  PSh[_,_] .F-∘ f g = ext λ h i j x →
    ap (h .η i) (Σ-pathp (sym (C.assoc _ _ _)) refl)
```

```agda
PSh-closed : Cartesian-closed (PSh ℓ C) PSh-products PSh-terminal
PSh-closed = cc where
  cat = PSh ℓ C

  module _ (A : PSh.Ob) where
    func : Functor (PSh ℓ C) (PSh ℓ C)
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
    adj .unit .η x .is-natural _ _ _ = ext λ _ _ _ _ → sym (x .F-∘ _ _ # _) ,ₚ refl
    adj .unit .is-natural x y f = ext λ _ _ _ _ _ → sym (f .is-natural _ _ _ $ₚ _) ,ₚ refl
    adj .counit .η _ .η _ x = x .fst .η _ (C.id , x .snd)
    adj .counit .η _ .is-natural x y f = funext λ h →
      ap (h .fst .η _) (Σ-pathp C.id-comm refl) ∙ happly (h .fst .is-natural _ _ _) _
    adj .counit .is-natural x y f = trivial!
    adj .zig {A} = ext λ x _ _ → happly (F-id A) _ ,ₚ refl
    adj .zag {A} = ext λ _ x i f g j → x .η i (C.idr f j , g)

  cc : Cartesian-closed (PSh ℓ C) PSh-products PSh-terminal
  cc = product-adjoint→cartesian-closed (PSh ℓ C) _ _ func adj
```
