<!--
```agda
open import Cat.Prelude
open import Cat.Displayed.Base
open import Cat.Instances.Product
open import Cat.Bi.Base
open import Cat.Displayed.Total
open import Cat.Displayed.Functor
open import Cat.Displayed.Instances.TotalProduct
open import Cat.Displayed.Instances.DisplayedFunctor hiding (_◆'_)
open import Cat.Displayed.Morphism
open import Cat.Displayed.Functor.Naturality
import Cat.Displayed.Reasoning as DR

-- Some reference taken from https://arxiv.org/pdf/1903.01152
```
-->
```agda
module Cat.Bi.Displayed.Base where
```
<!--
```agda
open Functor
open Displayed-functor
open _=[_]=>_
open make-natural-iso[_]

module _ where
 
  compose-assocˡ' : ∀ {o o' d d' ℓ ℓ'} {O : Type o} {H : O → O → Precategory ℓ ℓ'}
                  → {O' : O → Type o'} {H' : ∀ {a b} → O' a → O' b → Displayed (H a b) d d'}
                  → {F : ∀ {A B C} → Functor (H B C ×ᶜ H A B) (H A C)}
                  → (F' : ∀ {A B C} {A' : O' A} {B' : O' B} {C' : O' C} → Displayed-functor F (H' B' C' ×ᵀᴰ H' A' B') (H' A' C'))
                  → ∀ {A B C D} {A' : O' A} {B' : O' B} {C' : O' C} {D' : O' D} 
                  → Displayed-functor (compose-assocˡ {O = O} {H = H} F) (H' C' D' ×ᵀᴰ H' B' C' ×ᵀᴰ H' A' B') (H' A' D')
  compose-assocˡ' F' .F₀' (F , G , H) = F' .F₀' (F' .F₀' (F , G) , H)
  compose-assocˡ' F' .F₁' (f , g , h) = F' .F₁' (F' .F₁' (f , g) , h)
  compose-assocˡ' {H' = H'} F' {A' = A'} {D' = D'} .F-id' = 
    cast[] (apd (λ _ → F' .F₁') (F' .F-id' ,ₚ refl) ∙[] (F' .F-id')) 
    where 
      open Displayed (H' A' D')
      open DR (H' A' D')
  compose-assocˡ' {H' = H'} F' {A' = A'} {D' = D'} .F-∘' = 
    cast[] (apd (λ _ → F' .F₁') (F' .F-∘' ,ₚ refl) ∙[] F' .F-∘')
    where 
      open Displayed (H' A' D')
      open DR (H' A' D')

  compose-assocʳ' : ∀ {o o' d d' ℓ ℓ'} {O : Type o} {H : O → O → Precategory ℓ ℓ'}
                   → {O' : O → Type o'} {H' : ∀ {a b} → O' a → O' b → Displayed (H a b) d d'}
                   → {F : ∀ {A B C} → Functor (H B C ×ᶜ H A B) (H A C)}
                   → (F' : ∀ {A B C} {A' : O' A} {B' : O' B} {C' : O' C}
                         → Displayed-functor F (H' B' C' ×ᵀᴰ H' A' B') (H' A' C'))
                   → ∀ {A B C D} {A' : O' A} {B' : O' B} {C' : O' C} {D' : O' D}
                   → Displayed-functor (compose-assocʳ {O = O} {H = H} F)
                                       (H' C' D' ×ᵀᴰ H' B' C' ×ᵀᴰ H' A' B') (H' A' D')
  compose-assocʳ' F' .F₀' (F , G , H) = F' .F₀' (F , F' .F₀' (G , H))
  compose-assocʳ' F' .F₁' (f , g , h) = F' .F₁' (f , F' .F₁' (g , h))
  compose-assocʳ' {H' = H'} F' {A' = A'} {D' = D'} .F-id' =
    cast[] (apd (λ _ → F' .F₁') (refl ,ₚ F' .F-id') ∙[] F' .F-id')
    where
      open Displayed (H' A' D')
      open DR (H' A' D')
  compose-assocʳ' {H' = H'} F' {A' = A'} {D' = D'} .F-∘' =
    cast[] (apd (λ _ → F' .F₁') (refl ,ₚ F' .F-∘') ∙[] F' .F-∘')
    where
      open Displayed (H' A' D')
      open DR (H' A' D')
```
-->
Just as a displayed category $\cE \liesover \cB$ allows us to describe categorical structure over the category $\cB$, a
displayed _bi_category $\bf{E} \liesover \bf{B}$ allows us to describe _bi_categorical structure over the _bi_category $\bf{B}$.

```agda
record Bidisplayed {o oh ℓh} (B : Prebicategory o oh ℓh) o' oh' ℓh' : Type (lsuc (o' ⊔ oh' ⊔ ℓh') ⊔ o ⊔ oh ⊔ ℓh) where
```
For each object of the base bicateogry, we have a type of displayed objects indexed over it.
```agda
  field
    Ob[_] : Ob → Type o'
```
For any two displayed objects, we have a category displayed over the $\hom$ category of their bases.
```agda
    Hom[_,_] : ∀ {A B} → Ob[ A ] → Ob[ B ] → Displayed (Hom A B) oh' ℓh'

  module Hom[] {A B} {A' : Ob[ A ]} {B' : Ob[ B ]} = Displayed (Hom[ A' , B' ])
```
The displayed objects of these displayed $\hom$ categories are the _displayed 1-cells_.
The displayed morphims are the _displayed 2-cells_.
```agda
  _[_]↦_ : ∀ {A B} → Ob[ A ] → (A ↦ B) → Ob[ B ] → Type _
  A' [ f ]↦ B' = Hom[ A' , B' ] .Displayed.Ob[_] f


  _[_]⇒_ : ∀ {A B} {f g : A ↦ B} 
         → {A' : Ob[ A ]} {B' : Ob[ B ]} 
         → A' [ f ]↦ B' → (f ⇒ g) → A' [ g ]↦ B'
         → Type _
  _[_]⇒_ {A' = A'} {B' = B'} f' α g' = Hom[ A' , B' ] .Displayed.Hom[_] α f' g'
```
We require an indentity 1-cell displayed over the identity 1-cell of the base bicategory.
```agda 
  field
    ↦id' : ∀ {x} {x' : Ob[ x ]} → x' [ id ]↦ x'
```
We get displayed identity 2-cells automatically from the displayed $\hom$ structure.
```agda 
  ⇒id' : ∀ {A B} {A' : Ob[ A ]} {B' : Ob[ B ]}
      → {f : A ↦ B} {f' : A' [ f ]↦ B'}
      → f' [ Hom.id ]⇒ f'
  ⇒id' = Hom[].id'
```
The displayed composition functor is between total products of displayed $\hom$ categories, and
lies over the composition functor of the base bicategory.
```agda
  field
    compose' : ∀ {A B C} {A' : Ob[ A ]} {B' : Ob[ B ]} {C' : Ob[ C ]} 
              → Displayed-functor compose (Hom[ B' , C' ] ×ᵀᴰ Hom[ A' , B' ]) Hom[ A' , C' ]
    
  module compose' {A} {B} {C} {A'} {B'} {C'} = Displayed-functor (compose' {A} {B} {C} {A'} {B'} {C'})
```
Displayed 1-cell and 2-cell composition proceeds in the same way.
```agda 
  _⊗'_ : ∀ {A B C A' B' C'} {f : B ↦ C} {g : A ↦ B} → (B' [ f ]↦ C') → (A' [ g ]↦ B') → A' [ f ⊗ g ]↦ C'
  _⊗'_ f' g' = compose' · (f' , g') 

  _∘'_ : ∀ {A B A' B'} {f g h : A ↦ B} 
      → {f' : A' [ f ]↦ B'} {g' : A' [ g ]↦ B'} {h' : A' [ h ]↦ B'}
      → {β : g ⇒ h} {α : f ⇒ g} 
      → g' [ β ]⇒ h' → f' [ α ]⇒ g'
      → f' [ β ∘ α ]⇒ h'
  _∘'_ = Hom[]._∘'_

  _◆'_ : ∀ {A B C A' B' C'} 
       → {f₁ f₂ : B ↦ C} {β : f₁ ⇒ f₂} 
       → {g₁ g₂ : A ↦ B} {α : g₁ ⇒ g₂}
       → {f₁' : B' [ f₁ ]↦ C'} {f₂' : B' [ f₂ ]↦ C'}
       → {g₁' : A' [ g₁ ]↦ B'} {g₂' : A' [ g₂ ]↦ B'}
       → (β' : f₁' [ β ]⇒ f₂') (α' : g₁' [ α ]⇒ g₂')
       → (f₁' ⊗' g₁') [ β ◆ α ]⇒ (f₂' ⊗' g₂') 
  _◆'_ α' β' = compose'.₁' (α' , β')

  infixr 30 _∘'_
  infixr 25 _⊗'_
  infix 35 _◀'_ _▶'_

  _▶'_ : ∀ {A B C A' B' C'} {f : B ↦ C} {g₁ g₂ : A ↦ B} {α : g₁ ⇒ g₂}
        → {g₁' : A' [ g₁ ]↦ B'} {g₂' : A' [ g₂ ]↦ B'} 
        → (f' : B' [ f ]↦ C')
        → (α' : g₁' [ α ]⇒ g₂')
        → f' ⊗' g₁' [ f ▶ α ]⇒ f' ⊗' g₂'
  _▶'_ f' α' = compose'.₁' (⇒id' , α')


  _◀'_ : ∀ {A B C A' B' C'} {g : A ↦ B} {f₁ f₂ : B ↦ C} {β : f₁ ⇒ f₂}
        → {f₁' : B' [ f₁ ]↦ C'} {f₂' : B' [ f₂ ]↦ C'} 
        → (β' : f₁' [ β ]⇒ f₂')
        → (g' : A' [ g ]↦ B')
        → f₁' ⊗' g' [ β ◀ g ]⇒ f₂' ⊗' g'
  _◀'_ β' g' = compose'.₁' (β' , ⇒id')

```
The unitors and associator are displayed isomorphims over the unitors and associator the base bicategory.
```agda 
  -- Displayed unitor and associator isos
  field
    unitor-l' : ∀ {A B} {A' : Ob[ A ]} {B' : Ob[ B ]} → _≅[_]_ Disp[ Hom[ A' , B' ] , Hom[ A' , B' ] ] Id' unitor-l (Right' compose' ↦id')
    unitor-r' : ∀ {A B} {A' : Ob[ A ]} {B' : Ob[ B ]} → _≅[_]_ Disp[ Hom[ A' , B' ] , Hom[ A' , B' ] ] Id' unitor-r (Left'  compose' ↦id')

    associator' : ∀ {A B C D} {A' : Ob[ A ]} {B' : Ob[ B ]} {C' : Ob[ C ]} {D' : Ob[ D ]}
                → _≅[_]_ Disp[ Hom[ C' , D' ] ×ᵀᴰ (Hom[ B' , C' ] ×ᵀᴰ Hom[ A' , B' ]) , Hom[ A' , D' ] ] 
                  (compose-assocˡ' {H' = Hom[_,_]}  compose') associator (compose-assocʳ' {H' = Hom[_,_]}  compose')
```
The associated displayed cell combinators proceed in the same way.
```agda
  λ←' : ∀ {A B A' B'} {f : A ↦ B} (f' : A' [ f ]↦ B') → (↦id' ⊗' f') [ λ← f ]⇒ f'
  λ←' = unitor-l' ._≅[_]_.from' .η' 

  λ→' : ∀ {A B A' B'} {f : A ↦ B}
       → (f' : A' [ f ]↦ B')
       → f' [ λ→ f ]⇒ (↦id' ⊗' f')
  λ→' = unitor-l' ._≅[_]_.to' .η'

  ρ←' : ∀ {A B A' B'} {f : A ↦ B}
       → (f' : A' [ f ]↦ B')
       → (f' ⊗' ↦id') [ ρ← f ]⇒ f'
  ρ←' = unitor-r' ._≅[_]_.from' .η'

  ρ→' : ∀ {A B A' B'} {f : A ↦ B}
       → (f' : A' [ f ]↦ B')
       → f' [ ρ→ f ]⇒ (f' ⊗' ↦id')
  ρ→' = unitor-r' ._≅[_]_.to' .η'

  ρ←nat' : ∀ {A B A' B'} {f₁ f₂ : A ↦ B} {β : f₁ ⇒ f₂}
         → {f₁' : A' [ f₁ ]↦ B'} {f₂' : A' [ f₂ ]↦ B'}
         → (β' : f₁' [ β ]⇒ f₂')
         → (ρ←' _ ∘' (β' ◀' ↦id')) Hom[].≡[ ρ←nat β ] (β' ∘' ρ←' _)
  ρ←nat' β' = unitor-r' .from' .is-natural' _ _ β'

  λ←nat' : ∀ {A B A' B'} {f₁ f₂ : A ↦ B} {β : f₁ ⇒ f₂}
         → {f₁' : A' [ f₁ ]↦ B'} {f₂' : A' [ f₂ ]↦ B'}
         → (β' : f₁' [ β ]⇒ f₂')
         → (λ←' _ ∘' (↦id' ▶' β')) Hom[].≡[ λ←nat β ] (β' ∘' λ←' _)
  λ←nat' β' = unitor-l' .from' .is-natural' _ _ β'

  ρ→nat' : ∀ {A B A' B'} {f₁ f₂ : A ↦ B} {β : f₁ ⇒ f₂}
         → {f₁' : A' [ f₁ ]↦ B'} {f₂' : A' [ f₂ ]↦ B'}
         → (β' : f₁' [ β ]⇒ f₂')
         → (ρ→' _ ∘' β') Hom[].≡[ ρ→nat β ] ((β' ◀' ↦id') ∘' ρ→' _)
  ρ→nat' β' = unitor-r' .to' .is-natural' _ _ β'

  λ→nat' : ∀ {A B A' B'} {f₁ f₂ : A ↦ B} {β : f₁ ⇒ f₂}
         → {f₁' : A' [ f₁ ]↦ B'} {f₂' : A' [ f₂ ]↦ B'}
         → (β' : f₁' [ β ]⇒ f₂')
         → (λ→' _ ∘' β') Hom[].≡[ λ→nat β ] ((↦id' ▶' β') ∘' λ→' _)
  λ→nat' β' = unitor-l' .to' .is-natural' _ _ β'

  α→' : ∀ {A B C D A' B' C' D'}
       {f : C ↦ D} {g : B ↦ C} {h : A ↦ B}
       → (f' : C' [ f ]↦ D') (g' : B' [ g ]↦ C') (h' : A' [ h ]↦ B')
       → ((f' ⊗' g') ⊗' h') [ α→ f g h ]⇒ (f' ⊗' (g' ⊗' h'))
  α→' f' g' h' = associator' ._≅[_]_.to' .η' (f' , g' , h')

  α←' : ∀ {A B C D A' B' C' D'}
       {f : C ↦ D} {g : B ↦ C} {h : A ↦ B}
       → (f' : C' [ f ]↦ D') (g' : B' [ g ]↦ C') (h' : A' [ h ]↦ B')
       → (f' ⊗' (g' ⊗' h')) [ α← f g h ]⇒ ((f' ⊗' g') ⊗' h')
  α←' f' g' h' = associator' ._≅[_]_.from' .η' (f' , g' , h')

  α←nat' : ∀ {A B C D A' B' C' D'}
         {f₁ f₂ : C ↦ D} {g₁ g₂ : B ↦ C} {h₁ h₂ : A ↦ B}
         {β : f₁ ⇒ f₂} {γ : g₁ ⇒ g₂} {δ : h₁ ⇒ h₂}
         {f₁' : C' [ f₁ ]↦ D'} {f₂' : C' [ f₂ ]↦ D'}
         {g₁' : B' [ g₁ ]↦ C'} {g₂' : B' [ g₂ ]↦ C'}
         {h₁' : A' [ h₁ ]↦ B'} {h₂' : A' [ h₂ ]↦ B'}
         → (β' : f₁' [ β ]⇒ f₂') (γ' : g₁' [ γ ]⇒ g₂') (δ' : h₁' [ δ ]⇒ h₂')
         → (α←' _ _ _ ∘' (β' ◆' (γ' ◆' δ'))) Hom[].≡[ α←nat β γ δ ]
              (((β' ◆' γ') ◆' δ') ∘' α←' _ _ _)
  α←nat' β' γ' δ' =
    associator' .from' .is-natural' (_ , _ , _) (_ , _ , _) (β' , γ' , δ')

  α→nat' : ∀ {A B C D A' B' C' D'}
         {f₁ f₂ : C ↦ D} {g₁ g₂ : B ↦ C} {h₁ h₂ : A ↦ B}
         {β : f₁ ⇒ f₂} {γ : g₁ ⇒ g₂} {δ : h₁ ⇒ h₂}
         {f₁' : C' [ f₁ ]↦ D'} {f₂' : C' [ f₂ ]↦ D'}
         {g₁' : B' [ g₁ ]↦ C'} {g₂' : B' [ g₂ ]↦ C'}
         {h₁' : A' [ h₁ ]↦ B'} {h₂' : A' [ h₂ ]↦ B'}
         → (β' : f₁' [ β ]⇒ f₂') (γ' : g₁' [ γ ]⇒ g₂') (δ' : h₁' [ δ ]⇒ h₂')
         → (α→' _ _ _ ∘' ((β' ◆' γ') ◆' δ')) Hom[].≡[ α→nat β γ δ ]
              ((β' ◆' (γ' ◆' δ')) ∘' α→' _ _ _)
  α→nat' β' γ' δ' =
    associator' .to' .is-natural' (_ , _ , _) (_ , _ , _) (β' , γ' , δ')
```
As do the triangle and pentagon identities.
```agda
  field
    triangle' 
      : ∀ {A B C A' B' C'} {f : B ↦ C} {g : A ↦ B}
      → (f' : B' [ f ]↦ C') (g' : A' [ g ]↦ B')
      → ((ρ←' f' ◀' g') ∘' α←' f' ↦id' g') Hom[].≡[ triangle f g ] (f' ▶' λ←' g')

    pentagon'
      : ∀ {A B C D E A' B' C' D' E'}
      → {f : D ↦ E} {g : C ↦ D} {h : B ↦ C} {i : A ↦ B}
      → (f' : D' [ f ]↦ E')
      → (g' : C' [ g ]↦ D')
      → (h' : B' [ h ]↦ C')
      → (i' : A' [ i ]↦ B')
      → ((α←' f' g' h' ◀' i') ∘' α←' f' (g' ⊗' h') i' ∘' (f' ▶' α←' g' h' i'))
          Hom[].≡[ pentagon f g h i ]
          (α←' (f' ⊗' g') h' i' ∘' α←' f' g' (h' ⊗' i'))
```

## The displayed bicategory of displayed categories

Displayed categories naturally assemble into a displayed biacategory over $\bf{Cat}$.
<!--
```agda 
open Bidisplayed hiding (_∘'_)
```
-->
```agda
Displayed-cat : ∀ o ℓ o' ℓ' → Bidisplayed (Cat o ℓ) _ _ _
Displayed-cat o ℓ o' ℓ' .Ob[_] C = Displayed C o' ℓ'
Displayed-cat o ℓ o' ℓ' .Hom[_,_] D E = Disp[ D , E ]
Displayed-cat o ℓ o' ℓ' .↦id' = Id'
Displayed-cat o ℓ o' ℓ' .compose' = F∘'-functor
Displayed-cat o ℓ o' ℓ' .unitor-l' {B' = B'} = to-natural-iso' ni where
  open Displayed B'
  open DR B'
  ni : make-natural-iso[ _ ] _ _
  ni .eta' x' = NT' (λ _ → id') λ _ _ _ → id-comm-sym[]
  ni .inv' x' = NT' (λ _ → id') λ _ _ _ → id-comm-sym[]
  ni .eta∘inv' x' = Nat'-path λ x'' → idl' _
  ni .inv∘eta' x' = Nat'-path λ x'' → idl' _
  ni .natural' x' y' f' = Nat'-path λ x'' → cast[] $ symP $ (idr' _ ∙[] id-comm[])

Displayed-cat o ℓ o' ℓ' .unitor-r' {B' = B'} = to-natural-iso' ni where
  open Displayed B'
  open DR B'
  ni : make-natural-iso[ _ ] _ _
  ni .eta' x' = NT' (λ _ → id') λ _ _ _ → id-comm-sym[]
  ni .inv' x' = NT' (λ _ → id') λ _ _ _ → id-comm-sym[]
  ni .eta∘inv' x' = Nat'-path λ x'' → idl' _
  ni .inv∘eta' x' = Nat'-path λ x'' → idl' _
  ni .natural' x' y' f' = Nat'-path λ x'' → cast[] $ (idl' _ ∙[] symP (idr' _ ∙[] ((y' .F-id' ⟩∘'⟨refl) ∙[] idl' _)))
  
Displayed-cat o ℓ o' ℓ' .associator' {C' = C'} {D' = D'} = to-natural-iso' ni where
  open Displayed D'
  open DR D'
  module C' = Displayed C'
  ni : make-natural-iso[ _ ] _ _ 
  ni .eta' x' = NT' (λ _ → id') λ _ _ _ → id-comm-sym[]
  ni .inv' x' = NT' (λ _ → id') λ _ _ _ → id-comm-sym[]
  ni .eta∘inv' x' = Nat'-path (λ _ → idl' _)
  ni .inv∘eta' x' = Nat'-path (λ _ → idl' _)
  ni .natural' (x₁ , x₂ , x₃) (y₁ , y₂ , y₃) (α₁ , α₂ , α₃) = Nat'-path λ z → cast[] $
    (idl' _ ∙[] symP (pushl[] _ (y₁ .F-∘')) ∙[] symP (idr' _))

Displayed-cat o ℓ o' ℓ' .triangle' {B' = B'} {C' = C'} f' g' = Nat'-path λ x' → C'.idr' _ where
  module C' = Displayed C'
Displayed-cat o ℓ o' ℓ' .pentagon' {B' = B'} {C' = C'} {D' = D'} {E' = E'} f' g' h' i' = Nat'-path λ x' → cast[] $
  (f' .F₁' (g' .F₁' (h' .F₁' B'.id')) ∘' id') ∘' (id' ∘' f' .F₁' D'.id' ∘' id') ≡[]⟨ idr' _ ⟩∘'⟨ idl' _ ⟩
  (f' .F₁' (g' .F₁' (h' .F₁' B'.id'))) ∘' (f' .F₁' D'.id' ∘' id')               ≡[]⟨ ((apd (λ _ z → f' .F₁' (g' .F₁' z)) (h' .F-id')) ⟩∘'⟨ (idr' _)) ⟩ 
  (f' .F₁' (g' .F₁' C'.id')) ∘' (f' .F₁' D'.id')                                ≡[]⟨ ((apd (λ _ → f' .F₁') (g' .F-id') ∙[] f' .F-id') ⟩∘'⟨ f' .F-id') ⟩
  id' ∘' id'                                                                    ∎
  where
    open Displayed E'
    open DR E'
    module B' = Displayed B'
    module C' = Displayed C'
    module D' = Displayed D' 
```