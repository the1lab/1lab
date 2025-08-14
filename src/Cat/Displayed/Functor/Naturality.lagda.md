<!--
```agda
open import Cat.Displayed.Instances.DisplayedFunctor
open import Cat.Functor.Naturality
open import Cat.Displayed.Functor
open import Cat.Displayed.Base
open import Cat.Morphism
open import Cat.Prelude

import Cat.Displayed.Reasoning as DR
import Cat.Displayed.Morphism as DM
```
-->
We define displayed versions of the our functor naturality tech.
```agda
module Cat.Displayed.Functor.Naturality where
```
<!--
```agda
module _ 
  {ob ℓb oc ℓc od ℓd oe ℓe} 
  {B : Precategory ob ℓb} {C : Precategory oc ℓc}
  {D : Displayed B od ℓd} {E : Displayed C oe ℓe}
  where
  private
    module B = Precategory B
    module C = Precategory C
    module DE where
      open Displayed Disp[ D , E ] public
      open DR Disp[ D , E ] public 
      open DM Disp[ D , E ] public
    module D where
      open Displayed D public
      open DR D public
    module E where
      open Displayed E public
      open DR E public
    
  open Functor
  open _=>_
  open Displayed-functor
  open _=[_]=>_
```
-->
```agda

  _≅[_]ⁿ_ : {F G : Functor B C} → Displayed-functor F D E → F ≅ⁿ G → Displayed-functor G D E → Type _
  F ≅[ i ]ⁿ G = F DE.≅[ i ] G


  is-natural-transformation' 
    : {F G : Functor B C} (F' : Displayed-functor F D E) (G' : Displayed-functor G D E)
    → (α : F => G)
    → (η' : ∀ {x} (x' : D.Ob[ x ]) → E.Hom[ α .η x ] (F' .F₀' x') (G' .F₀' x'))
    → Type _
  is-natural-transformation' F' G' α η' = 
    ∀ {x y f} (x' : D.Ob[ x ]) (y' : D.Ob[ y ]) (f' : D.Hom[ f ] x' y')
        → η' y' E.∘' F' .F₁' f' E.≡[ α .is-natural x y f ] G' .F₁' f' E.∘' η' x'

  inverse-is-natural'
    : ∀ {F G : Functor B C} (iso : F ≅ⁿ G) {F' : Displayed-functor F D E} {G' : Displayed-functor G D E}
    → (α' : F' =[ iso .to ]=> G')
    → (β' : ∀ {x} (x' : D.Ob[ x ]) → E.Hom[ iso .from .η x ] (G' .F₀' x') (F' .F₀' x'))
    → (∀ {x} (x' : D.Ob[ x ]) → α' .η' x' E.∘' β' x' E.≡[ iso .invl ηₚ x ] E.id')
    → (∀ {x} (x' : D.Ob[ x ]) → β' x' E.∘' α' .η' x' E.≡[ iso .invr ηₚ x ] E.id')
    → is-natural-transformation' G' F' (iso .from) β'
  inverse-is-natural' i {F'} {G'} α' β' invl' invr' x' y' f' = E.cast[] $ 
    β' y' E.∘' G' .F₁' f'                           E.≡[]⟨ E.refl⟩∘'⟨ E.intror[] _ (invl' x') ⟩ 
    β' y' E.∘' G' .F₁' f' E.∘' α' .η' x' E.∘' β' x' E.≡[]⟨ E.refl⟩∘'⟨ E.extendl[] _ (symP (α' .is-natural' _ _ _)) ⟩
    β' y' E.∘' α' .η' y' E.∘' F' .F₁' f' E.∘' β' x' E.≡[]⟨ E.cancell[] _ (invr' _) ⟩
    F' .F₁' f' E.∘' β' x'                           ∎


  record make-natural-iso[_] {F G : Functor B C} (iso : F ≅ⁿ G) (F' : Displayed-functor F D E) (G' : Displayed-functor G D E) : Type (ob ⊔ ℓb ⊔ od ⊔ ℓd ⊔ ℓe) where
    no-eta-equality
    field
      eta' : ∀ {x} (x' : D.Ob[ x ]) → E.Hom[ iso .to .η x   ] (F' .F₀' x') (G' .F₀' x')
      inv' : ∀ {x} (x' : D.Ob[ x ]) → E.Hom[ iso .from .η x ] (G' .F₀' x') (F' .F₀' x')
      eta∘inv' : ∀ {x} (x' : D.Ob[ x ]) → eta' x' E.∘' inv' x' E.≡[ (λ i → iso .invl i .η x) ] E.id'
      inv∘eta' : ∀ {x} (x' : D.Ob[ x ]) → inv' x' E.∘' eta' x' E.≡[ (λ i → iso .invr i .η x) ] E.id'
      natural' : ∀ {x y} x' y' {f : B.Hom x y} (f' : D.Hom[ f ] x' y')
               →  eta' y' E.∘' F' .F₁' f' E.≡[ (λ i → iso .to .is-natural x y f i) ]  G' .F₁' f' E.∘' eta' x'


  open make-natural-iso[_]

  to-natural-iso' : {F G : Functor B C} {iso : F ≅ⁿ G} {F' : Displayed-functor F D E} {G' : Displayed-functor G D E}
                  → make-natural-iso[ iso ] F' G' → F' ≅[ iso ]ⁿ G'
  to-natural-iso' {iso = i} mk = 
    let to' = record { η' = mk .eta' ; is-natural' = λ {x} {y} {f} x' y' → mk .natural' x' y' } in
    record 
      { to' = to'
      ; from' = record { η' = mk .inv' ; is-natural' = inverse-is-natural' i to' (mk .inv') (mk .eta∘inv') (mk .inv∘eta') } 
      ; inverses' = record { invl' = Nat'-path (mk .eta∘inv') ; invr' = Nat'-path (mk .inv∘eta') } 
      }
```
<!--
```agda
  {-# INLINE to-natural-iso' #-}
```
-->