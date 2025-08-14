<!--
```agda
open import 1Lab.HLevel.Universe
open import 1Lab.HLevel.Closure
open import 1Lab.Type.Sigma

open import Cat.Instances.Sets.Complete
open import Cat.Instances.Product
open import Cat.Diagram.Product
open import Cat.Displayed.Base
open import Cat.Instances.Sets
open import Cat.Prelude
open import Cat.Base
open import Cat.Displayed.Functor
import Cat.Functor.Bifunctor
import Cat.Displayed.Reasoning as DR

```
-->

```agda
module Cat.Displayed.Instances.TotalProduct where

module _ 
  {o₁ ℓ₁ o₂ ℓ₂ o₃ ℓ₃ o₄ ℓ₄}
  {C : Precategory o₁ ℓ₁}
  {D : Precategory o₂ ℓ₂}
  (EC : Displayed C o₃ ℓ₃) (ED : Displayed D o₄ ℓ₄) where
  private module EC = Displayed EC
  private module ED = Displayed ED
```
# The total product of displayed categories

If $\cE\to \cB$ and $q :\cD \to \cC$ are
displayed categories, then we can define their **total product**
$\cE\times \cD\to \cB\times \cC$,
which is again a displayed category.

```agda
  infixr 20 _×ᵀᴰ_
  _×ᵀᴰ_ : Displayed (C ×ᶜ D) (o₃ ⊔ o₄) (ℓ₃ ⊔ ℓ₄)
```
If displayed categories are regarded as functors, then the product of
displayed categories can be regarded as the usual product of functors.
```agda
  _×ᵀᴰ_ .Displayed.Ob[_] (p₁ , p₂) =
   EC.Ob[ p₁ ]  × ED.Ob[ p₂ ]
  _×ᵀᴰ_ .Displayed.Hom[_] (f₁ , f₂) (c₁ , c₂) (d₁ , d₂) =
    EC.Hom[ f₁ ] c₁ d₁ ×
    ED.Hom[ f₂ ] c₂ d₂
  _×ᵀᴰ_ .Displayed.id' = (EC.id' , ED.id')
```

We establish that the hom sets of the product fibration are actually
sets.

If $x, y : \operatorname{Ob}[C \times D]$
(so $x = (x_C, x_D), y = (y_C, y_D)$) and
$f : x \to y$ (so $f$ is $(f_C, f_D)$)
then for any two morphisms $f_1,f_2$ lying over $f$,
and any $p, q : f_1 = f_2$, $p=q$.

```agda
  _×ᵀᴰ_ .Displayed.Hom[_]-set _ _ _ = hlevel 2
```
Composition is pairwise.
```agda
  _×ᵀᴰ_ .Displayed._∘'_ (f₁ , f₂) (g₁ , g₂) =
    EC._∘'_ f₁ g₁ , ED._∘'_ f₂ g₂
```

Associativity and left/right identity laws hold because
they hold for the components of the ordered pairs.

```agda
  _×ᵀᴰ_ .Displayed.idr' (f₁ , f₂) = EC.idr' f₁ ,ₚ ED.idr' f₂
  _×ᵀᴰ_ .Displayed.idl' (f₁ , f₂) = EC.idl' f₁ ,ₚ ED.idl' f₂
  _×ᵀᴰ_ .Displayed.assoc' (f₁ , f₂) (g₁ , g₂) (h₁ , h₂) =
    EC.assoc' f₁ g₁ h₁ ,ₚ ED.assoc' f₂ g₂ h₂
```

```agda

module _
  {oa ℓa ob ℓb oc ℓc oa' ℓa' ob' ℓb' oc' ℓc'}
  {A : Precategory oa ℓa} {B : Precategory ob ℓb} {C : Precategory oc ℓc}
  {A' : Displayed A oa' ℓa'} {B' : Displayed B ob' ℓb'} {C' : Displayed C oc' ℓc'}
  {F : Functor (A ×ᶜ B) C}
  (F' : Displayed-functor F (A' ×ᵀᴰ B') C')
  where
  private
    module A = Precategory A
    module B = Precategory B
    module C = Precategory C
    module A' where
      open Displayed A' public
      open DR A' public
    module B' where
      open Displayed B' public
      open DR B' public
    module C' where
      open Displayed C' public
      open DR C' public
  
  open Displayed-functor F'
  open Cat.Functor.Bifunctor F

  first' : ∀ {a b a' b'} {f : A.Hom a b} {x} {x' : B'.Ob[ x ]} → A'.Hom[ f ] a' b' → C'.Hom[ first f ] (F₀' (a' , x')) (F₀' (b' , x'))
  first' f' = F₁' (f' , B'.id')

  second' : ∀ {a b a' b'} {f : B.Hom a b} {x} {x' : A'.Ob[ x ]} → B'.Hom[ f ] a' b' → C'.Hom[ second f ] (F₀' (x' , a')) (F₀' (x' , b'))
  second' f' = F₁' (A'.id' , f')

  first-id' : ∀ {a x} {a' : B'.Ob[ a ]} {x' : A'.Ob[ x ]} → first' A'.id' C'.≡[ first-id ] C'.id' {x = F₀' (x' , a')}
  first-id' = F-id'

  second-id' : ∀ {a x} {a' : A'.Ob[ a ]} {x' : B'.Ob[ x ]} → second' B'.id' C'.≡[ second-id ] C'.id' {x = F₀' (a' , x')}
  second-id' = F-id'

  first∘first' : ∀ {a b c a' b' c'} {x x'} {f : A.Hom b c} {g : A.Hom a b}
               → {f' : A'.Hom[ f ] b' c'} {g' : A'.Hom[ g ] a' b'}
               → first' {x = x} {x'} (f' A'.∘' g') C'.≡[ first∘first ] first' f' C'.∘' first' g'
  first∘first' {f' = f'} {g' = g'} = C'.cast[] $ symP $
    F₁' (f' , B'.id') C'.∘' F₁' (g' , B'.id') C'.≡[]⟨ symP F-∘' ⟩ 
    F₁' (f' A'.∘' g' , B'.id' B'.∘' B'.id')   C'.≡[]⟨ apd (λ _ e → F₁' (f' A'.∘' g' , e)) (B'.idl' _) ⟩
    F₁' (f' A'.∘' g' , B'.id')                ∎

  second∘second' : ∀ {a b c a' b' c'} {x x'} {f : B.Hom b c} {g : B.Hom a b}
                  → {f' : B'.Hom[ f ] b' c'} {g' : B'.Hom[ g ] a' b'}
                  → second' {x = x} {x'} (f' B'.∘' g')
                  C'.≡[ second∘second ]
                    second' f' C'.∘' second' g'
  second∘second' {f' = f'} {g' = g'} = C'.cast[] $ symP $
    F₁' (A'.id' , f') C'.∘' F₁' (A'.id' , g') C'.≡[]⟨ symP F-∘' ⟩
    F₁' (A'.id' A'.∘' A'.id' , f' B'.∘' g')   C'.≡[]⟨ apd (λ _ e → F₁' (e , f' B'.∘' g')) (A'.idl' _) ⟩
    F₁' (A'.id' , f' B'.∘' g')                ∎

  Left' : ∀ {y} → B'.Ob[ y ] → Displayed-functor (Left y) A' C'
  Left' y' .F₀' x' = F₀' (x' , y')
  Left' y' .F₁' = first'
  Left' y' .F-id' = F-id'
  Left' y' .F-∘' = first∘first'

  Right' : ∀ {x} → A'.Ob[ x ] → Displayed-functor (Right x) B' C'
  Right' x .F₀' y' = F₀' (x , y')
  Right' x .F₁' = second'
  Right' x .F-id' = F-id'
  Right' x .F-∘' = second∘second'
```