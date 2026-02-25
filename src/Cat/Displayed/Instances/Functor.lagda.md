
<!--
```agda
open import Cat.Displayed.Reasoning as Dr
open import Cat.Displayed.Functor
open import Cat.Displayed.Base
open import Cat.Functor.Base
open import Cat.Reasoning as Cr
open import Cat.Prelude
```
--> 

```agda
module Cat.Displayed.Instances.Functor where
```

<!--
```agda
open _=>_
open _=[_]=>_
open Functor
open Displayed-functor
```
-->

# Displayed functor (pre)categories {defines="displayed-functor-category"}

Just as the [functors] between precategories $\cC$ and $\cD$ form
a precategory $[\cA , \cB]$, the [[displayed functors|displayed functor]] 
between [[displayed precategories|displayed precategory]] $\cE$ and $\cF$ 
over $\cA$ and $\cB$ form a [[displayed precategory]] $[\cE, \cF]$ over
$[\cA, \cB]$, with [[displayed natural transformations|displayed natural
transformations]] as morphisms. The construction is analogous to the 
non-displayed [[functor category]]. For instance, we define identity
displayed natural transformations by

[functors]: Cat.Functor.Base.html
[displayed functors]: Cat.Displayed.Functor.html

```agda
module _ 
  {oa ℓa ob ℓb oe ℓe of ℓf}
  {A : Precategory oa ℓa} {B : Precategory ob ℓb}
  {ℰ : Displayed A oe ℓe} {ℱ : Displayed B of ℓf}
  where

  private
    variable
      F G H : Functor A B
      F' : Displayed-functor F ℰ ℱ
      G' : Displayed-functor G ℰ ℱ
      H' : Displayed-functor H ℰ ℱ
    
    module A = Cr A
    module B = Cr B
    module ℱ = Dr ℱ
    module ℰ = Dr ℰ
```

```agda
  idnt' : F' =[ idnt ]=> F'
  idnt' .η' _ = ℱ.id'
  idnt' .is-natural' _ _ _ = ℱ.to-pathp[] ℱ.id-comm-sym[]
```

Composition of displayed natural transformations is defined by

```agda
  _∘nt'_ : ∀ {α β} → G' =[ α ]=> H' → F' =[ β ]=> G' → F' =[ α ∘nt β ]=> H'
  (α' ∘nt' β') .η' x' = α' .η' x' ℱ.∘' β' .η' x'
  _∘nt'_ {G} {G'} {H} {H'} {F} {F'} {α} {β} α' β' .is-natural' {x} {y} {f} x' y' f' = 
    (α' .η' y' ℱ.∘' β' .η' y') ℱ.∘' F₁' F' f' ℱ.≡[]⟨ ℱ.pullr' (β .is-natural x y f) (is-natural' β' x' y' f') ⟩
    α' .η' y' ℱ.∘' ₁' G' f' ℱ.∘' β' .η' x'    ℱ.≡[]⟨ ℱ.extendl' (α .is-natural x y f) (is-natural' α' x' y' f') ⟩
    ₁' H' f' ℱ.∘' α' .η' x' ℱ.∘' β' .η' x'    ∎
```

We then define the displayed category $[\cE, \cF]$ over $[\cA, \cB]$ so
that a displayed functor over $F$ is an object over $F$, and a displayed
natural transformation over $η$ is a morphism over $η$.

<!-- 
```agda
module _ 
  {oa ℓa ob ℓb oe ℓe of ℓf}
  {A : Precategory oa ℓa} {B : Precategory ob ℓb}
  (ℰ : Displayed A oe ℓe) (ℱ : Displayed B of ℓf)
  where

  private
    variable
      F G H : Functor A B
      F' : Displayed-functor F ℰ ℱ
      G' : Displayed-functor G ℰ ℱ
      H' : Displayed-functor H ℰ ℱ
    
    module A = Cr A
    module B = Cr B
    module ℱ = Dr ℱ
    module ℰ = Dr ℰ
``` 
-->

```agda
  DisCat[_,_] : Displayed Cat[ A , B ] (oa ⊔ ℓa ⊔ oe ⊔ ℓe ⊔ of ⊔ ℓf) (oa ⊔ ℓa ⊔ oe ⊔ ℓe ⊔ ℓf)
  DisCat[_,_] .Ob[_] F = Displayed-functor F ℰ ℱ
  DisCat[_,_] .Hom[_] α F' G' = F' =[ α ]=> G'
  DisCat[_,_] .Hom[_]-set α F' G' = hlevel 2

  DisCat[_,_] .id' = idnt'
  DisCat[_,_] ._∘'_ = _∘nt'_

  DisCat[_,_] .idr' α' = Nat'-path λ x' → ℱ.idr' (η' α' x')
  DisCat[_,_] .idl' α' = Nat'-path λ x' → ℱ.idl' (η' α' x')
  DisCat[_,_] .assoc' α' β' γ' = Nat'-path λ x' 
    → ℱ.assoc' (η' α' x') (η' β' x') (η' γ' x')

  DisCat[_,_] .hom[_] {x = F'} {G'} p α' = record 
    { η' = λ {x} x' → ℱ.hom[ p ηₚ x ] (α' .η' x') 
    ; is-natural' = λ {x} {y} {f} x' y' f' → ℱ.cast[] $
      ℱ.hom[ p ηₚ y ] (α' .η' y') ℱ.∘' ₁' F' f' ℱ.≡[]⟨ ℱ.unwrapl (p ηₚ y) ⟩
      α' .η' y' ℱ.∘' ₁' F' f'                   ℱ.≡[]⟨ α' .is-natural' x' y' f' ⟩
      ₁' G' f' ℱ.∘' α' .η' x'                   ℱ.≡[]⟨ ℱ.wrapr (p ηₚ x) ⟩
      ₁' G' f' ℱ.∘' ℱ.hom[ p ηₚ x ] (α' .η' x') ∎ 
    }
  DisCat[_,_] .coh[_] p α' = Nat'-path λ {x} x' → ℱ.coh[ p ηₚ x ] (η' α' x')
```
