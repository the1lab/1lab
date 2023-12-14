<!--
```agda
open import 1Lab.HLevel.Retracts
open import 1Lab.HLevel.Universe
open import 1Lab.Type.Sigma

open import Cat.Instances.Sets.Complete
open import Cat.Instances.Product
open import Cat.Diagram.Product
open import Cat.Displayed.Base
open import Cat.Instances.Sets
open import Cat.Prelude
open import Cat.Base
```
-->

```agda
module Cat.Displayed.Instances.TotalProduct
  {o₁ ℓ₁ o₂ ℓ₂ o₃ ℓ₃ o₄ ℓ₄}
  (C : Precategory o₁ ℓ₁)
  (D : Precategory o₂ ℓ₂)
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
  _×ᵀᴰ_ .Displayed.Hom[_]-set (f₁ , f₂) (x'₁ , x'₂) (y'₁ , y'₂) =
    ×-is-hlevel 2
    (EC.Hom[ f₁ ]-set x'₁ y'₁) (ED.Hom[ f₂ ]-set x'₂ y'₂)
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
