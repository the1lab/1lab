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
```
# The Total Product of Displayed Categories

If $p : \mathbb{E}C\to C$ and $q :\mathbb{E}D\to \mathbb{D}$ are
displayed categories, then we can define their **total product**
$p \times q : \mathbb{E}C\times \mathbb{E}D\to C\times D$,
which is again a displayed category. The name

```agda
  _×ᵀᴰ_ : Displayed (C ×ᶜ D) (o₃ ⊔ o₄) (ℓ₃ ⊔ ℓ₄)
```
If displayed categories are regarded as functors, then the product of
displayed categories can be regarded as the usual product of functors.
```agda
  _×ᵀᴰ_ .Displayed.Ob[_] p =
    Displayed.Ob[ EC ] (fst p) × Displayed.Ob[ ED ] (snd p)
  _×ᵀᴰ_ .Displayed.Hom[_] c d e =
    Displayed.Hom[ EC ] (fst c) (fst d) (fst e) ×
    Displayed.Hom[ ED ] (snd c) (snd d) (snd e)
  _×ᵀᴰ_ .Displayed.id'  = ( Displayed.id' EC , Displayed.id' ED  )
```

We establish that the hom sets of the product fibration are actually
sets.

If $x, y : \operatorname{Ob}[C \times D]$
(so $x = (x_C, x_D), y = (y_C, y_D)$) and
$f : x \to y$ (so $f$ is $(f_C, f_D)$)
then for any two morphisms $f_1,f_2$ lying over $f$,
and any $p, q : f_1 = f_2$, $p=q$.

```agda
  _×ᵀᴰ_ .Displayed.Hom[_]-set f x' y' = ×-is-hlevel 2
       (Displayed.Hom[ EC ]-set (fst f) (fst x') (fst y'))
       (Displayed.Hom[ ED ]-set (snd f) (snd x') (snd y'))
```
Composition is pairwise.
```agda
  _×ᵀᴰ_ .Displayed._∘'_ f g =
    EC .Displayed._∘'_ (fst f) (fst g) ,
    ED .Displayed._∘'_ (snd f) (snd g)
```

Associativity and left/right identity laws can be proved
starting from the intuition that paths are functions from
the unit interval: a function into a product $X\times Y$ is a
pair of functions into $X$ and $Y$ respectively.

```agda
  _×ᵀᴰ_ .Displayed.idr' f = λ i →
    EC .Displayed.idr' (fst f) i , ED .Displayed.idr' (snd f) i
  _×ᵀᴰ_ .Displayed.idl' f = λ i →
    EC .Displayed.idl' (fst f) i , ED .Displayed.idl' (snd f) i
  _×ᵀᴰ_ .Displayed.assoc' f g h = λ i →
    EC .Displayed.assoc' (fst f) (fst g) (fst h) i ,
    ED .Displayed.assoc' (snd f) (snd g) (snd h) i  
```
