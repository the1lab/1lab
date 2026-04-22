<!--
```agda
open import Cat.Displayed.Functor.Properties
open import Cat.Displayed.Functor.Total
open import Cat.Functor.Properties
open import Cat.Displayed.Functor
open import Cat.Displayed.Total
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Reasoning as Dr
import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Displayed.Functor.Properties.Total
  {oa ℓa ob ℓb oe ℓe of ℓf}
  {A : Precategory oa ℓa} {B : Precategory ob ℓb}
  {ℰ : Displayed A oe ℓe} {ℱ : Displayed B of ℓf}
  {F : Functor A B}
  (F' : Displayed-functor F ℰ ℱ)
  where
```

<!--
```agda
private
  module A = Cr A
  module B = Cr B
  module ℰ = Dr ℰ
  module ℱ = Dr ℱ
  ∫ℰ = ∫ ℰ
  module ∫ℰ = Cr ∫ℰ
  ∫ℱ = ∫ ℱ
  module ∫ℱ = Cr ∫ℱ
  module F = Functor F
  module F' = Displayed-functor F'
  ∫F' = ∫ᶠ F'
  module ∫F' = Functor ∫F'
```
-->

# Properties of total functors

Here we show how [properties of a displayed functor] $F' : \cE \to \cF$
interact with the corresponding [properties of the base functor] $F :
\cA \to \cF$ to induce properties of the [[total functor]] $\int F' :
\int \cE \to \int \cF$.

[properties of a displayed functor]: Cat.Displayed.Functor.Properties.html
[properties of the base functor]: Cat.Functor.Properties.html

```agda
∫-ff : is-fully-faithful F → is-ff[] F' → is-fully-faithful ∫F'
∫-ff ff ff' {x = (x , x')} {y = (y , y')} = is-iso→is-equiv (iso inv invr invl) where
  module ff = Equiv (F.₁ {x} {y} , ff)
  open ff[ff] F' ff ff'

  inv : ∫ℱ.Hom (F.₀ x , F'.₀' x') (F.₀ y , F'.₀' y') → ∫ℰ.Hom (x , x') (y , y')
  inv (∫hom f f') = ∫hom (ff.from f) (ff'⁻¹ f')

  invr : is-right-inverse inv ∫F'.₁
  invr (∫hom f f') = ∫Hom-path ℱ (ff.ε f) (ε[] f')

  invl : is-left-inverse inv ∫F'.₁
  invl (∫hom f f') = ∫Hom-path ℰ (ff.η f) (η[] f')
```
