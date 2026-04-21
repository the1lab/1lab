<!--
```agda
open import Cat.Displayed.Functor.Adjoint.Total
open import Cat.Displayed.Functor.Equivalence
open import Cat.Displayed.Functor.Total
open import Cat.Functor.Equivalence
open import Cat.Functor.Naturality
open import Cat.Displayed.Functor
open import Cat.Displayed.Total
open import Cat.Displayed.Base
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Displayed.Morphism.Reasoning as Dr
import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Displayed.Functor.Equivalence.Total
  {oa ℓa ob ℓb oe ℓe of ℓf}
  {A : Precategory oa ℓa} {B : Precategory ob ℓb}
  {ℰ : Displayed A oe ℓe} {ℱ : Displayed B of ℓf}
  {F : Functor A B} {F' : Displayed-functor F ℰ ℱ}
  {F-is-equivalence : is-equivalence F}
  (F'-is-equivalence : is-equivalence[ F-is-equivalence ] F')
  where
```

## Total equivalence

Suppose $\cE \liesover \cA$ and $\cF \liesover \cB$ are [[displayed
categories]], $F : \cA \to \cB$ is an [[equivalence of categories]], and
$F' : \cE \to_{F} \cF$ is a [[displayed functor]]. Then if $F'$ is a
[[displayed equivalence]] over $F$, the [[total functor]]  $\int F' :
\int \cA \to \int \cB$ is an equivalence of the [[total categories]].

<!--
```agda
private
  module A = Cr A
  module B = Cr B
  module ℱ = Dr ℱ
  module ℰ = Dr ℰ
  ∫ℱ = ∫ ℱ
  module ∫ℱ = Cr ∫ℱ
  ∫ℰ = ∫ ℰ
  module ∫ℰ = Cr ∫ℰ
  ∫ℰF = Cat[ ∫ ℰ , ∫ ℰ ]
  module ∫ℰF = Cr ∫ℰF
  ∫ℱF = Cat[ ∫ ℱ , ∫ ℱ ]
  module ∫ℱF = Cr ∫ℱF

  open is-equivalence[_] F'-is-equivalence

  module F where
    open Functor F public
    module ⁻¹ = Functor F⁻¹
  module F' where
    open Displayed-functor F' public
    ⁻¹ = F'⁻¹
    module ⁻¹ = Displayed-functor ⁻¹
  ∫F' = ∫ᶠ F'
  module ∫F' = Functor ∫F'

  open _=>_
  open _=[_]=>_
```
-->

For the inverse and adjunction, we can appeal to the [[total functor]]
and [[total adjunction]] respectively.

```agda
  ∫F'⁻¹ = ∫ᶠ F'.⁻¹
  ∫F'⊣∫F'⁻¹ = ∫⊣ F'⊣F'⁻¹
```

<!--
```agda
  module ∫F'⁻¹ = Functor ∫F'⁻¹
```
-->

Recall that in order to construct the unit and counit of the total
adjunction `∫⊣`{.Agda}, we had to compose with the natural isomorphisms
`∫ᶠ∘`{.Agda} and `∫ᶠId'≅Id`{.Agda}. When the adjunction is question is
in fact an _equivalence_, all the natural transformations become
isomorphisms:

```agda
  ∫η≅ : ∀ x → x ∫ℰ.≅ ∫F'⁻¹.₀ (∫F'.₀ x)
  ∫η≅ (a , a') = isoⁿ→iso (∫ᶠ∘ {F' = F'⁻¹} {G' = F'}) (a , a')
    ∫ℰ.∘Iso iso[]→total-iso ℰ (ℰ.invertible[]→iso[] (unit'-iso a'))
    ∫ℰ.∘Iso isoⁿ→iso (∫ᶠId'≅Id ni⁻¹) (a , a')

  ∫ε≅ : ∀ x → ∫F'.₀ (∫F'⁻¹.₀ x) ∫ℱ.≅ x
  ∫ε≅ (b , b') = isoⁿ→iso ∫ᶠId'≅Id (b , b')
    ∫ℱ.∘Iso iso[]→total-iso ℱ (ℱ.invertible[]→iso[] (counit'-iso b'))
    ∫ℱ.∘Iso isoⁿ→iso (∫ᶠ∘ {F' = F'} {G' = F'⁻¹} ni⁻¹) (b , b')
```

Hence the adjunction `∫F'⊣∫F'⁻¹`{.Agda} is in fact an equivalence:

```agda
∫-equivalence : is-equivalence ∫F'
∫-equivalence = record
  { F⁻¹ = ∫F'⁻¹
  ; F⊣F⁻¹ = ∫F'⊣∫F'⁻¹
  ; has-is-equivalence = record
    { unit-iso = λ x → ∫ℰ.iso→invertible (∫η≅ x)
    ; counit-iso = λ x → ∫ℱ.iso→invertible (∫ε≅ x)
    }
  }
```
