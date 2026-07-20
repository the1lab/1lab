<!--
```agda
open import Cat.Displayed.Functor.Adjoint
open import Cat.Displayed.Functor.Total
open import Cat.Displayed.Functor
open import Cat.Displayed.Total
open import Cat.Functor.Adjoint
open import Cat.Displayed.Base
open import Cat.Functor.Base
open import Cat.Reasoning renaming (_≅_ to Iso)
open import Cat.Prelude

import Cat.Displayed.Reasoning as Dr
import Cat.Reasoning as Cr

open Displayed-functor
open Functor
open _⊣[_]_
open _⊣_
```
-->

```agda
module Cat.Displayed.Functor.Adjoint.Total
  {oa ℓa ob ℓb oe ℓe of ℓf}
  {A : Precategory oa ℓa} {B : Precategory ob ℓb}
  {ℰ : Displayed A oe ℓe} {ℱ : Displayed B of ℓf}
  {L : Functor A B} {R : Functor B A}
  {L' : Displayed-functor L ℰ ℱ} {R' : Displayed-functor R ℱ ℰ}
  {L⊣R : L ⊣ R} (L'⊣R' : L' ⊣[ L⊣R ] R')
  where
```

# Total adjunction {defines="total-adjunction"}

Suppose $\cE \liesover \cA$ and $\cF \liesover \cB$ are [[displayed
categories]], $L \dashv R : \cB \to \cA$ are [[adjoint functors]]. A
[[displayed adjunction]] $L' \dashv R' : \cF \to \cE$ induces an ordinary
adjunction of the corresponding [[total functors]] $\int L' \dashv \int
R' : \int \cF \to \int \cE$.

<!--
```agda
private
  module L⊣R = _⊣_ L⊣R
  module L'⊣R' = _⊣[_]_ L'⊣R'
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
```
-->

In both the case of the unit and counit, we take the [[total natural
transformation]] and compose with the natural isomorphisms `∫ᶠ∘`{.Agda}
and `∫ᶠId'≅Id`{.Agda} to adjust the domain and codomain.

```agda
∫⊣ : ∫ᶠ L' ⊣ ∫ᶠ R'
∫⊣ .unit = Iso.to ∫ᶠ∘ ∫ℰF.∘ ∫ⁿ (L'⊣R'.unit') ∫ℰF.∘ Iso.from ∫ᶠId'≅Id
∫⊣ .counit = Iso.to ∫ᶠId'≅Id ∫ℱF.∘ ∫ⁿ (L'⊣R'.counit') ∫ℱF.∘ Iso.from ∫ᶠ∘
```

The zig-zag identities follow from their displayed counterparts after
taking care of the extra identity morphisms due to `∫ᶠ∘`{.Agda} and
`∫ᶠId'≅Id`{.Agda}.

```agda
∫⊣ .zig {x , x'} = ∫Hom-path[]
  ⌜ ℱ.id' ℱ.∘' L'⊣R'.counit'.ε' (₀' L' x') ℱ.∘' ℱ.id' ⌝
    ℱ.∘' ₁' L' (ℰ.id' ℰ.∘' L'⊣R'.unit'.η' x' ℰ.∘' ℰ.id')                              ℱ.≡[]⟨ apd! (ℱ.idlr' (L'⊣R'.counit'.ε' (₀' L' x'))) ⟩
  L'⊣R'.counit'.ε' (₀' L' x') ℱ.∘' ₁' L' ⌜ ℰ.id' ℰ.∘' L'⊣R'.unit'.η' x' ℰ.∘' ℰ.id' ⌝  ℱ.≡[]⟨ apd! (ℰ.idlr' (L'⊣R'.unit'.η' x')) ⟩
  L'⊣R'.counit'.ε' (₀' L' x') ℱ.∘' ₁' L' (L'⊣R'.unit'.η' x')                          ℱ.≡[]⟨ L'⊣R'.zig' ⟩
  ℱ.id'                                                                               ℱ.∎[]
∫⊣ .zag {x , x'} = ∫Hom-path[]
  ₁' R' (ℱ.id' ℱ.∘' L'⊣R'.counit'.ε' x' ℱ.∘' ℱ.id')
    ℰ.∘' ⌜ ℰ.id' ℰ.∘' L'⊣R'.unit'.η' (₀' R' x') ℰ.∘' ℰ.id' ⌝                         ℰ.≡[]⟨ apd! (ℰ.idlr' (L'⊣R'.unit'.η' (₀' R' x'))) ⟩
  ₁' R' ⌜ ℱ.id' ℱ.∘' L'⊣R'.counit'.ε' x' ℱ.∘' ℱ.id' ⌝ ℰ.∘' L'⊣R'.unit'.η' (₀' R' x') ℰ.≡[]⟨ apd! (ℱ.idlr' (L'⊣R'.counit'.ε' x')) ⟩
  ₁' R' (L'⊣R'.counit'.ε' x') ℰ.∘' L'⊣R'.unit'.η' (₀' R' x')                         ℰ.≡[]⟨ L'⊣R'.zag' ⟩
  ℰ.id'                                                                              ℰ.∎[]
```
