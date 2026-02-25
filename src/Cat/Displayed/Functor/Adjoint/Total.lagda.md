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

import Cat.Displayed.Reasoning

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

# Total adjunction

Suppose $\cE \liesover \cA$ and $\cF \liesover \cB$ are 
[[displayed categories|displayed category]], $L \dashv R : \cB \to \cA$ 
are [[adjoint functors]]. A [[displayed adjunction]] $L' \dashv R : \cF \to \cE$
induces an ordinary adjunction of the corresponding [[total functors|total functor]]
$\int L' \dashv \int R' : \int \cF \to \int \cE$.

<!--
```agda
private
  module L⊣R = _⊣_ L⊣R
  module L'⊣R' = _⊣[_]_ L'⊣R' 
  module A = Cat.Reasoning A
  module B = Cat.Reasoning B
  module ℱ = Cat.Displayed.Reasoning ℱ
  module ℰ = Cat.Displayed.Reasoning ℰ
  ∫ℱ = ∫ ℱ
  module ∫ℱ = Cat.Reasoning ∫ℱ
  ∫ℰ = ∫ ℰ
  module ∫ℰ = Cat.Reasoning ∫ℰ
  ∫ℰF = Cat[ ∫ ℰ , ∫ ℰ ]
  module ∫ℰF = Cat.Reasoning ∫ℰF
  ∫ℱF = Cat[ ∫ ℱ , ∫ ℱ ]
  module ∫ℱF = Cat.Reasoning ∫ℱF
```
-->

In both the case of the unit and counit, we take the [[total natural transformation]]
and compose with the natural isomorphisms `∫ᶠ∘`{.Agda} and `∫ᶠId'≅Id` to
adjust the domain and codomain.

```agda
∫⊣ : (∫ᶠ L') ⊣ (∫ᶠ R')
∫⊣ .unit = Iso.to ∫ᶠ∘ ∫ℰF.∘ ∫ⁿ (L'⊣R'.unit') ∫ℰF.∘ Iso.from ∫ᶠId'≅Id
∫⊣ .counit = Iso.to ∫ᶠId'≅Id ∫ℱF.∘ ∫ⁿ (L'⊣R'.counit') ∫ℱF.∘ Iso.from ∫ᶠ∘
```

The zig-zag identities follow from their displayed counterparts after
taking care of the extra identity morphisms due to `∫ᶠ∘`{.Agda} and 
`∫ᶠId'≅Id`{.Agda}.

```agda
∫⊣ .zig {(x , x')} = ∫Hom-path ℱ 
  ( (B.id B.∘ L⊣R.ε (₀ L x) B.∘ B.id) B.∘ ₁ L (A.id A.∘ L⊣R.η x A.∘ A.id) ≡⟨ ap (B._∘ ₁ L (A.id A.∘ L⊣R.η x A.∘ A.id)) (B.idlr (L⊣R.ε (₀ L x))) ⟩
    L⊣R .ε (₀ L x) B.∘ ₁ L (A.id A.∘ L⊣R.η x A.∘ A.id)                    ≡⟨ ap (λ f → L⊣R.ε (F₀ L x) B.∘ ₁ L f) (A.idlr (L⊣R.η x)) ⟩
    L⊣R .ε (₀ L x) B.∘ ₁ L (L⊣R .η x)                                     ≡⟨ L⊣R.zig ⟩
    B.id                                                                  ∎)
  $ ℱ.cast[] $
    (ℱ.id' ℱ.∘' L'⊣R'.counit'.ε' (₀' L' x') ℱ.∘' ℱ.id') 
      ℱ.∘' ₁' L' (ℰ.id' ℰ.∘' L'⊣R'.unit'.η' x' ℰ.∘' ℰ.id')                            ℱ.≡[]⟨ apd (λ i → ℱ._∘' ₁' L' (ℰ.id' ℰ.∘' L'⊣R'.unit'.η' x' ℰ.∘' ℰ.id')) (ℱ.idlr' (L'⊣R'.counit'.ε' (₀' L' x'))) ⟩ 
    L'⊣R'.counit'.ε' (₀' L' x') ℱ.∘' ₁' L' (ℰ.id' ℰ.∘' L'⊣R'.unit'.η' x' ℰ.∘' ℰ.id')  ℱ.≡[]⟨ apd (λ i f' → L'⊣R'.counit'.ε' (₀' L' x') ℱ.∘' ₁' L' f') (ℰ.idlr' (L'⊣R'.unit'.η' x')) ⟩
    L'⊣R'.counit'.ε' (₀' L' x') ℱ.∘' ₁' L' (L'⊣R'.unit'.η' x')                        ℱ.≡[]⟨ L'⊣R'.zig' ⟩ 
    ℱ.id' ∎
∫⊣ .zag {(x , x')} = ∫Hom-path ℰ 
  ( ₁ R (B.id B.∘ L⊣R.ε x B.∘ B.id) A.∘ A.id A.∘ L⊣R.η (₀ R x) A.∘ A.id   ≡⟨ ap (₁ R (B.id B.∘ L⊣R.ε x B.∘ B.id) A.∘_) (A.idlr (L⊣R.η (₀ R x))) ⟩
    ₁ R (B.id B.∘ L⊣R.ε x B.∘ B.id) A.∘ L⊣R.η (₀ R x)                     ≡⟨ ap (λ f → ₁ R f A.∘ L⊣R.η (F₀ R x)) (B.idlr (L⊣R.ε x)) ⟩
    ₁ R (L⊣R.ε x) A.∘ L⊣R.η (₀ R x)                                       ≡⟨ L⊣R.zag ⟩
    A.id ∎)
  $ ℰ.cast[] $
    ₁' R' (ℱ.id' ℱ.∘' L'⊣R'.counit'.ε' x' ℱ.∘' ℱ.id') 
      ℰ.∘' ℰ.id' ℰ.∘' L'⊣R'.unit'.η' (₀' R' x') ℰ.∘' ℰ.id'                            ℰ.≡[]⟨ apd (λ i → ₁' R' (ℱ.id' ℱ.∘' L'⊣R'.counit'.ε' x' ℱ.∘' ℱ.id') ℰ.∘'_) (ℰ.idlr' (L'⊣R'.unit'.η' (₀' R' x'))) ⟩
    ₁' R' (ℱ.id' ℱ.∘' L'⊣R'.counit'.ε' x' ℱ.∘' ℱ.id') ℰ.∘' L'⊣R'.unit'.η' (₀' R' x')  ℰ.≡[]⟨ apd (λ i f → ₁' R' f ℰ.∘' L'⊣R'.unit'.η' (₀' R' x')) (ℱ.idlr' (L'⊣R'.counit'.ε' x')) ⟩
    ₁' R' (L'⊣R'.counit'.ε' x') ℰ.∘' L'⊣R'.unit'.η' (₀' R' x')                        ℰ.≡[]⟨ L'⊣R'.zag' ⟩
    ℰ.id'                                                                             ∎
```
