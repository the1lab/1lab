<!--
```agda
open import 1Lab.Equiv.Fibrewise

open import Cat.Displayed.Functor.Naturality
open import Cat.Displayed.Functor.Properties
open import Cat.Displayed.Instances.Functor
open import Cat.Displayed.Functor.Adjoint
open import Cat.Functor.Equivalence
open import Cat.Functor.Properties
open import Cat.Displayed.Functor
open import Cat.Functor.Adjoint
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Morphism.Reasoning as Dr
import Cat.Reasoning as Cr

open Displayed-functor
open _=[_]=>_
```
-->


```agda
module Cat.Displayed.Functor.Equivalence where
```

# Equivalences of displayed categories {defines="displayed-equivalence"}

Recall that we define an [[equivalence of categories]] is defined as a
special kind  of [[adjoint functor]]. Similarly, if $\cE \liesover \cA$
and $\cF \liesover \cB$ are [[displayed categories]], and $F : \cA \to \cB$
is an [[equivalence|equivalence of categories]] of the [[base categories]],
we say that a [[displayed functor]] $F' : \cE \to \cF$
over $F$ is a **displayed equivalence** over $F$ when there is a
[[displayed adjunction]] $F' \dashv_{F \dashv F^{-1}} F'^{-1}$,
where the the unit and counit are [[displayed natural isomorphisms]].

```agda
record is-equivalence[_]
```

<!--
```agda
  {oa ℓa ob ℓb oe ℓe of ℓf}
  {A : Precategory oa ℓa} {B : Precategory ob ℓb}
  {ℰ : Displayed A oe ℓe} {ℱ : Displayed B of ℓf}
  {F : Functor A B}
```
-->

```agda
  (F-is-equiv : is-equivalence F) (F' : Displayed-functor F ℰ ℱ)
  : Type (adj-level' ℰ ℱ) where

  open is-equivalence F-is-equiv public
```

<!--
```agda
  private
    module F = Functor F
    module F⁻¹ = Functor F⁻¹
    module A = Cr A
    module B = Cr B
    module ℰ = Dr ℰ
    module ℱ = Dr ℱ
    [ℰ,ℰ] = DisCat[ ℰ , ℰ ]
    [ℱ,ℱ] = DisCat[ ℱ , ℱ ]
    module [ℰ,ℰ] = Dr [ℰ,ℰ]
    module [ℱ,ℱ] = Dr [ℱ,ℱ]
    module F' = Displayed-functor F'
```
-->

```agda
  field
    F'⁻¹ : Displayed-functor F⁻¹ ℱ ℰ
    F'⊣F'⁻¹ : F' ⊣[ F⊣F⁻¹ ] F'⁻¹

  open _⊣[_]_ F'⊣F'⁻¹ public
```

<!--
```agda
  private module F'⁻¹ = Displayed-functor F'⁻¹
```
-->

```agda
  field
    unit'-iso : ∀ {x} x' →  ℰ.is-invertible[ unit-iso x ] (unit' .η' x')
    counit'-iso : ∀ {x} x' →  ℱ.is-invertible[ counit-iso x ] (counit' .η' x')
```

Again, we see that natural families of invertible morphisms give rise to
displayed isomorphisms in the [[displayed functor category]]:

```agda
  F'∘F'⁻¹≅Id' : F' F∘' F'⁻¹ [ℱ,ℱ].≅[ F∘F⁻¹≅Id ] Id'
  F'∘F'⁻¹≅Id' = [ℱ,ℱ].invertible[]→iso[]
   (invertible[]→invertibleⁿ[ _ ] counit' counit'-iso)

  Id'≅F'⁻¹∘'F' : Id' [ℰ,ℰ].≅[ Id≅F⁻¹∘F ] F'⁻¹ F∘' F'
  Id'≅F'⁻¹∘'F' = [ℰ,ℰ].invertible[]→iso[]
    (invertible[]→invertibleⁿ[ _ ] unit' unit'-iso)

  unit'⁻¹ = [ℰ,ℰ].from' Id'≅F'⁻¹∘'F'
  counit'⁻¹ = [ℱ,ℱ].from' F'∘F'⁻¹≅Id'
```

This implies the displayed adjunction

```agda
  F'⁻¹⊣F' : F'⁻¹ ⊣[ F⁻¹⊣F ] F'
```

whence we have

```agda
  inverse-equivalence' : is-equivalence[ inverse-equivalence ] F'⁻¹
```

<details>
<summary>Construction of `F'⁻¹⊣F'`{.Agda} and `inverse-equivalence'`{.Agda}</summary>
```agda
  F'⁻¹⊣F' ._⊣[_]_.unit' = counit'⁻¹
  F'⁻¹⊣F' ._⊣[_]_.counit' = unit'⁻¹
  F'⁻¹⊣F' ._⊣[_]_.zig' {b} {b'} = z' where
    z' : unit'⁻¹ .η' (F'⁻¹.₀' b') ℰ.∘' F'⁻¹.₁' (counit'⁻¹ .η' b')
      ℰ.≡[ _⊣_.zig F⁻¹⊣F ] ℰ.id'
    z' = ℰ.cast[] $ ℰ.inverse-unique₀'
      ((F'-map-iso F'⁻¹ (isoⁿ[]→iso[] F'∘F'⁻¹≅Id' b'))
        ℰ.∘Iso' isoⁿ[]→iso[] Id'≅F'⁻¹∘'F' (F'⁻¹.₀' b'))
      ℰ.id-iso↓ zag'
  F'⁻¹⊣F' ._⊣[_]_.zag' {a} {a'} = z' where
    z' : F'.₁' (unit'⁻¹ .η' a') ℱ.∘' counit'⁻¹ .η' (F'.₀' a')
      ℱ.≡[ _⊣_.zag F⁻¹⊣F ] ℱ.id'
    z' = ℱ.cast[] $ ℱ.inverse-unique₀'
      (isoⁿ[]→iso[] F'∘F'⁻¹≅Id' (F'.₀' a')
        ℱ.∘Iso' F'-map-iso F' (isoⁿ[]→iso[] Id'≅F'⁻¹∘'F' a'))
      ℱ.id-iso↓ zig'

  inverse-equivalence' = record
    { F'⁻¹ = F'
    ; F'⊣F'⁻¹ = F'⁻¹⊣F'
    ; unit'-iso = λ x' → ℱ.is-invertible[]-inverse (counit'-iso x')
    ; counit'-iso = λ x' → ℰ.is-invertible[]-inverse (unit'-iso x') }
```
</details>

As with an ordinary [[equivalence of categories]] there are other ways
of characterising displayed equivalences which will usually be more
convenient when it comes to constructing equivalences by hand.

## Fully faithful, essentially surjective

Here we give the displayed analogue of `ff+split-eso→is-equivalence`{.Agda},
requiring a similarly Herculean effort. Suppose $F' : \cE \to_F \cF$
is a displayed functor over a [[fully faithful]] and [[split essentially
surjective]] base functor $F : \cA \to \cB$, so that $F'$ is [[fully
faithfully displayed]] and [[essentially split surjective over]] $F$.

```agda
module _
```

<!--
```agda
  {oa ℓa ob ℓb oe ℓe of ℓf}
  {A : Precategory oa ℓa} {B : Precategory ob ℓb}
  {ℰ : Displayed A oe ℓe} {ℱ : Displayed B of ℓf}
  {F : Functor A B} {F' : Displayed-functor F ℰ ℱ}
```
-->

```agda
  (ff : is-fully-faithful F) {eso : is-split-eso F}
  (ff' : is-ff[] F') (eso' : is-split-eso[ eso ] F')
  where

  private module ff[ff]+split-eso[]→is-equivalence[] where
    F-is-equiv = ff+split-eso→is-equivalence {F = F} ff eso
    open is-equivalence F-is-equiv
```

<!--
```agda
    module A = Cr A
    module B = Cr B
    module ℰ = Dr ℰ
    module ℱ = Dr ℱ
    module F = Functor F
    module F' = Displayed-functor F'
    module F⁻¹ = Functor F⁻¹
    module ff {x} {y} = Equiv (F.F₁ , ff {x} {y})
```
-->

We can use the inverse action `ff'⁻¹`{.Agda} together with essential
surjectivity to define `F'⁻¹`{.Agda}:

```agda
    open ff[ff] F' ff ff'

    F'⁻¹ : Displayed-functor F⁻¹ ℱ ℰ
    F'⁻¹ .F₀' b' = eso' b' .fst

    F'⁻¹ .F₁' {x} {y} {f} {x'} {y'} f' = ff'⁻¹ (ffy' ℱ.∘' f' ℱ.∘' ftx') where
      open Σ (eso' x') renaming (fst to f*x' ; snd to f*x'-iso)
      open Σ (eso' y') renaming (fst to f*y' ; snd to f*y'-iso)
      ftx' = f*x'-iso .ℱ.to'
      ffy' = f*y'-iso .ℱ.from'

    F'⁻¹ .F-id' {x} {x'} = ℰ.begin[]
      ff'⁻¹ (ffx' ℱ.∘' ℱ.id' ℱ.∘' ftx') ℰ.≡[]⟨ apd (λ _ f' → ff'⁻¹ (ffx' ℱ.∘' f')) (ℱ.idl' ftx') ⟩
      ff'⁻¹ (ffx' ℱ.∘' ftx')            ℰ.≡[]⟨ apd (λ _ → ff'⁻¹) (f*x'-iso.invr') ⟩
      ff'⁻¹ ℱ.id'                       ℰ.≡[]˘⟨ apd (λ _ → ff'⁻¹) (F' .F-id') ⟩
      ff'⁻¹ (F'.₁' ℰ.id')               ℰ.≡[]⟨ η[] ℰ.id' ⟩
      ℰ.id'                             ℰ.∎[]
      where
        open Σ (eso' x') renaming (fst to f*x' ; snd to f*x'-iso)
        module f*x'-iso = ℱ._≅[_]_ f*x'-iso
        ftx' = f*x'-iso.to'
        ffx' = f*x'-iso.from'


    F'⁻¹ .F-∘' {a' = x'} {y'} {z'} {f'} {g'} = ff[]→faithful[] F' ff' $ ℱ.begin[]
      F'.₁' (ff'⁻¹ (ffz' ℱ.∘' (f' ℱ.∘' g') ℱ.∘' ftx'))                                    ℱ.≡[]⟨ ε[] (ffz' ℱ.∘' (f' ℱ.∘' g') ℱ.∘' ftx') ⟩
      ffz' ℱ.∘' (f' ℱ.∘' g') ℱ.∘' ftx'                                                    ℱ.≡[]˘⟨ apd (λ _ → ffz' ℱ.∘'_) (ℱ.assoc' f' g' ftx') ⟩
      ffz' ℱ.∘' f' ℱ.∘' g' ℱ.∘' ftx'                                                      ℱ.≡[]˘⟨ apd (λ _ h' → ffz' ℱ.∘' f' ℱ.∘' h') (ℱ.idl' (g' ℱ.∘' ftx')) ⟩
      ffz' ℱ.∘' f' ℱ.∘' ℱ.id' ℱ.∘' g' ℱ.∘' ftx'                                           ℱ.≡[]˘⟨ apd (λ _ h' → ffz' ℱ.∘' f' ℱ.∘' h' ℱ.∘' g' ℱ.∘' ftx')  (f*y'-iso .ℱ.invl') ⟩
      ffz' ℱ.∘' f' ℱ.∘' (fty' ℱ.∘' ffy') ℱ.∘' g' ℱ.∘' ftx'                                ℱ.≡[]˘⟨ apd (λ _ h' → ffz' ℱ.∘' f' ℱ.∘' h') (ℱ.assoc' fty' ffy' (g' ℱ.∘' ftx')) ⟩
      ffz' ℱ.∘' f' ℱ.∘' fty' ℱ.∘' (ffy' ℱ.∘' g' ℱ.∘' ftx')                                ℱ.≡[]⟨ apd (λ _ → ffz' ℱ.∘'_) (ℱ.assoc' f' fty' (ffy' ℱ.∘' g' ℱ.∘' ftx'))⟩
      ffz' ℱ.∘' (f' ℱ.∘' fty') ℱ.∘' (ffy' ℱ.∘' g' ℱ.∘' ftx')                              ℱ.≡[]⟨ ℱ.assoc' ffz' (f' ℱ.∘' fty') (ffy' ℱ.∘' g' ℱ.∘' ftx') ⟩
      (ffz' ℱ.∘' f' ℱ.∘' fty') ℱ.∘' (ffy' ℱ.∘' g' ℱ.∘' ftx')                              ℱ.≡[]˘⟨ apd (λ _ → ℱ._∘' (ffy' ℱ.∘' g' ℱ.∘' ftx')) (ε[] (ffz' ℱ.∘' f' ℱ.∘' fty')) ⟩
      F'.₁' (ff'⁻¹ (ffz' ℱ.∘' f' ℱ.∘' fty')) ℱ.∘' (ffy' ℱ.∘' g' ℱ.∘' ftx')                ℱ.≡[]˘⟨ apd (λ _ → F'.₁' (ff'⁻¹ (ffz' ℱ.∘' f' ℱ.∘' fty')) ℱ.∘'_) (ε[] (ffy' ℱ.∘' g' ℱ.∘' ftx')) ⟩
      F'.₁' (ff'⁻¹ (ffz' ℱ.∘' f' ℱ.∘' fty')) ℱ.∘' F'.₁' (ff'⁻¹ (ffy' ℱ.∘' g' ℱ.∘' ftx'))  ℱ.≡[]˘⟨ F' .F-∘' {f' = (ff'⁻¹ (ffz' ℱ.∘' f' ℱ.∘' fty'))} {g' = (ff'⁻¹ (ffy' ℱ.∘' g' ℱ.∘' ftx'))}⟩
      F'.₁' (ff'⁻¹ (ffz' ℱ.∘' f' ℱ.∘' fty') ℰ.∘' ff'⁻¹ (ffy' ℱ.∘' g' ℱ.∘' ftx'))          ℱ.∎[]
      where
        open Σ (eso' x') renaming (fst to f*x' ; snd to f*x'-iso)
        open Σ (eso' y') renaming (fst to f*y' ; snd to f*y'-iso)
        open Σ (eso' z') renaming (fst to f*z' ; snd to f*z'-iso)
        ffz' = f*z'-iso .ℱ.from'
        ffy' = f*y'-iso .ℱ.from'
        ftz' = f*z'-iso .ℱ.to'
        fty' = f*y'-iso .ℱ.to'
        ffx' = f*x'-iso .ℱ.from'
        ftx' = f*x'-iso .ℱ.to'
```

<details>
<summary>Defining the displayed unit, counit, and associated identities
are all given by straightforward (if tedious) adaptions of those for
`ff+split-eso→is-equivalence`{.Agda}, and are given without commentary.
</summary>
```agda
    module F'⁻¹ = Displayed-functor F'⁻¹

    module F'⊣F'⁻¹ where
      open _=[_]=>_

      unit' : Id' =[ unit ]=> F'⁻¹ F∘' F'
      unit' .η' x' = ff'⁻¹ ffx' where
        open Σ (eso' (F'.₀' x')) renaming (fst to f*x' ; snd to f*x'-iso)
        ffx' = f*x'-iso .ℱ.from'

      unit' .is-natural' x' y' f' = ff[]→faithful[] F' ff' $ ℱ.begin[]
        F'.₁' (η'y' ℰ.∘' f')                                                  ℱ.≡[]⟨ F'.F-∘' ⟩
        F'.₁' (ff'⁻¹ ffy') ℱ.∘' F'.₁' f'                                      ℱ.≡[]⟨ ε[] ffy' ℱ.⟩∘'⟨refl ⟩
        ffy' ℱ.∘' F'.₁' f'                                                    ℱ.≡[]˘⟨ ℱ.refl⟩∘'⟨ ℱ.idr' _ ⟩
        ffy' ℱ.∘' F'.₁' f' ℱ.∘' ℱ.id'                                         ℱ.≡[]˘⟨ ℱ.refl⟩∘'⟨ ℱ.refl⟩∘'⟨ f*x'-iso.invl' ⟩
        ffy' ℱ.∘' F'.₁' f' ℱ.∘' ftx' ℱ.∘' ffx'                                ℱ.≡[]⟨ (ℱ.refl⟩∘'⟨ ℱ.assoc' _ _ _ ) ℱ.∙[]  ℱ.assoc' _ _ _ ⟩
        (ffy' ℱ.∘' F'.₁' f' ℱ.∘' ftx') ℱ.∘' ffx'                              ℱ.≡[]˘⟨ ε[] _ ℱ.⟩∘'⟨ ε[] _ ⟩
        F'.₁' (ff'⁻¹ (ffy' ℱ.∘' F'.₁' f' ℱ.∘' ftx')) ℱ.∘' F'.₁' (ff'⁻¹ ffx')  ℱ.≡[]˘⟨ F'.F-∘' ⟩
        F'.₁' (₁' (F'⁻¹ F∘' F') f' ℰ.∘' η'x')                                 ℱ.∎[]
        where
          open Σ (eso' (F'.₀' x')) renaming (fst to f*x' ; snd to f*x'-iso)
          open Σ (eso' (F'.₀' y')) renaming (fst to f*y' ; snd to f*y'-iso)
          module f*x'-iso = ℱ._≅[_]_ f*x'-iso
          module f*y'-iso = ℱ._≅[_]_ f*y'-iso
          ffx' = f*x'-iso.from'
          ffy' = f*y'-iso.from'
          ftx' = f*x'-iso.to'
          η'x' = unit' .η' x'
          η'y' = unit' .η' y'

      counit' : F' F∘' F'⁻¹ =[ counit ]=> Id'
      counit' .η' x' = ftx' where
        open Σ (eso' x') renaming (fst to f*x' ; snd to f*x'-iso)
        ftx' = f*x'-iso .ℱ.to'

      counit' .is-natural' x' y' f' = ℱ.begin[]
        fty' ℱ.∘' F'.₁' (ff'⁻¹ (ffy' ℱ.∘' f' ℱ.∘' ftx'))  ℱ.≡[]⟨ ℱ.refl⟩∘'⟨ ε[] _ ⟩
        fty' ℱ.∘' ffy' ℱ.∘' f' ℱ.∘' ftx'                  ℱ.≡[]⟨ ℱ.cancell[] _ f*y'-iso.invl' ⟩
        f' ℱ.∘' ftx'                                      ℱ.∎[]
        where
          open Σ (eso' x') renaming (fst to f*x' ; snd to f*x'-iso)
          open Σ (eso' y') renaming (fst to f*y' ; snd to f*y'-iso)
          module f*x'-iso = ℱ._≅[_]_ f*x'-iso
          module f*y'-iso = ℱ._≅[_]_ f*y'-iso
          ffy' = f*y'-iso.from'
          ftx' = f*x'-iso.to'
          fty' = f*y'-iso.to'

      zig'
        : ∀ {x} {x' : ℰ.Ob[ x ]}
        → counit' .η' (F'.₀' x') ℱ.∘' F'.₁' (unit' .η' x') ℱ.≡[ zig ] ℱ.id'
      zig' {x' = x'} = ℱ.begin[]
        ftx' ℱ.∘' F'.₁' (ff'⁻¹ ffx')  ℱ.≡[]⟨ ℱ.refl⟩∘'⟨ ε[] _ ⟩
        ftx' ℱ.∘' ffx'                ℱ.≡[]⟨ f*x'-iso.invl' ⟩
        ℱ.id'                         ℱ.∎[]
        where
          open Σ (eso' (F'.₀' x')) renaming (fst to f*x' ; snd to f*x'-iso)
          module f*x'-iso = ℱ._≅[_]_ f*x'-iso
          ftx' = f*x'-iso.to'
          ffx' = f*x'-iso.from'

      zag'
        : ∀ {x} {x' : ℱ.Ob[ x ]}
        → F'⁻¹.₁' (counit' .η' x') ℰ.∘' unit' .η' (F'⁻¹.₀' x') ℰ.≡[ zag ] ℰ.id'
      zag' {x' = x'} = ff[]→faithful[] F' ff' $ ℱ.begin[]
        F'.₁' (ff'⁻¹ (ffx' ℱ.∘' ftx' ℱ.∘' fftx') ℰ.∘' ff'⁻¹ fffx')            ℱ.≡[]⟨ F'.F-∘' ⟩
        F'.F₁' (ff'⁻¹ (ffx' ℱ.∘' ftx' ℱ.∘' fftx')) ℱ.∘' F'.F₁' (ff'⁻¹ fffx')  ℱ.≡[]⟨ ε[] _ ℱ.⟩∘'⟨ ε[] _ ⟩
        (ffx' ℱ.∘' ftx' ℱ.∘' fftx') ℱ.∘' fffx'                                ℱ.≡[]⟨ (ℱ.assoc' _ _ _ ℱ.⟩∘'⟨refl) ⟩
        ((ffx' ℱ.∘' ftx') ℱ.∘' fftx') ℱ.∘' fffx'                              ℱ.≡[]˘⟨ ℱ.assoc' _ _ _ ⟩
        (ffx' ℱ.∘' ftx') ℱ.∘' (fftx' ℱ.∘' fffx')                              ℱ.≡[]⟨ f*x'-iso.invr' ℱ.⟩∘'⟨ f*f*x'-iso.invl' ⟩
        ℱ.id' ℱ.∘' ℱ.id'                                                      ℱ.≡[]⟨ ℱ.idl' _ ⟩
        ℱ.id'                                                                 ℱ.≡[]˘⟨ F'.F-id' ⟩
        F'.₁' ℰ.id'                                                           ℱ.∎[]
        where
          open Σ (eso' x') renaming (fst to f*x' ; snd to f*x'-iso)
          open Σ (eso' (F'.₀' f*x')) renaming (fst to f*f*x' ; snd to f*f*x'-iso)
          module f*x'-iso = ℱ._≅[_]_ f*x'-iso
          module f*f*x'-iso = ℱ._≅[_]_ f*f*x'-iso
          ftx' = f*x'-iso.to'
          ffx' = f*x'-iso.from'
          fftx' = f*f*x'-iso.to'
          fffx' = f*f*x'-iso.from'

    open F'⊣F'⁻¹

    F'⊣F'⁻¹ : F' ⊣[ F⊣F⁻¹ ] F'⁻¹
    F'⊣F'⁻¹ = record { F'⊣F'⁻¹ }

    unit'-iso : ∀ {x} x' → ℰ.is-invertible[ unit-iso x ] (unit' .η' x')
    unit'-iso x' = record
      { inv' = ff'⁻¹ ftx'
      ; inverses' = record
        { invl' = ff[]→faithful[] F' ff' $ ℱ.begin[]
          F'.₁' (ff'⁻¹ ffx' ℰ.∘' ff'⁻¹ ftx')          ℱ.≡[]⟨ F'.F-∘' ⟩
          F'.₁' (ff'⁻¹ ffx') ℱ.∘' F'.₁' (ff'⁻¹ ftx')  ℱ.≡[]⟨ ε[] _ ℱ.⟩∘'⟨ ε[] _ ⟩
          ffx' ℱ.∘' ftx'                              ℱ.≡[]⟨ f*x'-iso.invr' ⟩
          ℱ.id'                                       ℱ.≡[]˘⟨ F'.F-id' ⟩
          F'.₁' ℰ.id'                                 ℱ.∎[]
        ; invr' = ff[]→faithful[] F' ff' $ ℱ.begin[]
          F'.₁' (ff'⁻¹ ftx' ℰ.∘' ff'⁻¹ ffx')          ℱ.≡[]⟨ F'.F-∘' ⟩
          F'.₁' (ff'⁻¹ ftx') ℱ.∘' F'.₁' (ff'⁻¹ ffx')  ℱ.≡[]⟨ ε[] _ ℱ.⟩∘'⟨ ε[] _ ⟩
          ftx' ℱ.∘' ffx'                              ℱ.≡[]⟨ f*x'-iso.invl' ⟩
          ℱ.id'                                       ℱ.≡[]˘⟨ F'.F-id' ⟩
          F'.₁' ℰ.id' ℱ.∎[]
        }
      }
      where
        open Σ (eso' (F'.₀' x')) renaming (fst to f*x' ; snd to f*x'-iso)
        module f*x'-iso = ℱ._≅[_]_ f*x'-iso
        ftx' = f*x'-iso.to'
        ffx' = f*x'-iso.from'

    counit'-iso : ∀ {x} x' → ℱ.is-invertible[ counit-iso x ] (counit' .η' x')
    counit'-iso x' = record { f*x'-iso } where
      open Σ (eso' x') renaming (fst to f*x' ; snd to f*x'-iso)
      module f*x'-iso = ℱ._≅[_]_ f*x'-iso
```
</details>

To summarise, from the data of `ff'`{.Agda}, and `eso'`{.Agda} we are
able to construct the following

```agda
  open ff[ff]+split-eso[]→is-equivalence[]

  ff[ff]+split-eso[]→inverse = F'⁻¹
  ff[ff]+split-eso[]→unit' = F'⊣F'⁻¹.unit'
  ff[ff]+split-eso[]→counit' = F'⊣F'⁻¹.counit'
  ff[ff]+split-eso[]→F'⊣inverse' = F'⊣F'⁻¹
  ff[ff]+split-eso[]→unit'-iso = unit'-iso
  ff[ff]+split-eso[]→counit'-iso = counit'-iso
```

and thus a displayed equivalence of categories:

```agda
  ff[ff]+split-eso[]→is-equivalence[] : is-equivalence[ F-is-equiv ] F'
  ff[ff]+split-eso[]→is-equivalence[] = record { ff[ff]+split-eso[]→is-equivalence[] }
```

## Isomorphism {defines="isomorphism-of-displayed-precategories"}

When the base functor is an [[isomorphism of precategories]], a stronger
property than being an equivalence of displayed categories is being an
**isomomorphism of displayed categories**:

```agda
record is-precat-iso[_]
```

<!--
```agda
  {oa ℓa ob ℓb oe ℓe of ℓf}
  {A : Precategory oa ℓa} {B : Precategory ob ℓb}
  {ℰ : Displayed A oe ℓe} {ℱ : Displayed B of ℓf}
  {F : Functor A B}
```
-->

```agda
  (F-iso : is-precat-iso F) (F' : Displayed-functor F ℰ ℱ)
  : Type (adj-level' ℰ ℱ) where
  no-eta-equality
  constructor iso[]

  open is-precat-iso F-iso public
```

<!--
```agda
  private
    module ℰ = Dr ℰ
    module F = Functor F
    module F' = Displayed-functor F'
```
-->

```agda
  field
    has-is-ff' : is-ff[] F'
    has-is-iso' : ∀ x → is-equiv {A = ℰ.Ob[ x ]} F'.₀'
```

Apart from being fully faithfully displayed, such a functor is split
surjective on objects by `has-is-iso'`{.Agda} and therefore essentially
surjective:

```agda
module _
```

<!--
```agda
  {oa ℓa ob ℓb oe ℓe of ℓf}
  {A : Precategory oa ℓa} {B : Precategory ob ℓb}
  {ℰ : Displayed A oe ℓe} {ℱ : Displayed B of ℓf}
  {F : Functor A B} {F' : Displayed-functor F ℰ ℱ}
```
-->

```agda
  (F-iso : is-precat-iso F) (F'-iso : is-precat-iso[ F-iso ] F') where
```

<!--
```agda
  private
    module A = Cr A
    module B = Cr B
    module ℰ = Dr ℰ
    module ℱ = Dr ℱ
    module F = Functor F
    module F' = Displayed-functor F'

  open is-precat-iso[_] F'-iso
  eso = is-precat-iso→is-split-eso F-iso
  F₀≃ : A.Ob ≃ B.Ob
  F₀≃ = (F.₀ , has-is-iso)
  module F₀ = Equiv F₀≃
```
-->

```agda
  is-precat-iso[_]→is-split-eso[] : is-split-eso[ is-precat-iso→is-split-eso F-iso ] F'
  is-precat-iso[_]→is-split-eso[] {x} x' = (f*x' , f*x'-iso) where
    open Σ (eso x) renaming (fst to f*x ; snd to f*x-iso)

    f*x' = equiv→inverse (has-is-iso' (F₀.from x)) (subst ℱ.Ob[_] (sym (F₀.ε x)) x')

    p : F'.₀' f*x' ≡ subst ℱ.Ob[_] (sym (F₀.ε x)) x'
    p = equiv→counit (has-is-iso' f*x) (subst ℱ.Ob[_] (sym (F₀.ε x)) x')

    f*x'-iso = ℱ.path[ F₀.ε x ]→iso[] (to-pathp⁻ p)
```

Thus, $F$ is a displayed equivalence of displayed categories.

```agda
  is-precat-iso[_]→is-equivalence[] : is-equivalence[ is-precat-iso→is-equivalence F-iso ] F'
  is-precat-iso[_]→is-equivalence[] =
    ff[ff]+split-eso[]→is-equivalence[]
    has-is-ff has-is-ff' is-precat-iso[_]→is-split-eso[]
```
