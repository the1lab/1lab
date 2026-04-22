<!--
```agda
open import Cat.Displayed.Functor.Properties.Total
open import Cat.Displayed.Functor.Adjoint.Total
open import Cat.Displayed.Functor.Equivalence
open import Cat.Displayed.Functor.Adjoint
open import Cat.Displayed.Functor.Total
open import Cat.Functor.Equivalence
open import Cat.Functor.Naturality
open import Cat.Functor.Properties
open import Cat.Displayed.Functor
open import Cat.Displayed.Total
open import Cat.Functor.Adjoint
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
  module F = Functor F
  module F' = Displayed-functor F'
  ∫F' = ∫ᶠ F'
  module ∫F' = Functor ∫F'
```
-->

# Total equivalence {defines="total-equivalence"}

Suppose $\cE \liesover \cA$ and $\cF \liesover \cB$ are [[displayed
categories|displayed category]], $F : \cA \to \cB$ is an [[equivalence
of categories]], and $F' : \cE \to_{F} \cF$ is a [[displayed functor]].
Then if $F'$ is a [[displayed equivalence]] over $F$, the [[total
functor]]  $\int F' : \int \cA \to \int \cB$ is an equivalence of the
[[total categories|total category]].

```agda
module _
  {F-is-equivalence : is-equivalence F}
  (F'-is-equivalence : is-equivalence[ F-is-equivalence ] F')
  where
```

<!--
```agda
  open is-equivalence[_] F'-is-equivalence
  open _=>_
  open _=[_]=>_
```
-->

For the inverse and adjunction, we can appeal to the [[total functor]]
and [[total adjunction]] respectively.

```agda
  ∫F'⁻¹ = ∫ᶠ F'⁻¹
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

## Total isomorphism {defines="total-isomorphism-of-precategories"}

If instead $F$ is an [[isomorphism of precategories]] and $F'$ is a
[[isomorphism of displayed precategories]], we similarly have that the
total functor $\int F' : \int \cE \to \int \cF$ is an isomorphism of
precategories.

```agda
module _
  {F-is-precat-iso : is-precat-iso F}
  (F'-is-precat-iso : is-precat-iso[ F-is-precat-iso ] F')
  where
```

<!--
```agda
  open is-precat-iso F-is-precat-iso
    renaming (has-is-ff to ff ; has-is-iso to F-iso)
  open is-precat-iso[_] F'-is-precat-iso
    renaming (has-is-ff' to ff' ; has-is-iso' to F'-iso)

  private
    module F₀ = Equiv (F.₀ , F-iso)
    module F₀' {a} = Equiv (F'.₀' {a} , F'-iso a)
```
-->

That $\int F'$ is fully faithful is given by `∫-ff`{.Agda}, while
showing that $\int F'$ gives an isomorphism on objects is a little more
involved.

```agda
  ∫-is-precat-iso : is-precat-iso ∫F'
  ∫-is-precat-iso = iso (∫-ff F' ff ff') (is-iso→is-equiv (iso ∫F₀'⁻¹ rinv linv)) where
    F₀'⁻¹ : ∀ {b} → ℱ.Ob[ b ] → ℰ.Ob[ F₀.from b ]
    F₀'⁻¹ {b} b' = F₀'.from $ subst ℱ.Ob[_] (sym (F₀.ε b)) b'

    ε' : ∀ {b} b' → PathP (λ i → ℱ.Ob[ F₀.ε b i ]) (F'.₀' (F₀'⁻¹ b')) b'
    ε' {b} b' = to-pathp⁻ (F₀'.ε (subst ℱ.Ob[_] (sym (F₀.ε b)) b'))

    η' : ∀ {a} a' → PathP (λ i → ℰ.Ob[ F₀.η a i ]) (F₀'⁻¹ (F'.₀' a')) a'
    η' {a} a' = to-pathp⁻ $
      F₀'.from (subst ℱ.Ob[_] (sym ⌜ F₀.ε (F.₀ a) ⌝) (F'.₀' a'))        ≡˘⟨ ap¡ (F₀.zig a) ⟩
      F₀'.from (subst (λ x → ℱ.Ob[ F.₀ x ]) (sym (F₀.η a)) (F'.₀' a'))  ≡˘⟨ subst-fibrewise (λ x → F₀'.from {x}) (sym (F₀.η a)) (F'.₀' a') ⟩
      subst ℰ.Ob[_] (sym (F₀.η a)) ⌜ F₀'.from (F'.₀' a') ⌝              ≡⟨ ap! (F₀'.η a') ⟩
      subst ℰ.Ob[_] (sym (F₀.η a)) a'                                   ∎

    ∫F₀'⁻¹ : ∫ℱ.Ob → ∫ℰ.Ob
    ∫F₀'⁻¹ (b , b') = F₀.from b , F₀'⁻¹ b'

    rinv : is-right-inverse ∫F₀'⁻¹ ∫F'.₀
    rinv (b , b') = Σ-pathp (F₀.ε b) (ε' b')

    linv : is-left-inverse ∫F₀'⁻¹ ∫F'.₀
    linv (a , a') = Σ-pathp (F₀.η a) (η' a')
```
