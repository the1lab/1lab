<!--
```agda
open import Cat.Instances.Product
open import Cat.Functor.Constant
open import Cat.Functor.Compose
open import Cat.Prelude

import Cat.Functor.Reasoning
import Cat.Reasoning

open Precategory
open Functor
open _=>_
```
-->

```agda
module Cat.Instances.Functor where

private variable
  o h o₁ h₁ o₂ h₂ : Level
  B C D E : Precategory o h
  F G : Functor C D
```

# Functor (pre)categories

```agda
open import Cat.Functor.Base public
```

## Functor categories

When the codomain category $D$ is [[univalent|univalent category]], then
so is the category of functors $[C,D]$. Essentially, this can be read as
saying that "naturally isomorphic functors are identified". We begin by
proving that the components of a natural isomorphism (a natural
transformation with natural inverse) are themselves isomorphisms in $D$.

```agda
open import Cat.Functor.Univalence public
```

## Constant diagrams

There is a functor from $\cC$ to $[\cJ, \cC]$ that takes an object
$x : \cC$ to the constant functor $j \mapsto x$.

<!--
```agda
module _ {o ℓ o' ℓ'} {C : Precategory o ℓ} {J : Precategory o' ℓ'} where
  private module C = Precategory C
  private module J = Precategory J
```
-->

```agda
  ConstD : Functor C Cat[ J , C ]
  ConstD .F₀ x = Const x
  ConstD .F₁ f = constⁿ f
  ConstD .F-id = ext λ _ → refl
  ConstD .F-∘ f g = ext λ _ → refl
```


<!--
```agda
F∘-assoc
  : ∀ {o ℓ o' ℓ' o'' ℓ'' o₃ ℓ₃}
      {C : Precategory o ℓ} {D : Precategory o' ℓ'} {E : Precategory o'' ℓ''} {F : Precategory o₃ ℓ₃}
      {F : Functor E F} {G : Functor D E} {H : Functor C D}
  → F F∘ (G F∘ H) ≡ (F F∘ G) F∘ H
F∘-assoc = Functor-path (λ x → refl) λ x → refl

F∘-idl
  : ∀ {o'' ℓ'' o₃ ℓ₃}
      {E : Precategory o'' ℓ''} {E' : Precategory o₃ ℓ₃}
      {F : Functor E E'}
  → Id F∘ F ≡ F
F∘-idl = Functor-path (λ x → refl) λ x → refl

F∘-idr
  : ∀ {o'' ℓ'' o₃ ℓ₃}
      {E : Precategory o'' ℓ''} {E' : Precategory o₃ ℓ₃}
      {F : Functor E E'}
  → F F∘ Id ≡ F
F∘-idr = Functor-path (λ x → refl) λ x → refl

module
  _ {o ℓ o' ℓ' o'' ℓ''}
    {C : Precategory o ℓ} {D : Precategory o' ℓ'} {E : Precategory o'' ℓ''}
  where
    private
      module CD = Cat.Reasoning Cat[ C , D ]
      module DE = Cat.Reasoning Cat[ D , E ]
      module CE = Cat.Reasoning Cat[ C , E ]

    F∘-iso-l : {F F' : Functor D E} {G : Functor C D}
             → F DE.≅ F' → (F F∘ G) CE.≅ (F' F∘ G)
    F∘-iso-l {F} {F'} {G} isom =
      CE.make-iso (isom.to ◂ G) (isom.from ◂ G)
        (ext λ x → isom.invl #ₚ _)
        (ext λ x → isom.invr #ₚ _)
      where
        module isom = DE._≅_ isom

    F∘-iso-r : {F : Functor D E} {G G' : Functor C D}
             → G CD.≅ G' → (F F∘ G) CE.≅ (F F∘ G')
    F∘-iso-r {F} {G} {G'} isom =
      CE.make-iso (F ▸ isom.to) (F ▸ isom.from)
        (ext λ x → F.annihilate (isom.invl ηₚ _))
        (ext λ x → F.annihilate (isom.invr ηₚ _))
      where
        module isom = CD._≅_ isom
        module F = Cat.Functor.Reasoning F

open import Cat.Functor.Naturality public

module
  _ {o ℓ o' ℓ'}
    {C : Precategory o ℓ} {D : Precategory o' ℓ'}
  where

  private
    module DD = Cat.Reasoning Cat[ D , D ]
    module CD = Cat.Reasoning Cat[ C , D ]
    module D = Cat.Reasoning D
    module C = Cat.Reasoning C

  F∘-iso-id-l
    : {F : Functor D D} {G : Functor C D}
    → F ≅ⁿ Id → (F F∘ G) ≅ⁿ G
  F∘-iso-id-l {F} {G} isom = subst ((F F∘ G) CD.≅_) F∘-idl (F∘-iso-l isom)

open _=>_

_ni^op : F ≅ⁿ G → Functor.op F ≅ⁿ Functor.op G
_ni^op α = Cat.Reasoning.make-iso _
  (_=>_.op (Isoⁿ.from α)) (_=>_.op (Isoⁿ.to α))
  (reext! (Isoⁿ.invl α)) (reext! (Isoⁿ.invr α))

module _ {o ℓ κ} {C : Precategory o ℓ} where
  open Functor
  open _=>_

  natural-iso-to-is-equiv
    : {F G : Functor C (Sets κ)}
    → (eta : F ≅ⁿ G)
    → ∀ x → is-equiv (Isoⁿ.to eta .η x)
  natural-iso-to-is-equiv eta x = is-iso→is-equiv $ iso
    (Isoⁿ.from eta .η x)
    (λ x i → Isoⁿ.invl eta i .η _ x)
    (λ x i → Isoⁿ.invr eta i .η _ x)

  natural-iso-from-is-equiv
    : {F G : Functor C (Sets κ)}
    → (eta : F ≅ⁿ G)
    → ∀ x → is-equiv (Isoⁿ.from eta .η x)
  natural-iso-from-is-equiv eta x = is-iso→is-equiv $ iso
    (Isoⁿ.to eta .η x)
    (λ x i → Isoⁿ.invr eta i .η _ x)
    (λ x i → Isoⁿ.invl eta i .η _ x)

  natural-iso→equiv
    : {F G : Functor C (Sets κ)}
    → (eta : F ≅ⁿ G)
    → ∀ x → F ʻ x ≃ G ʻ x
  natural-iso→equiv eta x =
    Isoⁿ.to eta .η x ,
    natural-iso-to-is-equiv eta x
```
-->
