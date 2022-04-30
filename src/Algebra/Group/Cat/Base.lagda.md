```agda
open import Algebra.Prelude
open import Algebra.Group

open import Cat.Prelude

module Algebra.Group.Cat.Base where
```

<!--
```agda
private variable
  ℓ : Level
open Functor
import Cat.Reasoning as CR
```
-->

# The category of Groups

The category of groups, as the name implies, has its objects the
`Groups`{.Agda ident=Group}, with the morphisms between them the `group
homomorphisms`{.Agda ident=Group-hom}.

```agda
Groups : ∀ ℓ → Precategory (lsuc ℓ) ℓ
Groups ℓ = c where
  open Precategory
  open Group-hom
  open Group-on

  c : Precategory _ _
  c .Ob = Group ℓ
  c .Hom A B = Group[ A ⇒ B ]
  c .Hom-set _ (B , bg) = hlevel 2 where open Group-on bg
```

We must show that the identity is a group homomorphisms, and group homs
are closed under composition, but this follows immediately from the
properties of equality:

```agda
  c .id .fst = λ x → x
  c .id .snd = record { pres-⋆ = λ _ _ → refl }

  c ._∘_ {x} {y} {z} (f , fh) (g , gh) = (λ x → f (g x)) , fogh where abstract
    fogh : Group-hom x z (λ x → f (g x))
    fogh .pres-⋆ x y = ap f (gh .pres-⋆ x y) ∙ fh .pres-⋆ _ _

  c .idr f       = Σ-prop-path (λ _ → Group-hom-is-prop) refl
  c .idl f       = Σ-prop-path (λ _ → Group-hom-is-prop) refl
  c .assoc f g h = Σ-prop-path (λ _ → Group-hom-is-prop) refl

module Groups {ℓ} = Cat (Groups ℓ)
```

## The underlying set

The category of groups admits a `faithful`{.Agda ident=is-faithful}
functor into the category of sets, written $U : \id{Groups} \to
\sets$, which projects out the underlying set of the group. Faithfulness
of this functor says, in more specific words, that equality of group
homomorphisms can be tested by comparing the underlying morphisms of
sets.

```agda
Forget : Functor (Groups ℓ) (Sets ℓ)
Forget .F₀ (G , ggroup) = G , ggroup .Group-on.has-is-set
Forget .F₁ = fst
Forget .F-id = refl
Forget .F-∘ _ _ = refl

Forget-is-faithful : is-faithful (Forget {ℓ})
Forget-is-faithful = Σ-prop-path λ _ → Group-hom-is-prop
```

## Univalence

The [structure identity principle] already implies that identification
of groups is equivalent to isomorphism of groups. We now extend this to
proving that the category of groups is [univalent], but first we take a
detour by showing that isomorphisms in the category of groups are the
same thing as homomorphic equivalences of the groups' underlying types.

[structure identity principle]: 1Lab.Univalence.SIP.html
[univalent]: Cat.Univalent.html

```agda
Group-equiv≃Groups-iso
  : ∀ {A B : Group ℓ} → (Σ (Group≃ A B)) ≃ (A Groups.≅ B)
Group-equiv≃Groups-iso {A = A} {B = B} .fst ((f , eqv) , grh) =
  Groups.make-iso (f , grh) (equiv→inverse eqv , inv-group-hom)
    (Forget-is-faithful (funext (equiv→section eqv)))
    (Forget-is-faithful (funext (equiv→retraction eqv)))
```

To build an isomorphism given a homomorphic equivalence, we use
`Forget-is-faithful`{.Agda}, reducing equality of morphisms in
`Groups`{.Agda} to equality of morphisms in `Sets`{.Agda}. But then, the
data of an equivalence guarantees that it has a two-sided inverse, so
the only thing left to establish is that the inverse of a homomorphic
equivalence is also homomorphic:

```agda
  where
    module A = Group-on (A .snd)
    module B = Group-on (B .snd)
    open Group-hom

    g : B .fst → A .fst
    g = equiv→inverse eqv

    abstract
      inv-group-hom : Group-hom B A g
      inv-group-hom .pres-⋆ x y =
        g (x B.⋆ y)             ≡˘⟨ ap₂ (λ x y → g (x B.⋆ y)) (equiv→section eqv _) (equiv→section eqv _) ⟩
        g (f (g x) B.⋆ f (g y)) ≡˘⟨ ap g (grh .pres-⋆ _ _) ⟩
        g (f (g x A.⋆ g y))     ≡⟨ equiv→retraction eqv _ ⟩
        g x A.⋆ g y             ∎
```

<!--
```agda
Group-equiv≃Groups-iso .snd = is-iso→is-equiv isic where
  open is-iso
  open Groups._≅_

  isic : is-iso _
  isic .is-iso.inv x =
    ( x .to .fst
    , is-iso→is-equiv (iso
        (x .from .fst)
        (happly (ap fst (x .invl)))
        (happly (ap fst (x .invr))))
    )
    , x .to .snd
  isic .is-iso.rinv x =
    Groups.≅-pathp refl refl refl
  isic .is-iso.linv x =
    Σ-prop-path (λ _ → Group-hom-is-prop)
      (Σ-prop-path is-equiv-is-prop refl)
```
-->

With this equivalence in hands, we can establish that the category of
groups is indeed univalent.

```agda
Groups-is-category : is-category (Groups ℓ)
Groups-is-category = iso≃path→is-category _ eqv where
  open is-iso

  eqv : ∀ {A B} → (A ≡ B) ≃ (A Groups.≅ B)
  eqv {A} {B} =
    (A ≡ B)        ≃⟨ SIP Group-univalent e⁻¹ ⟩
    Σ (Group≃ A B) ≃⟨ Group-equiv≃Groups-iso ⟩
    (A Groups.≅ B) ≃∎
```

<!--
```agda
injective-group-hom
  : ∀ {A B : Group ℓ} (f : Groups.Hom A B)
  → injective (f .fst)
  → Groups.is-monic f
injective-group-hom {A = A} {B} f inj g h p =
  Forget-is-faithful (fm (fst g) (fst h) (ap fst p)) where
  open Group-on
  fm = embedding→monic
    (injective-between-sets→has-prop-fibres (B .snd .has-is-set) (f .fst) inj)
```
-->
