```agda
open import Cat.Functor.Base
open import Cat.Instances.Functor
open import Cat.Prelude
open import Cat.Thin

import Cat.Reasoning

open import Data.Bool


module Cat.Instances.Shape.Isomorphism where
```

# The isomorphism category

The isomorphism category is the category with two points, along
with a unique isomorphism between them.

```agda
Iso-poset : Proset lzero lzero
Iso-poset = make-proset {R = R} hlevel! _ _ hlevel! where
  R : Bool → Bool → Type
  R _ _ = ⊤

*≅* : Precategory lzero lzero
*≅* = Iso-poset .Proset.underlying
```

<!--
```agda
private
  module *≅* = Cat.Reasoning *≅*
```
-->

Note that the space of isomorphisms between any 2 objects is contractible.

```agda
*≅*-iso-contr : ∀ X Y → is-contr (X *≅*.≅ Y)
*≅*-iso-contr _ _ .centre =
  *≅*.make-iso tt tt (hlevel 1 _ _) (hlevel 1 _ _)
*≅*-iso-contr _ _ .paths p =
  *≅*.≅-pathp refl refl refl
```

The isomorphism category is strict, as it's objects form a set.

```agda
*≅*-strict : is-set *≅*.Ob
*≅*-strict = hlevel!
```

# The isomorphism category is not univalent

The isomorphism category is the canonical example of a non-univalent
category. If it were univalent, then we'd get a path between
`true`{.Agda} and `false`{.Agda}!

```agda
*≅*-not-univalent : is-category *≅* → ⊥
*≅*-not-univalent is-cat =
  true≠false $ is-cat .to-path $
  *≅*-iso-contr true false .centre
```

# Functors out of the isomorphism category

One important fact about the isomorphism category is that it classifies
isomorphisms in categories, in the sense that functors out of `*≅*`{.Agda}
into some category $\ca{C}$ are equivalent to isomorphisms in $\ca{C}$.

```agda
Isos : ∀ {o ℓ} → Precategory o ℓ → Type (o ⊔ ℓ)
Isos 𝒞 = Σ[ A ∈ 𝒞.Ob ] Σ[ B ∈ 𝒞.Ob ] (A 𝒞.≅ B)
  where module 𝒞 = Cat.Reasoning 𝒞
```

To prove this, we fix some category $\ca{C}$, and construct an
isomorphism between functors out of `*≅*`{.Agda} and isomorphisms
in $\ca{C}$.

```agda
module _ {o ℓ} {𝒞 : Precategory o ℓ} where
  private
    module 𝒞 = Cat.Reasoning 𝒞
    open Functor
    open 𝒞._≅_
```

For the forward direction, we use the fact that all objects in
`*≅*`{.Agda} are isomorphic to construct an iso between `true`{.Agda}
and `false`{.Agda}, and then use the fact that functors preserve
isomorphisms to obtain an isomorphism in $\ca{C}$.

```agda
  functor→iso : (F : Functor *≅* 𝒞) → Isos 𝒞
  functor→iso F =
    _ , _ , F-map-iso F (*≅*-iso-contr true false .centre)
```

For the backwards direction, we are given an isomorphism $X \cong Y$
in $\ca{C}$. Our functor will map `true`{.Agda} to $X$, and `false`
to $Y$: this is somewhat arbitrary, but lines up with our choices for
the forward direciton. We then perform a big case bash to construct
the mapping of morphisms, and unpack the components of the provided
isomorphism into place. Functoriality follows by the fact that the
provided isomorphism is indeed an isomorphism.

```agda
  iso→functor : Isos 𝒞 → Functor *≅* 𝒞
  iso→functor (X , Y , isom) = fun
    where
      fun : Functor _ _
      fun .F₀ true = X
      fun .F₀ false = Y
      fun .F₁ {true} {true} _ = 𝒞.id
      fun .F₁ {true} {false} _ = to isom
      fun .F₁ {false} {true} _ = from isom
      fun .F₁ {false} {false} _ = 𝒞.id
      fun .F-id {true} = refl
      fun .F-id {false} = refl
      fun .F-∘ {true} {true} {z} f g = sym $ 𝒞.idr _
      fun .F-∘ {true} {false} {true} f g = sym $ invr isom
      fun .F-∘ {true} {false} {false} f g = sym $ 𝒞.idl _
      fun .F-∘ {false} {true} {true} f g = sym $ 𝒞.idl _
      fun .F-∘ {false} {true} {false} f g = sym $ invl isom
      fun .F-∘ {false} {false} {z} f g = sym $ 𝒞.idr _
```

Showing that this function is an equivalence is relatively simple:
the only tricky part is figuring out which lemmas to use to characterise
path spaces!

```agda
  iso≃functor : is-equiv iso→functor
  iso≃functor = is-iso→is-equiv (iso functor→iso rinv linv) where
    rinv : is-right-inverse functor→iso iso→functor
    rinv F =
      Functor-path
        (λ { true → refl ; false → refl })
        (λ { {true} {true} _ → sym (F-id F)
           ; {true} {false} tt → refl
           ; {false} {true} tt → refl
           ; {false} {false} tt → sym (F-id F) })

    linv : is-left-inverse functor→iso iso→functor
    linv F = Σ-pathp refl $ Σ-pathp refl $ 𝒞.≅-pathp refl refl refl
```
