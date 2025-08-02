<!--
```agda
open import Cat.Functor.Naturality.Reflection
open import Cat.Diagram.Product.Indexed
open import Cat.Instances.Comma.Limits
open import Cat.Diagram.Limit.Initial
open import Cat.Diagram.Limit.Product
open import Cat.Diagram.Product.Power
open import Cat.Diagram.Initial.Weak
open import Cat.Diagram.Coseparator
open import Cat.Diagram.Limit.Base
open import Cat.Functor.Naturality
open import Cat.Diagram.Initial
open import Cat.Functor.Adjoint
open import Cat.Instances.Comma
open import Cat.Prelude

import Cat.Reasoning as Cat
import Cat.Morphism as Morb
```
-->

```agda
module Cat.Functor.Adjoint.Cofree {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'} where
```

# Cofree objects {defines="cofree-objects"}

Cofree objects are formally dual to [[free objects]], as opposed to
[[coffee objects|torus]].

<!--
```agda
private
  module C = Precategory C
  module D = Precategory D

module _ (F : Functor C D) where
  private
    open module F = Functor F hiding (op)
```
-->

```agda
  record Cofree-object (X : D.Ob) : Type (adj-level C D) where
    field
      {cofree} : C.Ob
      counit   : D.Hom (F₀ cofree) X

      unfold    : ∀ {Y} (f : D.Hom (F₀ Y) X) → C.Hom Y cofree
      commute : ∀ {Y} {f : D.Hom (F₀ Y) X} → counit D.∘ F₁ (unfold f) ≡ f
      unique
        : ∀ {Y} {f : D.Hom (F₀ Y) X} (g : C.Hom Y cofree)
        → counit D.∘ F₁ g ≡ f
        → g ≡ unfold f
```

<!--
```agda
module _ {F : Functor C D} where
  private
    module F = Functor F
```
-->
```agda
  co-free→cofree : ∀ {X} → Free-object F.op X → Cofree-object F X
  co-free→cofree free = record { Free-object free renaming (free to cofree; fold to unfold; unit to counit) }

  cofree→co-free : ∀ {X} → Cofree-object F X → Free-object F.op X
  cofree→co-free cofree = record { Cofree-object cofree renaming (cofree to free; unfold to fold; counit to unit) }

  right-adjoint→cofree-objects : {U : Functor D C} → F ⊣ U → ∀ X → Cofree-object F X
  right-adjoint→cofree-objects F⊣U = co-free→cofree ⊙ left-adjoint→free-objects (opposite-adjunction F⊣U)

  cofree-objects→right-adjoint : (∀ X → Cofree-object F X) → (Σ[ U ∈ Functor D C ] F ⊣ U)
  cofree-objects→right-adjoint cofree-objs = _ , adjoint-natural-isol ni adj where
    ni : unopF F.op ≅ⁿ F
    ni = trivial-isoⁿ!
    adj : unopF F.op ⊣ _
    adj = unop-adjunction (free-objects≃left-adjoint .fst (cofree→co-free ⊙ cofree-objs) .snd)
```
