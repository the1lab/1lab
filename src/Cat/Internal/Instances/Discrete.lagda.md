<!--
```agda
import Cat.Internal.Base

open import Cat.Prelude
import Cat.Reasoning
```
-->

```agda
module Cat.Internal.Instances.Discrete
  {o ℓ} (C : Precategory o ℓ)
  where
```

<!--
```agda
open Cat.Reasoning C
open Cat.Internal.Base C
open Internal-hom
```
-->

# Discrete Internal Categories

Every object $I : \cC$ induces an internal category of $\cC$, where the
objects and morphisms are both taken to be $I$, and the source and
target maps are the identity morphism. The identity morphism simply
regards an object as a morphism, and composition takes the intermediate
object as the morphism.

Such internal categories are called *discrete internal categories*, and
play the same role as [discrete categories] do in 1-category theory.

[discrete categories]: Cat.Instances.Discrete.html

```agda
Disci-is-internal-cat : ∀ (I : Ob) → Internal-cat-on (id {I}) (id {I})
Disci-is-internal-cat I = icat where
  open Internal-cat-on

  icat : Internal-cat-on id id
  icat .idi x .ihom = x
  icat .idi x .has-src = idl _
  icat .idi x .has-tgt = idl _
  _∘i_ icat {_} {x} {y} {z} f g .ihom = y
  _∘i_ icat {_} {x} {y} {z} f g .has-src =
    id ∘ y       ≡⟨ idl _ ⟩
    y            ≡˘⟨ g .has-tgt ⟩
    id ∘ g .ihom ≡⟨ g .has-src ⟩
    x ∎
  _∘i_ icat {_} {x} {y} {z} f g .has-tgt =
    id ∘ y       ≡⟨ idl _ ⟩
    y            ≡˘⟨ f .has-src ⟩
    id ∘ f .ihom ≡⟨ f .has-tgt ⟩
    z ∎
  icat .idli f = Internal-hom-path $ sym (f .has-tgt) ∙ idl _
  icat .idri f = Internal-hom-path $ sym (f .has-src) ∙ idl _
  icat .associ {_} {w} {x} {y} {z} f g h =
    Internal-hom-path $
    y            ≡˘⟨ g .has-tgt ⟩
    id ∘ g .ihom ≡⟨ g .has-src ⟩
    x ∎
  icat .idi-nat _ = refl
  icat .∘i-nat _ _ _ = refl

Disci : Ob → Internal-cat
Disci I .Internal-cat.C₀ = I
Disci I .Internal-cat.C₁ = I
Disci I .Internal-cat.src = id
Disci I .Internal-cat.tgt = id
Disci I .Internal-cat.has-internal-cat = Disci-is-internal-cat I
```

Functors between discrete internal categories are given by morphisms
between their objects of objects.

```agda
lift-disci : ∀ {I J : Ob} → Hom I J → Internal-functor (Disci I) (Disci J)
lift-disci f .Internal-functor.Fi₀ g = f ∘ g
lift-disci f .Internal-functor.Fi₁ g .ihom = f ∘ g .ihom
lift-disci f .Internal-functor.Fi₁ g .has-src =
  extendl id-comm-sym ∙ ap (f ∘_) (g .has-src)
lift-disci f .Internal-functor.Fi₁ g .has-tgt =
  extendl id-comm-sym ∙ ap (f ∘_) (g .has-tgt)
lift-disci f .Internal-functor.Fi-id = Internal-hom-path refl
lift-disci f .Internal-functor.Fi-∘ _ _ = Internal-hom-path refl
lift-disci f .Internal-functor.Fi₀-nat _ = sym (assoc _ _ _)
lift-disci f .Internal-functor.Fi₁-nat _ _ = sym (assoc _ _ _)
```
