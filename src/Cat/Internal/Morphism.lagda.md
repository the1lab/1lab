<!--
```agda
open import Cat.Internal.Base using (Internal-cat)
open import Cat.Prelude

import Cat.Internal.Reasoning
import Cat.Internal.Base
```
-->

```agda
module Cat.Internal.Morphism
  {o ℓ} {C : Precategory o ℓ}
  (ℂ : Internal-cat C)
  where
```

<!--
```agda
open Precategory C
open Cat.Internal.Base C
open Cat.Internal.Reasoning ℂ

private variable
  Γ : Ob
  w x y z : Hom Γ C₀
```
-->

# Morphisms in internal categories

This module defines the internal versions of monomorphisms,
epimorphisms, and isomorphisms. These definitions mirror [their
1-categorical counterparts], so we do not comment on them further.

[their 1-categorical counterparts]: Cat.Morphism.html

## Monos

```agda
is-monici : Homi x y → Type _
is-monici {x = x} f = ∀ {w} → (g h : Homi w x) → f ∘i g ≡ f ∘i g → g ≡ h

is-monici-is-prop : ∀ (f : Homi x y) → is-prop (is-monici f)
is-monici-is-prop f x y i {w} g h p = Internal-hom-set g h (x g h p) (y g h p) i

record _↪i_ (x y : Hom Γ C₀) : Type ℓ where
  field
    mori : Homi x y
    monici : is-monici mori
```

## Epis

```agda
is-epici : Homi x y → Type _
is-epici {y = y} f = ∀ {z} → (g h : Homi y z) → g ∘i f ≡ h ∘i f → g ≡ h

is-epici-is-prop : ∀ (f : Homi x y) → is-prop (is-epici f)
is-epici-is-prop f x y i {z} g h p = Internal-hom-set g h (x g h p) (y g h p) i

record _↠i_ (x y : Hom Γ C₀) : Type ℓ where
  field
    mori  : Homi x y
    epici : is-epici mori
```

## Isomorphisms

```agda
record Inversesi (f : Homi x y) (g : Homi y x) : Type ℓ where
  field
    invli : f ∘i g ≡ idi y
    invri : g ∘i f ≡ idi x

record is-invertiblei (f : Homi x y) : Type ℓ where
  field
    invi : Homi y x
    inversesi : Inversesi f invi

  open Inversesi inversesi public

record _≅i_ (x y : Hom Γ C₀) : Type ℓ where
  field
    toi : Homi x y
    fromi : Homi y x
    inversesi : Inversesi toi fromi

  open Inversesi inversesi public

open _≅i_ public
```
