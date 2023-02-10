```agda
open import Cat.Prelude

open import Data.Bool

import Cat.Reasoning

module Cat.Instances.Shape.Parallel where
```

# The "parallel arrows" category

The parallel arrows category is the category with two objects, and two
parallel arrows between them. It is the shape of [equaliser] and
[coequaliser] diagrams.

[equaliser]: Cat.Diagram.Equaliser.html
[coequaliser]: Cat.Diagram.Coequaliser.html

```agda

·⇉· : Precategory lzero lzero
·⇉· = precat where
  open Precategory
  precat : Precategory _ _
  precat .Ob = Bool

  precat .Hom false false = ⊤
  precat .Hom false true  = Bool
  precat .Hom true  false = ⊥
  precat .Hom true  true  = ⊤
```

<!--
```agda
  precat .Hom-set false false a b p q i j = tt
  precat .Hom-set false true  a b p q i j = Bool-is-set a b p q i j
  precat .Hom-set true  true  a b p q i j = tt

  precat .id {false} = tt
  precat .id {true} = tt
  _∘_ precat {false} {false} {false} _ _ = tt
  _∘_ precat {false} {false} {true}  p _ = p
  _∘_ precat {false} {true}  {true}  _ q = q
  _∘_ precat {true}  {true}  {true}  _ _ = tt
  precat .idr {false} {false} f = refl
  precat .idr {false} {true}  f = refl
  precat .idr {true}  {true}  f = refl
  precat .idl {false} {false} f = refl
  precat .idl {false} {true}  f = refl
  precat .idl {true}  {true}  f = refl
  precat .assoc {false} {false} {false} {false} f g h = refl
  precat .assoc {false} {false} {false} {true}  f g h = refl
  precat .assoc {false} {false} {true}  {true}  f g h = refl
  precat .assoc {false} {true}  {true}  {true}  f g h = refl
  precat .assoc {true}  {true}  {true}  {true}  f g h = refl
```
-->

```agda
module _ {o ℓ} {C : Precategory o ℓ} where
  open Cat.Reasoning C
  open Functor
  open _=>_

  Fork : ∀ {a b} (f g : Hom a b) → Functor ·⇉· C
  Fork f g = funct where
    funct : Functor _ _
    funct .F₀ false = _
    funct .F₀ true = _
    funct .F₁ {false} {false} _ = id
    funct .F₁ {false} {true}  false = f
    funct .F₁ {false} {true}  true = g
    funct .F₁ {true} {true}   _ = id
    funct .F-id {false} = refl
    funct .F-id {true} = refl
    funct .F-∘ {false} {false} {false} f g   = sym (idr _)
    funct .F-∘ {false} {false} {true}  f g   = sym (idr _)
    funct .F-∘ {false} {true}  {true}  tt _  = sym (idl _)
    funct .F-∘ {true}  {true}  {true}  tt tt = sym (idl _)

  Fork→Cone
    : ∀ {a b e} {f g : Hom a b} {equ : Hom e a}
    → (f ∘ equ ≡ g ∘ equ)
    → Const e => Fork f g
  Fork→Cone {e = e} {f = f} {g = g} {equ = equ} equal = nt where
    nt : Const e => Fork f g
    nt .η true = f ∘ equ
    nt .η false = equ
    nt .is-natural true true tt = id-comm
    nt .is-natural false true true = idr _ ∙ equal
    nt .is-natural false true false = idr _
    nt .is-natural false false tt = id-comm
```
