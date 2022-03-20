```agda
open import Cat.Prelude

module Cat.Instances.Shape.Cospan where
```

# The "cospan" category

A _cospan_ in a category $\ca{C}$ is a pair of morphisms $a \xto{f} c
\xot{g} b$ with a common codomain. A [limit] over a diagram with cospan
shape is called a [pullback]. Correspondingly, to encode such diagrams,
we have a "cospan category" $\bull \to \bull \ot \bull$. The dual of
this category, which looks like $\bull \ot \bull \to \bull$, is the
"span" category. Colimits over a span are called [pushouts].

[limit]: Cat.Diagram.Limit.Base.html
[pullback]: Cat.Diagram.Pullback.html
[pushouts]: Cat.Diagram.Pushout.html

```agda
data Cospan-ob : Type where
  cs-a cs-b cs-c : Cospan-ob

Cospan-hom : Cospan-ob → Cospan-ob → Type
Cospan-hom cs-a cs-a = ⊤ -- identity on a
Cospan-hom cs-a cs-b = ⊥ -- no maps a → b
Cospan-hom cs-a cs-c = ⊤ -- one map a → c
Cospan-hom cs-b cs-a = ⊥ -- no maps b → a
Cospan-hom cs-b cs-b = ⊤ -- identity on b
Cospan-hom cs-b cs-c = ⊤ -- one map b → c
Cospan-hom cs-c cs-a = ⊥ -- no maps c → a
Cospan-hom cs-c cs-b = ⊥ -- no maps c → b
Cospan-hom cs-c cs-c = ⊤ -- identity on c

·→·←· ·←·→· : Precategory lzero lzero
```

<!--
```agda
·→·←· = precat where
  open Precategory

  compose : ∀ {a b c} → Cospan-hom b c → Cospan-hom a b → Cospan-hom a c
  compose {cs-a} {cs-a} {cs-a} tt tt = tt
  compose {cs-a} {cs-a} {cs-c} tt tt = tt
  compose {cs-a} {cs-c} {cs-c} tt tt = tt
  compose {cs-b} {cs-b} {cs-b} tt tt = tt
  compose {cs-b} {cs-b} {cs-c} tt tt = tt
  compose {cs-b} {cs-c} {cs-c} tt tt = tt
  compose {cs-c} {cs-c} {cs-c} tt tt = tt

  precat : Precategory _ _
  precat .Ob = Cospan-ob
  precat .Hom = Cospan-hom
  precat .Hom-set cs-a cs-a tt tt p q i j = tt
  precat .Hom-set cs-a cs-c tt tt p q i j = tt
  precat .Hom-set cs-b cs-b tt tt p q i j = tt
  precat .Hom-set cs-b cs-c tt tt p q i j = tt
  precat .Hom-set cs-c cs-c tt tt p q i j = tt
  precat .id {cs-a} = tt
  precat .id {cs-b} = tt
  precat .id {cs-c} = tt
  precat ._∘_ = compose
  precat .idr {cs-a} {cs-a} tt i = tt
  precat .idr {cs-a} {cs-c} tt i = tt
  precat .idr {cs-b} {cs-b} tt i = tt
  precat .idr {cs-b} {cs-c} tt i = tt
  precat .idr {cs-c} {cs-c} tt i = tt
  precat .idl {cs-a} {cs-a} tt i = tt
  precat .idl {cs-a} {cs-c} tt i = tt
  precat .idl {cs-b} {cs-b} tt i = tt
  precat .idl {cs-b} {cs-c} tt i = tt
  precat .idl {cs-c} {cs-c} tt i = tt
  precat .assoc {cs-a} {cs-a} {cs-a} {cs-a} tt tt tt i = tt
  precat .assoc {cs-a} {cs-a} {cs-a} {cs-c} tt tt tt i = tt
  precat .assoc {cs-a} {cs-a} {cs-c} {cs-c} tt tt tt i = tt
  precat .assoc {cs-a} {cs-c} {cs-c} {cs-c} tt tt tt i = tt
  precat .assoc {cs-b} {cs-b} {cs-b} {cs-b} tt tt tt i = tt
  precat .assoc {cs-b} {cs-b} {cs-b} {cs-c} tt tt tt i = tt
  precat .assoc {cs-b} {cs-b} {cs-c} {cs-c} tt tt tt i = tt
  precat .assoc {cs-b} {cs-c} {cs-c} {cs-c} tt tt tt i = tt
  precat .assoc {cs-c} {cs-c} {cs-c} {cs-c} tt tt tt i = tt

·←·→· = ·→·←· ^op
```
-->

Converting a pair of morphisms with common codomain to a cospan-shaped
diagram is straightforward:

```agda
module _ {o ℓ} {C : Precategory o ℓ} where
  open Precategory C
  open Functor

  cospan→cospan-diagram : ∀ {a b c} → Hom a c → Hom b c → Functor ·→·←· C
  cospan→cospan-diagram f g = funct where
    funct : Functor _ _
    funct .F₀ cs-a = _
    funct .F₀ cs-b = _
    funct .F₀ cs-c = _
    funct .F₁ {cs-a} {cs-c} _ = f
    funct .F₁ {cs-b} {cs-c} _ = g
```

<!--
```agda
    funct .F₁ {cs-a} {cs-a} _ = _
    funct .F₁ {cs-b} {cs-b} _ = _
    funct .F₁ {cs-c} {cs-c} _ = _
    funct .F-id {cs-a} = refl
    funct .F-id {cs-b} = refl
    funct .F-id {cs-c} = refl
    funct .F-∘ {cs-a} {cs-a} {cs-a} _ _ i = idl id (~ i)
    funct .F-∘ {cs-a} {cs-a} {cs-c} _ _ i = idr f (~ i)
    funct .F-∘ {cs-a} {cs-c} {cs-c} _ _ i = idl f (~ i)
    funct .F-∘ {cs-b} {cs-b} {cs-b} _ _ i = idl id (~ i)
    funct .F-∘ {cs-b} {cs-b} {cs-c} _ _ i = idr g (~ i)
    funct .F-∘ {cs-b} {cs-c} {cs-c} _ _ i = idl g (~ i)
    funct .F-∘ {cs-c} {cs-c} {cs-c} _ _ i = idl id (~ i)

  span→span-diagram : ∀ {a b c} → Hom a b → Hom a c → Functor ·←·→· C
  span→span-diagram {a} {b} {c} f g = funct where
    funct : Functor _ _
    funct .F₀ cs-a = _
    funct .F₀ cs-b = _
    funct .F₀ cs-c = _
    funct .F₁ {cs-a} {cs-a} _ = id
    funct .F₁ {cs-b} {cs-b} _ = id
    funct .F₁ {cs-c} {cs-a} _ = g
    funct .F₁ {cs-c} {cs-b} _ = f
    funct .F₁ {cs-c} {cs-c} _ = id
    funct .F-id {cs-a} = refl
    funct .F-id {cs-b} = refl
    funct .F-id {cs-c} = refl
    funct .F-∘ {cs-a} {cs-a} {cs-a} tt tt i = idl id (~ i)
    funct .F-∘ {cs-b} {cs-b} {cs-b} tt tt i = idl id (~ i)
    funct .F-∘ {cs-c} {cs-a} {cs-a} tt tt i = idl g (~ i)
    funct .F-∘ {cs-c} {cs-b} {cs-b} tt tt i = idl f (~ i)
    funct .F-∘ {cs-c} {cs-c} {cs-a} tt tt i = idr g (~ i)
    funct .F-∘ {cs-c} {cs-c} {cs-b} tt tt i = idr f (~ i)
    funct .F-∘ {cs-c} {cs-c} {cs-c} tt tt i = idr id (~ i)
```
-->