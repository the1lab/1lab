---
description: We define the comonad associated to an adjunction.
---
<!--
```agda
open import Cat.Diagram.Comonad
open import Cat.Functor.Adjoint
open import Cat.Prelude

open Comonad-on
open Functor
open _=>_
```
-->

# The comonad from an adjunction {defines="comonad-from-an-adjunction"}

```agda
module
  Cat.Functor.Adjoint.Comonad
  {o₁ h₁ o₂ h₂ : _}
  {C : Precategory o₁ h₁}
  {D : Precategory o₂ h₂}
  {L : Functor C D} {R : Functor D C}
  (L⊣R : L ⊣ R)
  where
```

<!--
```agda
private
  module C = Precategory C
  module D = Precategory D
  module L = Functor L
  module R = Functor R
  module adj = _⊣_ L⊣R
```
-->

Every [[adjunction]] $L \dashv R$ gives rise to a [[comonad]], where the
underlying functor is $L \circ R$. This is dual to the construction
of the [[monad from an adjunction]].

```agda
Adjunction→Comonad : Comonad-on (L F∘ R)
```

The counit of the comonad is just the adjunction counit, and the
comultiplication comes from the unit.

```agda
Adjunction→Comonad .counit = adj.counit
Adjunction→Comonad .comult = NT (λ x → L.₁ (adj.η (R.₀ x))) λ x y f →
  L.₁ (adj.η (R.₀ y)) D.∘ L.₁ (R.₁ f)             ≡˘⟨ L.F-∘ _ _ ⟩
  L.₁ (adj.η (R.₀ y) C.∘ R.₁ f)                   ≡⟨ ap L.₁ (adj.unit.is-natural _ _ _) ⟩
  L.₁ (R.₁ (L.₁ (R.₁ f)) C.∘ adj.η (R.₀ x))       ≡⟨ L.F-∘ _ _ ⟩
  L.₁ (R.₁ (L.₁ (R.₁ f))) D.∘ L.₁ (adj.η (R.₀ x)) ∎
```

The comonad laws follow from the zig-zag identities. In fact, the
right identity law is exactly the `zig`{.Agda ident="adj.zag"}
identity.

```agda
Adjunction→Comonad .δ-unitr {x} = adj.zig
```

The others are slightly more involved.

```agda
Adjunction→Comonad .δ-unitl {x} = path where abstract
  path : L.₁ (R.₁ (adj.ε x)) D.∘ L.₁ (adj.η (R.F₀ x)) ≡ D.id
  path =
    L.₁ (R.₁ (adj.ε _)) D.∘ L.₁ (adj.η _) ≡⟨ sym (L.F-∘ _ _) ⟩
    L.₁ (R.₁ (adj.ε _) C.∘ adj.η _)       ≡⟨ ap L.₁ adj.zag ⟩
    L.₁ C.id                              ≡⟨ L.F-id ⟩
    D.id                                  ∎

Adjunction→Comonad .δ-assoc {x} = path where abstract
  path : L.₁ (R.₁ (L.₁ (adj.η (R.F₀ x)))) D.∘ L.₁ (adj.η _)
       ≡ L.₁ (adj.η (R .F₀ (L.F₀ (R.F₀ x)))) D.∘ L.₁ (adj.η _)
  path =
    L.₁ (R.₁ (L.₁ (adj.η _))) D.∘ L.₁ (adj.η _)   ≡⟨ sym (L.F-∘ _ _) ⟩
    L.₁ (R.₁ (L.₁ (adj.η _)) C.∘ adj.η _)         ≡˘⟨ ap L.₁ (adj.unit.is-natural _ _ _) ⟩
    L.₁ (adj.η _ C.∘ adj.η _)                     ≡⟨ L.F-∘ _ _ ⟩
    L.₁ (adj.η _) D.∘ L.₁ (adj.η _)               ∎
```
