<!--
```agda
open import Cat.Diagram.Comonad
open import Cat.Displayed.Total
open import Cat.Functor.Adjoint
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Instances.Coalgebras where
```

# Coalgebras over a comonad {defines="coalgebra category-of-coalgebras"}

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} (W : Comonad C) where
  open Cat.Reasoning C
  open Comonad W hiding (W)
```
-->

```agda
  record Coalgebra-on (A : Ob) : Type (o ⊔ ℓ) where
    no-eta-equality

    field
      ρ        : Hom A (W₀ A)
      ρ-counit : counit.ε A ∘ ρ ≡ id
      ρ-comult : W₁ ρ ∘ ρ       ≡ comult.η A ∘ ρ
```

<!--
```agda
  open Coalgebra-on
  module _ where
    open Displayed
```
-->

```agda
    is-coalgebra-hom : ∀ {x y} (h : Hom x y) → Coalgebra-on x → Coalgebra-on y → Type _
    is-coalgebra-hom f α β = W₁ f ∘ α .ρ ≡ β .ρ ∘ f

    Coalgebras-over : Displayed C (o ⊔ ℓ) ℓ
    Coalgebras-over .Ob[_]            = Coalgebra-on
    Coalgebras-over .Hom[_]           = is-coalgebra-hom
    Coalgebras-over .Hom[_]-set f α β = hlevel 2

    Coalgebras-over .id′      = eliml W-id ∙ intror refl
    Coalgebras-over ._∘′_ p q = pushl (W-∘ _ _) ·· ap (W₁ _ ∘_) q ·· extendl p

    Coalgebras-over .idr′ f′         = prop!
    Coalgebras-over .idl′ f′         = prop!
    Coalgebras-over .assoc′ f′ g′ h′ = prop!

  Coalgebras : Precategory (o ⊔ ℓ) ℓ
  Coalgebras = ∫ Coalgebras-over
```

<!--
```agda
  module Coalgebras = Cat.Reasoning Coalgebras

  open Total-hom
  open Functor
  open _⊣_
  open _=>_

  coalgebra-hom-path
    : ∀ {x y} {h h' : Coalgebras .Precategory.Hom x y}
    → h .hom ≡ h' .hom
    → h ≡ h'
  coalgebra-hom-path p = total-hom-path Coalgebras-over p prop!
```
-->

## Cofree coalgebras {defines="cofree-coalgebra"}

```agda
  Cofree-coalgebra : Ob → Coalgebras.Ob
  Cofree-coalgebra A .fst = W₀ A
  Cofree-coalgebra A .snd .ρ = comult.η _
  Cofree-coalgebra A .snd .ρ-counit = right-ident
  Cofree-coalgebra A .snd .ρ-comult = comult-assoc

  Cofree : Functor C Coalgebras
  Cofree .F₀ = Cofree-coalgebra

  Cofree .F₁ h .hom       = W₁ h
  Cofree .F₁ h .preserves = sym (comult.is-natural _ _ h)

  Cofree .F-id    = coalgebra-hom-path W-id
  Cofree .F-∘ f g = coalgebra-hom-path (W-∘ _ _)
```

```agda
  Forget⊣Cofree : πᶠ Coalgebras-over ⊣ Cofree
  Forget⊣Cofree .unit .η (x , α) .hom       = α .ρ
  Forget⊣Cofree .unit .η (x , α) .preserves = α .ρ-comult
  Forget⊣Cofree .unit .is-natural x y f = coalgebra-hom-path (sym (f .preserves))

  Forget⊣Cofree .counit .η x              = Comonad.counit.ε W _
  Forget⊣Cofree .counit .is-natural x y f = Comonad.counit.is-natural W _ _ _

  Forget⊣Cofree .zig {A , α} = α .ρ-counit
  Forget⊣Cofree .zag         = coalgebra-hom-path left-ident
```

<!--
```agda
  to-cofree-hom
    : ∀ {X Y} → Hom (X .fst) Y → Coalgebras.Hom X (Cofree-coalgebra Y)
  to-cofree-hom f = L-adjunct Forget⊣Cofree f
```
-->
