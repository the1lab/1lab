<!--
```agda
open import Cat.Displayed.Functor.Equivalence
open import Cat.Monoidal.Diagram.Comonoid
open import Cat.Monoidal.Diagram.Monoid
open import Cat.Functor.Equivalence
open import Cat.Displayed.Total.Op
open import Cat.Functor.Properties
open import Cat.Displayed.Functor
open import Cat.Monoidal.Opposite
open import Cat.Displayed.Base
open import Cat.Monoidal.Base
open import Cat.Functor.Base
open import Cat.Duality
open import Cat.Prelude

import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Monoidal.Diagram.Monoid.Duality {o ℓ}
  {C : Precategory o ℓ} (Cᵐ : Monoidal-category C)
  where
```

<!--
```agda
private module C where
  open Monoidal-category Cᵐ public
  open Cr C public

open Functor
open Monoid-on
open Comonoid-on

private unquoteDecl Comonoid-on-path = declare-record-path Comonoid-on-path (quote Comonoid-on)
private unquoteDecl Monoid-on-path = declare-record-path Monoid-on-path (quote Monoid-on)
```
-->

# Duality of monoids and comonoids

The duality of [monoids] and [comonoids] in a [[monoidal category]]
$\cC$ is manifested by an [[isomorphism of displayed precategories]]
$\rm{Comon}(\cC\op) \cong \rm{Mon}(\cC\op)\op$.

[monoids]: Cat.Monoidal.Diagram.Monoid.html
[comonoids]: Cat.Monoidal.Diagram.Comonoid.html

Our first step is to show that for any $x \in \cC$, the structure of a
`Monoid-object-on`{.Agda} $x$ in $\cC\op$ is the same as the structure
of a `Comonoid-object-on`{.Agda} $x$ in the category $\cC$.

```agda
module On {x : C.Ob} where
  Monᵒᵖ→Comon : Monoid-on (Cᵐ ^mop) x → Comonoid-on Cᵐ x
  Monᵒᵖ→Comon xᵐ = record where
    ε = xᵐ .η
    Δ = xᵐ .μ
    Δ-counitl = xᵐ .μ-unitl
    Δ-counitr = xᵐ .μ-unitr
    Δ-coassoc = xᵐ .μ-assoc ∙ sym (C.assoc _ _ _)

  Comon→Monᵒᵖ : Comonoid-on Cᵐ x → Monoid-on (Cᵐ ^mop) x
  Comon→Monᵒᵖ xᶜ = record where
    η = xᶜ .ε
    μ = xᶜ .Δ
    μ-unitl = xᶜ .Δ-counitl
    μ-unitr = xᶜ .Δ-counitr
    μ-assoc = xᶜ .Δ-coassoc ∙ C.assoc _ _ _

  Monᵒᵖ≅Comon : Iso (Monoid-on (Cᵐ ^mop) x) (Comonoid-on Cᵐ x)
  Monᵒᵖ≅Comon = Monᵒᵖ→Comon , iso Comon→Monᵒᵖ rinv linv where
    rinv : is-right-inverse Comon→Monᵒᵖ Monᵒᵖ→Comon
    rinv xᶜ = Comonoid-on-path refl refl

    linv : is-left-inverse Comon→Monᵒᵖ Monᵒᵖ→Comon
    linv xᵐ = Monoid-on-path refl refl

  Monᵒᵖ≃Comon : Monoid-on (Cᵐ ^mop) x ≃ Comonoid-on Cᵐ x
  Monᵒᵖ≃Comon = Iso→Equiv Monᵒᵖ≅Comon
```

<!--
```agda
private
  unquoteDecl is-comonoid-hom-iso = declare-record-iso is-comonoid-hom-iso
    (quote is-comonoid-hom)

  instance
    H-Level-is-comonoid-hom : ∀ {m n} {f : C .Precategory.Hom m n} {mo no} {k}
      → H-Level (is-comonoid-hom Cᵐ f mo no) (suc k)
    H-Level-is-comonoid-hom = prop-instance $ Iso→is-hlevel! 1 is-comonoid-hom-iso
```
-->

Next we extend this correspondence to morphisms, giving a [[displayed
functor]] `Monᵒᵖ→Comon`{.Agda} between `Monᵒᵖ`{.Agda} and `Comon`{.Agda}
over the [[isomorphism of precategories]] `^op^op→`{.Agda}:

```agda
Comon : Displayed C ℓ ℓ
Comon = Comon[ Cᵐ ]
Monᵒᵖ : Displayed (C ^op ^op) ℓ ℓ
Monᵒᵖ = Mon[ Cᵐ ^mop ] ^total-op

Monᵒᵖ→Comon : Displayed-functor ^op^op→ Monᵒᵖ Comon
Monᵒᵖ→Comon = record where
  F₀' = On.Monᵒᵖ→Comon
  F₁' fᵐ = record
    { pres-ε = fᵐ .is-monoid-hom.pres-η
    ; pres-Δ = fᵐ .is-monoid-hom.pres-μ ∙ (C.-⊗-.rlmap _ _ C.⟩∘⟨refl) }
  F-id' = prop!
  F-∘' = prop!
```

<!--
```agda
module Monᵒᵖ→Comon = Displayed-functor Monᵒᵖ→Comon
```
-->

Finally we show that `Monᵒᵖ→Comon`{.Agda} is an [[isomorphism of
displayed precategories]].

```agda
open is-precat-iso[_]
Monᵒᵖ→Comon-is-iso[] : is-precat-iso[ ^op^op-is-iso ] Monᵒᵖ→Comon
Monᵒᵖ→Comon-is-iso[] .has-is-iso' x = On.Monᵒᵖ≃Comon .snd
Monᵒᵖ→Comon-is-iso[] .has-is-ff' = biimp-is-equiv! (Monᵒᵖ→Comon.₁') λ fᶜ → record
  { pres-η = fᶜ .is-comonoid-hom.pres-ε
  ; pres-μ = fᶜ .is-comonoid-hom.pres-Δ ∙ (C.-⊗-.lrmap _ _ C.⟩∘⟨refl)
  }
```

Thus we also have a [[total isomorphism of precategories]] between the
corresponding [[total categories]].
