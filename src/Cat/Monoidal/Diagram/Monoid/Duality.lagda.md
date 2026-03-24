<!--
```agda
open import Cat.Functor.Bifunctor.Duality
open import Cat.Monoidal.Diagram.Comonoid
open import Cat.Monoidal.Diagram.Monoid
open import Cat.Functor.Equivalence
open import Cat.Displayed.Total.Op
open import Cat.Functor.Naturality
open import Cat.Functor.Properties
open import Cat.Displayed.Functor
open import Cat.Monoidal.Opposite
open import Cat.Displayed.Total
open import Cat.Displayed.Base
open import Cat.Monoidal.Base
open import Cat.Functor.Base
open import Cat.Duality
open import Cat.Prelude

import Cat.Reasoning
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
  open Cat.Reasoning C public

open Functor
open Monoid-on
open Comonoid-on
open Thinly-displayed

private unquoteDecl Comonoid-on-path = declare-record-path Comonoid-on-path (quote Comonoid-on)
private unquoteDecl Monoid-on-path = declare-record-path Monoid-on-path (quote Monoid-on)
```
-->

# Duality of monoids and comonoids

The duality of [monoids] and [comonoids] in a [[monoidal category]] 
$\cC$ is manifested by an [[isomorphism of precategories]] 
$\rm{Comon}(\cC\op) \cong \rm{Mon}(\cC\op)\op$.

[monoids]: Cat.Monoidal.Diagram.Monoid.html
[comonoids]: Cat.Monoidal.Diagram.Comonoid.html

Our first step is to show that for any $x \in \cC$, the structure of a
`Monoid-object-on`{.Agda} $x$ in $\cC\op$ is the same as the structure 
of a `Comonoid-object-on`{.Agda} $x$ in the category $\cC\op$.

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

```agda
Comon : Displayed C ℓ ℓ
Comon = Comon[ Cᵐ ]
Monᵒᵖ : Displayed (C ^op ^op) ℓ ℓ
Monᵒᵖ = Mon[ Cᵐ ^mop ] ^total-op

Monᵒᵖ→Comon : Displayed-functor ^op^op→ Monᵒᵖ Comon
Monᵒᵖ→Comon = record where
  F₀' = On.Monᵒᵖ→Comon
  F₁' fᵐ = record where
    pres-ε = fᵐ .is-monoid-hom.pres-η
    pres-Δ = fᵐ .is-monoid-hom.pres-μ
  F-id' = prop!
  F-∘' = prop!
```

```agda 
Comon[C] : Precategory (o ⊔ ℓ) ℓ
Comon[C] = ∫ Comon[ Cᵐ ]

Mon[Cᵒᵖ]ᵒᵖ : Precategory (o ⊔ ℓ) ℓ
Mon[Cᵒᵖ]ᵒᵖ = (∫ Mon[ Cᵐ ^mop ]) ^op

F-Monᵒᵖ→Comon : Functor Mon[Cᵒᵖ]ᵒᵖ Comon[C]
F-Monᵒᵖ→Comon .F₀ (x , xᵐ) = x , On.Monᵒᵖ→Comon xᵐ
F-Monᵒᵖ→Comon .F₁ f = ∫hom (f .∫Hom.fst) record where
   pres-ε = f .∫Hom.snd .is-monoid-hom.pres-η
   pres-Δ = f .∫Hom.snd .is-monoid-hom.pres-μ
F-Monᵒᵖ→Comon .F-id = ∫Hom-path Comon[ Cᵐ ] refl prop!
F-Monᵒᵖ→Comon .F-∘ f g = ∫Hom-path Comon[ Cᵐ ] refl prop!
```
