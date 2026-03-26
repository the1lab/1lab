<!--
```agda
open import Cat.Functor.Naturality
open import Cat.Functor.Bifunctor
open import Cat.Functor.Coherence
open import Cat.Monoidal.Base
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Reasoning

open Monoidal-category
```
-->

```agda
module Cat.Monoidal.Reverse {o ℓ}
  {C : Precategory o ℓ} (Cᵐ : Monoidal-category C)
  where
```

<!--
```agda
open Cat.Reasoning C
private module C = Monoidal-category Cᵐ
open _=>_
```
-->

# Reverse monoidal categories {defines="reverse-monoidal-category"}

Given a [[monoidal category]] $\cC$ with tensor product $\otimes :
\cC \times \cC \to \cC$, we can define the **reverse** monoidal category
$\cC^\rm{rev}$ with the same unit and the tensor product flipped
around: $A \otimes^\rm{rev} B = B \otimes A$.

```agda
_^rev : Monoidal-category C
_^rev .-⊗- = Flip C.-⊗-
_^rev .Unit = C.Unit
```

The coherence isomorphisms are straightforward to obtain from those of
$\cC$: the left and right unitors are swapped, and the associator is
reversed and has its arguments swapped.

```agda
_^rev .unitor-l = iso→isoⁿ (isoⁿ→iso C.unitor-r)
  λ f → sym (C.unitor-r .Isoⁿ.to .is-natural _ _ f)
_^rev .unitor-r = iso→isoⁿ (isoⁿ→iso C.unitor-l)
  λ f → sym (C.unitor-l .Isoⁿ.to .is-natural _ _ f)
_^rev .associator = iso→isoⁿ
  (λ (a , b , c) → isoⁿ→iso (C.associator ni⁻¹) (c , b , a))
  λ (f , g , h) →
    let
      p : (_ C.▶ f) ∘ ((_ C.▶ g) ∘ (h C.◀ _) C.◀ _) ≡ (((h C.◀ _) ∘ (_ C.▶ g)) C.◀ _) ∘ (_ C.▶ f)
      p = ap₂ _∘_ refl (ap (C._◀ _) (sym (C.-⊗-.lrmap _ _))) ∙ sym (C.-⊗-.lrmap _ _)

      q : (h C.◀ _) ∘ (_ C.▶ (g C.◀ _) ∘ (_ C.▶ f)) ≡ (_ C.▶ (_ C.▶ f) ∘ (g C.◀ _)) ∘ (h C.◀ _)
      q = ap₂ _∘_ refl (ap (_ C.▶_) (C.-⊗-.lrmap _ _)) ∙ C.-⊗-.lrmap _ _
    in ap₂ _∘_ p refl
    ∙∙ sym (C.associator .Isoⁿ.from .is-natural _ _ (h , g , f))
    ∙∙ ap₂ _∘_ refl q
_^rev .triangle = C.triangle-α→
_^rev .pentagon = C.pentagon-α→
```

<!--
```agda
_ = Deloop
```
-->

Thinking of monoidal categories as one-object [[bicategories]] (via the
`Deloop`{.Agda}ing construction), the $-^\rm{rev}$ operation corresponds to
flipping the 1-cells of a bicategory, leaving the 2-cells unchanged.
