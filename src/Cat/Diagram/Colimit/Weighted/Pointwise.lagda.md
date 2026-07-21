---
description: |
  Functors computed via pointwise weighted colimits.
---

<!--
```agda
open import Cat.Diagram.Colimit.Weighted
open import Cat.Functor.Kan.Pointwise
open import Cat.Functor.Profunctor
open import Cat.Functor.Kan.Base
open import Cat.Functor.Compose
open import Cat.Functor.Hom
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Diagram.Colimit.Weighted.Pointwise where
```

# Pointwise weighted colimits

```agda
module _
  {oj ℓj ok ℓk oc ℓc ℓw}
  {J : Precategory oj ℓj}
  {K : Precategory ok ℓk}
  {C : Precategory oc ℓc}
  where
  private
    module J = Cat.Reasoning J
    module K = Cat.Reasoning K
    module C = Cat.Reasoning C
    open Functor
    open _=>_
```

:::{.definition #pointwise-weighted-colimits}
Let $F : \cJ \to \cC$ be a diagram in $\cC$, and $W : \cK \rel \cJ$ be a [[profunctor]].
A functor $L : \cK \to \cC$ equipped with a family of maps $\iota_{j, k} : W(j,k) \to \cC(F(j), L(k))$
is a **pointwise weighted colimit** of $F$ weighted by $W$ if:

- Each weighted cocone $(L(k), \iota_{k})$ is a [[weighted colimit]] of $F$ weighted by
  $W(-,k)$, and
- $\iota$ is natural in $K$, insofar that $L(f) \circ \iota_{j,k_{1}}(w) = \iota_{j, k_{2}}(w \cdot f)$
  for every $f : \cK(k_{1}, k_{2})$.
:::


```agda
  record is-pointwise-weighted-colimit
    (W : Profunctor K J ℓw)
    (F : Functor J C)
    (L : Functor K C)
    (ι : ∀ j k → ⌞ W · j · k ⌟ → C.Hom (F · j) (L · k))
    : Type (oj ⊔ ℓj ⊔ ok ⊔ ℓk ⊔ oc ⊔ ℓc ⊔ ℓw) where
    no-eta-equality
    private
      module W = Bifunctor W
      module F = Functor F
      module L = Functor L
    field
      ι-natural
        : ∀ {k1 k2} (f : K.Hom k1 k2) (j : J.Ob) (w : ∣ W · j · k1 ∣)
        → L.₁ f C.∘ ι j k1 w ≡ ι j k2 (W.rmap f w)
      has-is-pointwise-colim : ∀ k → is-weighted-colimit (W.Left k) F (L · k) (λ j w → ι j k w)
```

If $L$ is a pointwise weighted colimit, then the functorial action of
$L$ is given pointwise via universal maps.

```agda
    module _ {k : K.Ob} where
      open is-weighted-colimit (has-is-pointwise-colim k) public

    abstract
      ι-rmap-commutes
        : ∀ {k1 k2} (f : K.Hom k1 k2)
        → is-weighted-cocone (W.Left k1) F (λ j w → ι j k2 (W.rmap f w))
      ι-rmap-commutes {k1} {k2} f {i} {j} h w =
        ι j k2 (W.rmap f w) C.∘ F.F₁ h ≡⟨ commutes h (W.rmap f w) ⟩
        ι i k2 (W.lmap h (W.rmap f w)) ≡⟨ ap (ι i k2) (W.lrmap h f ·ₚ w) ⟩
        ι i k2 (W.rmap f (W.lmap h w)) ∎

    pointwise-universal
      : ∀ {k1 k2} (f : K.Hom k1 k2)
      → L.₁ f ≡ universal (λ j w → ι j k2 (W.rmap f w)) (ι-rmap-commutes f)
    pointwise-universal f = sym $ unique _ _ _ λ j w → ι-natural f j w
```

Moreover, natural transformations out of a pointwise weighted colimit
are given by natural families of weighted cocones.

```agda
    universal-nt
      : ∀ {H : Functor K C}
      → (ψ : ∀ j k → ⌞ W · j · k ⌟ → C.Hom (F · j) (H · k))
      → (∀ k → is-weighted-cocone (W.Left k) F (λ j w → ψ j k w))
      → (∀ {k1 k2} (f : K.Hom k1 k2) (j : J.Ob) (w : ∣ W · j · k1 ∣)
         → H .F₁ f C.∘ ψ j k1 w ≡ ψ j k2 (W.rmap f w))
      → L => H
    universal-nt {H = H} ψ ψ-cocone ψ-nat .η k = universal (λ j w → ψ j k w) (ψ-cocone k)
    universal-nt {H = H} ψ ψ-cocone ψ-nat .is-natural k1 k2 f =
      unique₂ _ _ λ j w →
        (universal (λ j → ψ j k2) _ C.∘ L.F₁ f) C.∘ ι j k1 w  ≡⟨ C.pullr (ι-natural f j w) ⟩
        universal (λ j → ψ j k2) _ C.∘ ι j k2 (W.rmap f w)    ≡⟨ factors _ _ _ _ ⟩
        ψ j k2 (W.rmap f w)                                   ≡˘⟨ ψ-nat f j w ⟩
        H .F₁ f C.∘ ψ j k1 w                                  ≡⟨ C.pushr (sym (factors _ _ _ _)) ⟩
        (H .F₁ f C.∘ universal (λ j → ψ j k1) _) C.∘ ι j k1 w ∎
```

## Pointwise Kan extensions via pointwise weighted colimits

<!--
```agda
module _
  {oc ℓc oc' ℓc' od ℓd}
  {C : Precategory oc ℓc}
  {C' : Precategory oc' ℓc'}
  {D : Precategory od ℓd}
  {P : Functor C C'}
  {F : Functor C D}
  {L : Functor C' D}
  {ε : F => L F∘ P}
  where
  private
    module C = Cat.Reasoning C
    module C' = Cat.Reasoning C'
    module D = Cat.Reasoning D
    module P = Functor P
    module L = Functor L
    open Functor
    open _=>_
```
-->

We can compute [[left Kan extensions]] of $F : \cC \to \cD$ along $P : \cC \to \cC'$
as pointwise weighted colimits of $F$ along the representable profunctor $\cC'(P(-), =)$.

```agda
  private
    C'[P[-],-] : Profunctor C' C ℓc'
    C'[P[-],-] = precompose₂ (Hom[-,-] C') P.op Id

  is-pointwise-weighted-colimit→is-lan
    : is-pointwise-weighted-colimit C'[P[-],-] F L (λ c c' f → L.₁ f D.∘ ε .η c)
    → is-lan P F L ε
  is-pointwise-weighted-colimit→is-lan L-pointwise = record where
    open is-pointwise-weighted-colimit L-pointwise

    σ {M = M} α =
      universal-nt (λ c c' f → M .F₁ f D.∘ η α c)
        (λ c' f h → D.pullr (α .is-natural _ _ f) ∙ D.pulll (sym (M .F-∘ _ _)))
        (λ f c h → D.pulll (sym (M .F-∘ _ _)))
    σ-comm {M} {α} = ext λ c →
      universal (λ c' f → M .F₁ f D.∘ α .η c') _ D.∘ ε .η c               ≡⟨ D.cdr (D.introl L.F-id) ⟩
      universal (λ c' f → M .F₁ f D.∘ α .η c') _ D.∘ L.₁ C'.id D.∘ ε .η c ≡⟨ factors _ _ _ _ ⟩
      M .F₁ C'.id D.∘ η α c                                               ≡⟨ D.eliml (M .F-id) ⟩
      α .η c ∎
    σ-uniq {M} {α} {σ'} p = ext λ c' → unique _ _ _ λ c f →
      σ' .η c' D.∘ L.₁ f D.∘ ε .η c           ≡⟨ D.pulll (σ' .is-natural (P · c) c' f) ⟩
      (M .F₁ f D.∘ σ' .η (P · c)) D.∘ ε .η c  ≡⟨ D.pullr (sym $ p ·ₚ c) ⟩
      M .F₁ f D.∘ α .η c                      ∎
```
