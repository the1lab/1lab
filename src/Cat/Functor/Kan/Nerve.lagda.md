---
description: |
  We use the calculation of left Kan extensions as certain colimits to
  associate a "nerve" (restricted Yoneda embedding) and "realization"
  (left Kan extension along よ) adjunction given any functor.
---

```agda
{-# OPTIONS -vtc.decl:5 -WnoEmptyWhere #-}
open import Cat.Diagram.Colimit.Base
open import Cat.Diagram.Initial
open import Cat.Functor.Adjoint
open import Cat.Functor.Hom
open import Cat.Functor.Kan.Base
open import Cat.Functor.Kan.Pointwise
open import Cat.Instances.Comma
open import Cat.Instances.Functor
open import Cat.Instances.Functor.Compose
open import Cat.Instances.Shape.Terminal
open import Cat.Prelude

import Cat.Functor.Reasoning as Func
import Cat.Reasoning

module Cat.Functor.Kan.Nerve where
```

<!--
```agda
private
  variable o κ : Level
open Func
open _=>_
open is-lan
```
-->

# Nerve and realisation

Let $F : \cC \to \cD$ be a functor from a [$\kappa$-small] category
$\cC$ to a locally $\kappa$-small, $\kappa$-[cocomplete] category
$\cD$. $F$ induces a pair of [adjoint functors], as in the diagram
below, where $|-| \dashv \bf{N}$. In general, the left adjoint is called
"realization", and the right adjoint is called "nerve".

[$\kappa$-small]: 1Lab.intro.html#universes-and-size-issues
[cocomplete]: Cat.Diagram.Colimit.Base.html#cocompleteness
[adjoint functors]: Cat.Functor.Adjoint.html

~~~{.quiver .short-1}
\[\begin{tikzcd}
  {\mathrm{PSh}(\mathcal{C})} && {\mathcal{D}}
  \arrow[""{name=0, anchor=center, inner sep=0}, "{\mathbf{N}}"', shift right=2, from=1-3, to=1-1]
  \arrow[""{name=1, anchor=center, inner sep=0}, "{|-|}"', shift right=2, from=1-1, to=1-3]
  \arrow["\dashv"{anchor=center, rotate=90}, draw=none, from=1, to=0]
\end{tikzcd}\]
~~~

An example to keep in mind is the inclusion $F : \Delta \mono \strcat$
from the simplex category to [strict categories], which sends the
$n$-simplex to the finite [poset] $[n]$. In this case, the left adjoint
is the ordinary realisation of a simplicial set $[\Delta\op,\Sets]$ as a
strict category, and the right adjoint gives the simplicial nerve of a
strict category.

[strict categories]: Cat.Instances.StrictCat.html
[poset]: Order.Base.html

Since these adjunctions come for very cheap ($\kappa$-cocompleteness of
the codomain category is all we need), they are built out of very thin
abstract nonsense: The "realisation" left adjoint is given by the [left
Kan extension] of $F$ along the [Yoneda embedding] $\yo$, which can be
[computed] as a particular colimit, and the "nerve" right adjoint is
given by the _restricted_ Yoneda embedding functor $X \mapsto \hom(F(-),
X)$.

[left Kan extension]: Cat.Functor.Kan.Base.html
[Yoneda embedding]: Cat.Functor.Hom.html
[computed]: Cat.Functor.Kan.Pointwise.html

<!--
```agda
module _
  {o κ} {C : Precategory κ κ} {D : Precategory o κ}
  (F : Functor C D)
  where
    private
      module C = Cat.Reasoning C
      module D = Cat.Reasoning D
      module F = Func F
```
-->

```agda
    Nerve : Functor D (PSh κ C)
    Nerve .F₀ c = Hom-into D c F∘ Functor.op F
    Nerve .F₁ f = よ₁ D f ◂ (Functor.op F)
    Nerve .F-id = Nat-path (λ _ → funext λ _ → D.idl _)
    Nerve .F-∘ _ _ = Nat-path (λ _ → funext λ _ → sym (D.assoc _ _ _))
```

Furthermore, the nerve is a left kan extension along the yoneda
embedding.

<!--
```agda
    coapprox : よ C => Nerve F∘ F
    coapprox .η x .η y f = F.F₁ f
    coapprox .η x .is-natural _ _ _ =
      funext λ _ → F.F-∘ _ _
    coapprox .is-natural _ _ _ =
      Nat-path λ _ → funext λ _ → F.F-∘ _ _
```
-->

```agda
    Nerve-is-lan : is-lan F (よ C) Nerve coapprox
    Nerve-is-lan .σ {M = M} α .η d .η c f =
      M .F₁ f .η c (α .η c .η c C.id)
```

<details>The remainder of the proof follows by applying naturality 10000
times, and is not very interesting.
<summary>
```agda
    Nerve-is-lan .σ {M = M} α .η d .is-natural x y f =
      funext λ g →
        M .F₁ (g D.∘ F .F₁ f) .η y (α .η y .η y C.id)            ≡⟨ M .F-∘ g (F .F₁ f) ηₚ _ $ₚ _ ⟩
        M .F₁ g .η y (M .F₁ (F .F₁ f) .η y (α .η y .η y C.id))    ≡˘⟨ ap (M .F₁ g .η y) (α .is-natural _ _ _ ηₚ _ $ₚ _) ⟩
        M .F₁ g .η y (α .η x .η y ⌜ f C.∘ C.id ⌝)                 ≡⟨ ap! C.id-comm ⟩
        M .F₁ g .η y (α .η x .η y (C.id C.∘ f))                   ≡⟨ ap (M .F₁ g .η y) (α .η _ .is-natural _ _ _ $ₚ _) ⟩
        M .F₁ g .η y ((M .F₀ (F .F₀ x)) .F₁ f (α .η x .η x C.id)) ≡⟨ M .F₁ g .is-natural _ _ _ $ₚ _ ⟩
        (M .F₀ d) .F₁ f (M .F₁ g .η x (α .η x .η x C.id))        ∎
    Nerve-is-lan .σ {M = M} α .is-natural x y f =
      Nat-path λ z → funext λ g → M .F-∘ f g ηₚ _ $ₚ _ 
    Nerve-is-lan .σ-comm {M = M} {α = α} =
      Nat-path λ x → Nat-path λ y → funext λ f →
        M .F₁ (F .F₁ f) .η y (α .η y .η y C.id) ≡˘⟨ α .is-natural _ _ _ ηₚ _ $ₚ _ ⟩
        α .η x .η y (f C.∘ C.id)                ≡⟨ ap (α .η x .η y) (C.idr _) ⟩
        α .η x .η y f                           ∎
    Nerve-is-lan .σ-uniq {M = M} {α = α} {σ′ = σ′} p =
      Nat-path λ x → Nat-path λ y → funext λ f →
        M .F₁ f .η y (α .η y .η y C.id)            ≡⟨ ap (M .F₁ f .η y) (p ηₚ _ ηₚ _ $ₚ _) ⟩
        M .F₁ f .η y (σ′ .η _ .η y ⌜ F .F₁ C.id ⌝) ≡⟨ ap! (F .F-id) ⟩
        M .F₁ f .η y (σ′ .η _ .η y D.id)           ≡˘⟨ σ′ .is-natural _ _ _ ηₚ _ $ₚ _ ⟩
        σ′ .η x .η y (f D.∘ D.id)                  ≡⟨ ap (σ′ .η x .η y) (D.idr _) ⟩
        σ′ .η x .η y f                             ∎
```
</summary>
</details>

The realisation left adjoint is constructed by general abstract
nonsense.

<!--
```agda
module _
  {o κ κ′} {C : Precategory κ κ} {D : Precategory o κ′}
  (F : Functor C D)
  (cocompl : is-cocomplete κ κ D)
  where
```
-->

```agda
  Realisation : Functor (PSh κ C) D
  Realisation = Lan.Ext (cocomplete→lan (よ C) F cocompl)

  approx : F => Realisation F∘ よ C
  approx = Lan.eta (cocomplete→lan (よ C) F cocompl)

  Realisation-is-lan : is-lan (よ C) F Realisation approx
  Realisation-is-lan = Lan.has-lan (cocomplete→lan (よ C) F cocompl)
```

<!--
```agda
module _
  {o κ} {C : Precategory κ κ} {D : Precategory o κ}
  (F : Functor C D)
  (cocompl : is-cocomplete κ κ D)
  where

  private
    module C = Cat.Reasoning C
    module D = Cat.Reasoning D
    module F = Func F

    module ↓colim c' =
      cocomplete→lan.↓colim (よ C) F cocompl c'
```
-->

```agda
  Realisation⊣Nerve : Realisation F cocompl ⊣ Nerve F
  Realisation⊣Nerve = adj where

    open _⊣_
    open ↓Obj
    open ↓Hom

    hom′ : (P : Functor (C ^op) (Sets κ)) (i : C.Ob)
         → (arg : ∣ P .F₀ i ∣)
         → ↓Obj (よ C) _
    hom′ P i arg .x = i
    hom′ P i arg .y = tt
    hom′ P i arg .map .η j h = P .F₁ h arg
    hom′ P i arg .map .is-natural _ _ f = funext λ _ → happly (P .F-∘ _ _) _

    adj : Realisation F cocompl ⊣ Nerve F
    adj .unit .η P .η i arg =
      ↓colim.ψ P (hom′ P i arg)
    adj .unit .η P .is-natural x y f =
      funext λ _ →
        sym $ ↓colim.commutes P $ ↓hom (Nat-path λ _ → funext λ _ → P .F-∘ _ _ $ₚ _)
    adj .unit .is-natural x y f =
      Nat-path λ i → funext λ arg →
        sym $ ↓colim.factors _ {j = hom′ x i arg} _ _
        ∙ ap (↓colim.ψ _) (↓Obj-path _ _ refl refl
                             (Nat-path λ _ → funext λ _ → f .is-natural _ _ _ $ₚ _))

    adj .counit .η ob =
      ↓colim.universal _
        (λ j → j .map .η (x j) C.id)
        (λ {x} {y} f →
          sym (y .map .is-natural _ _ _ $ₚ _)
          ·· ap (y .map .η _) C.id-comm-sym
          ·· f .sq ηₚ _ $ₚ _)
    adj .counit .is-natural x y f =
      ↓colim.unique₂ _ _
        (λ {x'} {y'} f →
          D.pullr (sym (y' .map .is-natural _ _ _ $ₚ _)
                   ∙ ap (y' .map .η _) C.id-comm-sym)
          ∙ ap (_ D.∘_) (f .sq ηₚ _ $ₚ C.id))
        (λ j →
          D.pullr (↓colim.factors _ _ _)
          ∙ ↓colim.factors _ _ _)
        (λ j → D.pullr (↓colim.factors _ _ _))

    adj .zig {A} =
      ↓colim.unique₂ A _
      (λ f → ↓colim.commutes _ f)
        (λ j →
          D.pullr (↓colim.factors _ _ _)
          ∙ ↓colim.factors _ _ _
          ∙ ap (↓colim.ψ _)
              (↓Obj-path _ _ refl refl
                (Nat-path λ _ → funext λ _ →
                   sym (j .map .is-natural _ _ _ $ₚ _)
                   ∙ ap (j .map .η _) (C.idl _))))
        (λ j → D.idl _)
          
    adj .zag {d} =
      Nat-path λ c → funext λ f →
        ↓colim.factors (Nerve F .F₀ d) {j = hom′ _ c f} _ _
        ∙ F.elimr refl
```
