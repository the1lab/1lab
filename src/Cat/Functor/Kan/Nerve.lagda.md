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
open import Cat.Functor.Hom.Coyoneda
open import Cat.Functor.Kan.Base
open import Cat.Instances.Comma
open import Cat.Instances.Elements
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
open Element
open Element-hom
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

[left Kan extension]: Cat.Functor.Kan.html
[Yoneda embedding]: Cat.Functor.Hom.html
[computed]: Cat.Functor.Kan.html#a-formula

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
  {o κ} {C : Precategory κ κ} {D : Precategory o κ}
  (F : Functor C D)
  (cocompl : is-cocomplete κ κ D)
  where
    private
      module C = Cat.Reasoning C
      module D = Cat.Reasoning D
      module F = Func F
      module colim (P : Functor (C ^op) (Sets κ)) =
        Colimit (cocompl (F F∘ πₚ C P))
      module coyoneda (P : Functor (C ^op) (Sets κ)) =
        is-colimit (coyoneda C P)
```
-->

```agda
    Realisation : Functor (PSh κ C) D
    Realisation .F₀ = colim.coapex
    Realisation .F₁ {P} {Q} f =
      colim.universal _
        (λ j → colim.ψ Q (elem (j .ob) (f .η _ (j .section))))
        (λ g → colim.commutes Q
          (elem-hom (g .hom)
              (sym (f .is-natural _ _ _) $ₚ _
               ∙ ap (f .η _) (g .commute))))
    Realisation .F-id =
      sym $ colim.unique _ _ _ _ λ j →
        D.idl _
    Realisation .F-∘ f g =
      sym $ colim.unique _ _ _ _ λ j →
        D.pullr (colim.factors _ _ _)
        ∙ colim.factors _ _ _

    approx : F => Realisation F∘ よ C
    approx .η x = colim.ψ _ (elem x C.id) 
    approx .is-natural x y f =
      colim.commutes _ (elem-hom f C.id-comm-sym)
       ∙ sym (colim.factors _ _ _)

    Realisation-is-lan : is-lan (よ C) F Realisation approx
    Realisation-is-lan .σ {M = M} α .η P = 
      colim.universal P
        (λ j → M .F₁ (coyoneda.ψ P j) D.∘ α .η (j .ob))
        λ f →
          D.pullr (α .is-natural _ _ _)
          ∙ pulll M (coyoneda.commutes P f)
    Realisation-is-lan .σ {M = M} α .is-natural P Q f =
      colim.unique₂ P _
        (λ g →
          D.pullr (α .is-natural _ _ _)
          ∙ pulll M (coyoneda.commutes _ (elem-hom (g .hom) (sym (f .is-natural _ _ _ $ₚ _) ∙ ap (f .η _) (g .commute)))))
        (λ j →
          D.pullr (colim.factors P _ _)
          ∙ colim.factors Q _ _)
        (λ j →
          D.pullr (colim.factors P _ _)
          ∙ pulll M (Nat-path (λ _ → funext λ x → f .is-natural _ _ _ $ₚ j .section)))
    Realisation-is-lan .σ-comm {M = M} =
      Nat-path λ _ →
        colim.factors _ _ _
        ∙ eliml M (Nat-path (λ _ → funext λ _ → C.idl _))
    Realisation-is-lan .σ-uniq {M = M} {α = α} {σ′ = σ′} p =
      Nat-path λ P →
      sym $ colim.unique _ _ _ _ λ j →
        σ′ .η _ D.∘ colim.ψ P j                                     ≡⟨ D.pushr (sym (colim.factors _ _ _ ∙ ap (colim.ψ _) (ap₂ elem refl (P .F-id $ₚ _)))) ⟩
        (σ′ .η _ D.∘ colim.universal _ _ _) D.∘ colim.ψ (よ₀ C _) _ ≡⟨ D.pushl (σ′ .is-natural _ _ _) ⟩
        M .F₁ (coyoneda.ψ P j) D.∘ σ′ .η _ D.∘ colim.ψ (よ₀ C _) _  ≡˘⟨ (D.refl⟩∘⟨ (p ηₚ _)) ⟩
        M .F₁ (coyoneda.ψ P j) D.∘ α .η _                           ∎

--   Realisation⊣Nerve
--     : {D : Precategory κ κ} (F : Functor D C)
--     → Realisation F ⊣ Nerve F
-- ```

-- The construction of the nerve-realisation adjunction is done below in
-- components, but understanding it is not necessary: Either ponder the
-- $\Delta \mono \strcat$ example from above, or take it as a foundational
-- assumption. However, if you're feeling particularly brave, feel free to
-- look at the code. Godspeed.

-- ```agda
--   Realisation⊣Nerve {D = D} F = adj where
--     module D = Cat.Reasoning D
--     open _⊣_
--     open ↓Obj
--     open ↓Hom
--     module F = Functor-kit F

--     hom′ : (P : Functor (D ^op) (Sets κ)) (i : D.Ob)
--          → (arg : ∣ P .F₀ i ∣)
--          → ↓Obj (よ D) _
--     hom′ P i arg .x = i
--     hom′ P i arg .y = tt
--     hom′ P i arg .map .η j h = P .F₁ h arg
--     hom′ P i arg .map .is-natural _ _ f = funext λ _ → happly (P .F-∘ _ _) _

--     Shape : (c : C.Ob) → Functor (よ D ↘ Nerve F .F₀ c) C
--     Shape c = F F∘ Dom (よ D) (const! (Nerve F .F₀ c))

--     cocone′ : ∀ ob → Cocone (Shape ob)
--     cocone′ ob .coapex = ob
--     cocone′ ob .ψ obj = obj .map .η _ D.id
--     cocone′ ob .commutes {x} {y} f =
--         sym (y .map .is-natural _ _ _) $ₚ _
--       ∙ ap (y .map .η (x .↓Obj.x)) D.id-comm-sym
--       ∙ f .sq ηₚ _ $ₚ _
-- ```

-- Before proceeding, take a moment to appreciate the beauty of the
-- adjunction unit and counit, and you'll see that it _makes sense_ that
-- nerve and realisation are adjoints: The unit is given by the
-- coprojections defining the left Kan extension as a colimit, and the
-- counit is given by the unique "colimiting" map _from_ that colimit.

-- ```agda
--     adj : Realisation F ⊣ Nerve F
--     adj .unit .η P .η i arg = cocompl _ .bot .ψ (hom′ P i arg)
--     adj .counit .η ob       = cocompl _ .has⊥ (cocone′ ob) .centre .hom

--     adj .unit .η P .is-natural x y f = funext λ arg →
--       sym $ cocompl (F F∘ Dom (よ D) (Const P)) .bot .commutes
--         (record { sq = Nat-path (λ _ → funext λ _ → P .F-∘ _ _ $ₚ _) })

--     adj .unit .is-natural x y f = Nat-path λ i → funext λ arg → sym $
--       cocompl (F F∘ Dom (よ D) (Const x)) .has⊥ (lan-approximate cocompl (よ D) F f)
--         .centre .commutes (hom′ x i arg)
--       ∙ ap (cocompl (F F∘ Dom (よ D) (Const y)) .bot .ψ)
--         (↓Obj-path _ _ refl refl (Nat-path λ _ → funext λ _ → f .is-natural _ _ _ $ₚ _))

--     adj .counit .is-natural x y f = ap hom $
--       is-contr→is-prop (cocompl _  .has⊥ cocone₂)
--         (cocone-hom _ λ o →
--           C.pullr (cocompl (Shape x) .has⊥ _ .centre .commutes o)
--           ∙ cocompl (Shape y) .has⊥ (cocone′ _) .centre .commutes _)
--         (cocone-hom _ λ o →
--           C.pullr (cocompl _ .has⊥ (cocone′ x) .centre .commutes _))
--       where
--         cocone₂ : Cocone (Shape x)
--         cocone₂ .coapex = y
--         cocone₂ .ψ ob = f C.∘ ob .map .η _ D.id
--         cocone₂ .commutes {x₂} {y₂} f =
--           C.pullr ( sym (happly (y₂ .map .is-natural _ _ _) _)
--                   ∙ ap (y₂ .map .η _) (sym D.id-comm))
--           ∙ ap (_ C.∘_) (f .sq ηₚ _ $ₚ D.id)

--     adj .zig {A} = ap hom $
--       is-contr→is-prop (cocompl (F F∘ Dom (よ D) (const! A)) .has⊥ (cocompl _ .bot))
--         (cocone-hom _ λ o → C.pullr (
--             cocompl (F F∘ Dom (よ D) (Const A)) .has⊥ _ .centre .commutes o)
--         ·· cocompl (Shape (Realisation F .F₀ A)) .has⊥ _ .centre .commutes _
--         ·· ap (cocompl (F F∘ Dom (よ D) (const! A)) .bot .ψ)
--                 {x = hom′ A (o .x) (o .map .η (o .x) D.id)}
--                 (↓Obj-path _ _ _ refl (Nat-path λ x → funext λ _ →
--                   sym (o .map .is-natural _ _ _ $ₚ _) ∙ ap (o .map .η x) (D.idl _))))
--         (cocone-hom _ λ o → C.idl _)

--     adj .zag {B} = Nat-path λ x → funext λ a →
--         cocompl (F F∘ Dom (よ D) (const! (Nerve F .F₀ B))) .has⊥ (cocone′ B)
--           .centre .commutes (hom′ _ x a)
--       ∙ F.elimr refl
-- ```
