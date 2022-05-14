---
description: |
  We use the calculation of left Kan extensions as certain colimits to
  associate a "nerve" (restricted Yoneda embedding) and "realization"
  (left Kan extension along よ) adjunction given any functor.
---

```agda
open import Cat.Instances.Shape.Terminal
open import Cat.Diagram.Colimit.Base
open import Cat.Instances.Functor
open import Cat.Diagram.Initial
open import Cat.Functor.Adjoint
open import Cat.Instances.Comma
open import Cat.Functor.Hom
open import Cat.Functor.Kan
open import Cat.Prelude

import Cat.Functor.Reasoning as Functor-kit
import Cat.Reasoning

module Cat.Functor.Kan.Nerve where
```

<!--
```agda
private
  variable o κ : Level
open Functor
open _=>_
```
-->

# Nerve and realisation

Let $F : \ca{C} \to \ca{D}$ be a functor from a [$\kappa$-small] category
$\ca{C}$ to a locally $\kappa$-small, $\kappa$-[cocomplete] category
$\ca{D}$. $F$ induces a pair of [adjoint functors], as in the diagram
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
is the ordinary realisation of a simplicial set $[\Delta^op,\sets]$ as a
strict category, and the right adjoint gives the simplicial nerve of a
strict category.

[strict categories]: Cat.Instances.StrictCat.html
[poset]: Cat.Instances.Thin.html

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
module _ {κ o} {C : Precategory o κ} where
  private module C = Cat.Reasoning C
```
-->

```agda
  Nerve : {D : Precategory κ κ} → Functor D C → Functor C (PSh κ D)
  Nerve F .F₀ x .F₀ y    = C.Hom (F .F₀ y) x , C.Hom-set _ _
  Nerve F .F₀ x .F₁ f g  = g C.∘ F .F₁ f
  Nerve F .F₀ x .F-id    = funext λ x → C.elimr (F .F-id)
  Nerve F .F₀ x .F-∘ f g = funext λ x → C.pushr (F .F-∘ _ _)

  Nerve F .F₁ f .η _ g            = f C.∘ g
  Nerve F .F₁ _ .is-natural _ _ _ = funext λ _ → C.assoc _ _ _

  Nerve F .F-id    = Nat-path λ _ → funext λ _ → C.idl _
  Nerve F .F-∘ f g = Nat-path λ _ → funext λ _ → sym (C.assoc _ _ _)
```

The realisation left adjoint is constructed by general abstract
nonsense.

<!--
```agda
module _ {C : Precategory o κ} (cocompl : is-cocomplete κ κ C) where
  private module C = Cat.Reasoning C
  open Initial
  open Cocone-hom
  open Cocone
```
-->

```agda
  Realisation : {D : Precategory κ κ} → Functor D C → Functor (PSh κ D) C
  Realisation {D} F = cocomplete→lan cocompl F (よ D) .Lan.Ext

  Realisation⊣Nerve
    : {D : Precategory κ κ} (F : Functor D C)
    → Realisation F ⊣ Nerve F
```

The construction of the nerve-realisation adjunction is done below in
components, but understanding it is not necessary: Either ponder the
$\Delta \mono \strcat$ example from above, or take it as a foundational
assumption. However, if you're feeling particularly brave, feel free to
look at the code. Godspeed.

```agda
  Realisation⊣Nerve {D = D} F = adj where
    module D = Cat.Reasoning D
    open _⊣_
    open ↓Obj
    open ↓Hom
    module F = Functor-kit F

    hom′ : (P : Functor (D ^op) (Sets κ)) (i : D.Ob)
         → (arg : ∣ P .F₀ i ∣)
         → ↓Obj (よ D) _
    hom′ P i arg .x = i
    hom′ P i arg .y = tt
    hom′ P i arg .map .η j h = P .F₁ h arg
    hom′ P i arg .map .is-natural _ _ f = funext λ _ → happly (P .F-∘ _ _) _

    cocone′ : ∀ ob → Cocone (F F∘ Dom (よ D) (const! (Nerve F .F₀ ob)))
    cocone′ ob .coapex = ob
    cocone′ ob .ψ obj = obj .map .η _ D.id
    cocone′ ob .commutes {x} {y} f =
      happly (sym (y .map .is-natural _ _ _)) _
      ∙ ap (y .map .η (x .↓Obj.x)) (sym D.id-comm)
      ∙ happly (ap (λ e → e .η (x .↓Obj.x)) (f .sq)) _
```

Before proceeding, take a moment to appreciate the beauty of the
adjunction unit and counit, and you'll see that it _makes sense_ that
nerve and realisation are adjoints: The unit is given by the
coprojections defining the left Kan extension as a colimit, and the
counit is given by the unique "colimiting" map _from_ that colimit.

```agda
    adj : Realisation F ⊣ Nerve F
    adj .unit .η P .η i arg = cocompl _ .bot .ψ (hom′ P i arg)
    adj .counit .η ob       = cocompl _ .has⊥ (cocone′ ob) .centre .hom

    adj .unit .η P .is-natural x y f = funext λ arg →
      sym (cocompl _ .bot .commutes {x = obj′ arg}
          ( record { sq = Nat-path (λ _ → refl) })
          ∙ ap (cocompl _ .bot .ψ)
            (↓Obj-path _ _ refl refl
              (Nat-path λ _ → funext λ _ → happly (P .F-∘ _ _) _)))
      where
        obj′ : ∀ arg → ↓Obj (よ _) _
        obj′ arg .↓Obj.x = y
        obj′ arg .↓Obj.y = tt
        obj′ arg .map .η j h = P .F₁ (f D.∘ h) arg
        obj′ arg .map .is-natural X Y F = funext λ A →
            happly (P .F-∘ _ _) _
          ∙ happly (P .F-∘ _ _) _
          ∙ λ i → P .F₁ F (P .F-∘ A f (~ i) arg)

    adj .unit .is-natural x y f = Nat-path λ i → funext λ arg → sym $
      cocompl (F F∘ Dom (よ D) (const! x)) .has⊥ (lan-approximate cocompl _ _ f)
        .centre .commutes (hom′ x i arg)
      ∙ ap (cocompl _ .bot .ψ)
           (↓Obj-path _ _ refl refl
              (Nat-path λ _ → funext λ _ → happly (f .is-natural _ _ _) _))

    adj .counit .is-natural x y f = ap hom $
      is-contr→is-prop
        (cocompl (F F∘ Dom (よ D) (const! (Nerve F .F₀ x))) .has⊥ cocone₂)
        (cocone-hom _ λ o →
            C.pullr (cocompl _ .has⊥ (lan-approximate cocompl _ _ _)
                      .centre .commutes _)
          ∙ cocompl _ .has⊥ (cocone′ y) .centre .commutes _)
        (cocone-hom _ λ o →
          C.pullr (cocompl _ .has⊥ (cocone′ x) .centre .commutes _))
      where
        cocone₂ : Cocone _
        cocone₂ .coapex = y
        cocone₂ .ψ ob = f C.∘ ob .map .η _ D.id
        cocone₂ .commutes {x₂} {y₂} f =
          C.pullr ( sym (happly (y₂ .map .is-natural _ _ _) _)
                  ∙ ap (y₂ .map .η _) (sym D.id-comm))
          ∙ ap (_ C.∘_) (happly (ap (λ e → e .η (x₂ .↓Obj.x)) (f .sq)) D.id)

    adj .zig {A} = ap hom $
      is-contr→is-prop (cocompl (F F∘ Dom (よ D) (const! A)) .has⊥ (cocompl _ .bot))
        (cocone-hom _ λ o →
            C.pullr (cocompl _ .has⊥ (lan-approximate cocompl _ _ _)
                               .centre .commutes _)
          ∙ cocompl _ .has⊥ (cocone′ _) .centre .commutes _
          ∙ ap (cocompl (F F∘ Dom (よ D) (const! A)) .bot .ψ)
                  (↓Obj-path _ _ _ refl (Nat-path λ x → funext λ _ →
                      sym (happly (o .map .is-natural _ _ _) _)
                    ∙ ap (o .map .η x) (D.idl _))))
        (cocone-hom _ λ o → C.idl _)

    adj .zag {B} = Nat-path λ x → funext λ a →
        cocompl (F F∘ Dom (よ D) (const! (Nerve F .F₀ B))) .has⊥ (cocone′ B)
          .centre .commutes (hom′ _ x a)
      ∙ F.elimr refl
```
