<!--
```agda
{-# OPTIONS --allow-unsolved-metas #-}
open import Cat.Functor.Naturality.Reflection
open import Cat.Diagram.Pullback.Properties
open import Cat.Functor.Adjoint.Continuous
open import Cat.Instances.Shape.Terminal
open import Cat.CartesianClosed.Locally
open import Cat.Instances.Slice.Colimit
open import Cat.Functor.Kan.Reflection
open import Cat.Diagram.Colimit.Base
open import Cat.Diagram.Limit.Finite
open import Cat.Instances.Shape.Join
open import Cat.Functor.Kan.Unique
open import Cat.Functor.Naturality
open import Cat.Diagram.Pullback
open import Cat.Functor.Constant
open import Cat.Functor.Kan.Base
open import Cat.Functor.Pullback
open import Cat.Functor.Compose
open import Cat.Instances.Slice
open import Cat.Functor.Base
open import Cat.Prelude

open import Data.Sum

import Cat.Functor.Bifunctor as Bifunctor
import Cat.Reasoning

open creates-colimit
open lifts-colimit
open Functor
open _=>_
```
-->

```agda
module Cat.Diagram.Colimit.Universal where
```

# Universal colimits {defines="universal-colimit pullback-stable-colimit"}

A [[colimit]] in a category $\cC$ with [[pullbacks]] is said to be
**universal**, or **stable under pullback**, if it is preserved under
[[base change|pullback functor]].

There are multiple ways to make this precise. First, we might consider
pulling back a colimiting cocone --- say, for the sake of concreteness,
a coproduct diagram $A \to A + B \ot B$ --- along some morphism $f : X \to A + B$:

~~~{.quiver}
\[\begin{tikzcd}
  {f^* A} & X & {f^* B} \\
  A & {A+B} & B
  \arrow[from=1-1, to=1-2]
  \arrow[from=1-1, to=2-1]
  \arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=1-1, to=2-2]
  \arrow["f", from=1-2, to=2-2]
  \arrow[from=1-3, to=1-2]
  \arrow["\lrcorner"{anchor=center, pos=0.125, rotate=-90}, draw=none, from=1-3, to=2-2]
  \arrow[from=1-3, to=2-3]
  \arrow[from=2-1, to=2-2]
  \arrow[from=2-3, to=2-2]
\end{tikzcd}\]
~~~

We say that the bottom colimit is **universal** if the top
cocone $f^* A \to X \ot f^* B$ is also colimiting for all $f$.

Alternatively, we might consider pulling back a colimiting cocone in $\cC/Y$
along some morphism $f : X \to Y$ like so:

~~~{.quiver}
\[\begin{tikzcd}
  {f^* A} & {f^*(A + B)} & {f^* B} \\
  & X \\
  & Y \\
  A & {A+B} & B
  \arrow[from=1-1, to=1-2]
  \arrow[from=1-1, to=2-2]
  \arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=1-1, to=3-2]
  \arrow[from=1-1, to=4-1]
  \arrow[from=1-2, to=2-2]
  \arrow[from=1-3, to=1-2]
  \arrow[from=1-3, to=2-2]
  \arrow["\lrcorner"{anchor=center, pos=0.125, rotate=-90}, draw=none, from=1-3, to=3-2]
  \arrow[from=1-3, to=4-3]
  \arrow["f", from=2-2, to=3-2]
  \arrow[from=4-1, to=3-2]
  \arrow[from=4-1, to=4-2]
  \arrow[from=4-2, to=3-2]
  \arrow[from=4-3, to=3-2]
  \arrow[from=4-3, to=4-2]
\end{tikzcd}\]
~~~

In this case, we say that the colimit is **stable under pullback** if
the top diagram is colimiting in $\cC/X$, which amounts to saying that every
[[pullback functor]] $f^* : \cC/Y \to \cC/X$ preserves this colimit.

<!--
```agda
module _ {oj ℓj oc ℓc}
  (J : Precategory oj ℓj)
  (C : Precategory oc ℓc)
  (pb : has-pullbacks C)
  where
  open Precategory C
```
-->

```agda
  has-stable-colimits : Type _
  has-stable-colimits =
    ∀ {X Y} (f : Hom X Y) (F : Functor J (Slice C Y))
    → preserves-colimit (Base-change pb f) F
```

::: note
This definition makes sense even if not all pullback functors exist; however,
for the sake of simplicity, we assume that $\cC$ has all pullbacks.
:::

## Universality vs. pullback-stability

If $\cC$ has all colimits of shape $\cJ$, we can show that the two
notions are equivalent.

::: source
This is essentially a 1-categorical version of the proof of lemma 6.1.3.3
in Higher Topos Theory [@HTT].
:::

We start by noticing that a cocone under $F$ with coapex $X$ in $\cC$ can
equivalently be described as a functor $\cJ^\triangleright \to \cC$ that
sends the [[adjoined terminal object]] of $\cJ^\triangleright$ to $X$ and
otherwise restricts to $F$.

<!--
```agda
module _ {oj ℓj oc ℓc} {J : Precategory oj ℓj} {C : Precategory oc ℓc} where
  open Cat.Reasoning C
  open /-Obj
  open /-Hom
```
-->

```agda
  cocone→cocone▹
    : ∀ {X} {F : Functor J C} → F => X F∘ !F → Functor (J ▹) C
  cocone▹→cocone
    : (F : Functor (J ▹) C) → F F∘ ▹-in => Const (F .F₀ (inr _))

  is-colimit▹ : Functor (J ▹) C → Type _
  is-colimit▹ F = is-colimit (F F∘ ▹-in) (F .F₀ (inr _)) (cocone▹→cocone F)
```

Yet another way of describing a cocone with coapex $X$ is as a functor
$\cJ \to \cC/X$ into the [[slice category]] over $X$:

```agda
  cocone/→cocone▹
    : ∀ {X} → Functor J (Slice C X) → Functor (J ▹) C
  cocone▹→cocone/
    : (F : Functor (J ▹) C) → Functor J (Slice C (F .F₀ (inr _)))
```

<details>
<summary>The proofs are by simple data repackaging.</summary>

```agda
  cocone→cocone▹ {X} {F} α .F₀ (inl j) = F .F₀ j
  cocone→cocone▹ {X} {F} α .F₀ (inr tt) = X .F₀ _
  cocone→cocone▹ {X} {F} α .F₁ {inl x} {inl y} (lift f) = F .F₁ f
  cocone→cocone▹ {X} {F} α .F₁ {inl x} {inr tt} (lift f) = α .η x
  cocone→cocone▹ {X} {F} α .F₁ {inr tt} {inr tt} (lift tt) = id
  cocone→cocone▹ {X} {F} α .F-id {inl x} = F .F-id
  cocone→cocone▹ {X} {F} α .F-id {inr x} = refl
  cocone→cocone▹ {X} {F} α .F-∘ {inl x} {inl y} {inl z} f g = F .F-∘ _ _
  cocone→cocone▹ {X} {F} α .F-∘ {inl x} {inl y} {inr z} f g =
    sym (α .is-natural _ _ _ ∙ eliml (X .F-id))
  cocone→cocone▹ {X} {F} α .F-∘ {inl x} {inr y} {inr z} f g = sym (idl _)
  cocone→cocone▹ {X} {F} α .F-∘ {inr x} {inr y} {inr z} f g = sym (idl _)

  cocone▹→cocone F .η j = F .F₁ _
  cocone▹→cocone F .is-natural x y f = sym (F .F-∘ _ _) ∙ sym (idl _)

  cocone/→cocone▹ F .F₀ (inl x) = F .F₀ x .dom
  cocone/→cocone▹ {X} F .F₀ (inr _) = X
  cocone/→cocone▹ F .F₁ {inl x} {inl y} (lift f) = F .F₁ f .map
  cocone/→cocone▹ F .F₁ {inl x} {inr _} f = F .F₀ x .map
  cocone/→cocone▹ F .F₁ {inr _} {inr _} f = id
  cocone/→cocone▹ F .F-id {inl x} = ap map (F .F-id)
  cocone/→cocone▹ F .F-id {inr _} = refl
  cocone/→cocone▹ F .F-∘ {inl x} {inl y} {inl z} f g = ap map (F .F-∘ _ _)
  cocone/→cocone▹ F .F-∘ {inl x} {inl y} {inr z} f (lift g) = sym (F .F₁ g .com)
  cocone/→cocone▹ F .F-∘ {inl x} {inr y} {inr z} f g = sym (idl _)
  cocone/→cocone▹ F .F-∘ {inr x} {inr y} {inr z} f g = sym (idl _)

  cocone▹→cocone/ F .F₀ j = cut {dom = F .F₀ (inl j)} (F .F₁ _)
  cocone▹→cocone/ F .F₁ f .map = F .F₁ (lift f)
  cocone▹→cocone/ F .F₁ f .com = sym (F .F-∘ _ _)
  cocone▹→cocone/ F .F-id = ext (F .F-id)
  cocone▹→cocone/ F .F-∘ f g = ext (F .F-∘ _ _)
```
</details>

Using this language, we can define what it means for $\cC$
to have universal colimits in the sense of the first diagram above:
for every equifibred natural transformation $\alpha : F \To G$ between
diagrams $\cJ^\triangleright \to \cC$, if $G$ is colimiting then $F$ is
colimiting.

<!--
```agda
module _ {oj ℓj oc ℓc}
  (J : Precategory oj ℓj)
  (C : Precategory oc ℓc)
  where
```
-->

```agda
  has-universal-colimits : Type _
  has-universal-colimits =
    ∀ (F G : Functor (J ▹) C) (α : F => G) → is-equifibred α
    → is-colimit▹ G → is-colimit▹ F
```

We will establish the equivalence between pullback-stable and universal
colimits in several steps. First, we show that pullback-stability is
equivalent to the following condition: for every diagram as below, that
is, for every [[equifibred]] natural transformation $\alpha : F \To G$
between diagrams $F, G : \cJ^{\triangleright\triangleright} \to \cC$,
if the bottom diagram $G$ (seen as a diagram $\cJ^\triangleright \to
\cC/Y$) is colimiting, then the top diagram $F$ (seen as a diagram
$\cJ^\triangleright \to \cC/X$) is colimiting.

~~~{.quiver}
\[\begin{tikzcd}
  U & W & V \\
  & X \\
  & Y \\
  A & C & B
  \arrow[from=1-1, to=1-2]
  \arrow[from=1-1, to=2-2]
  \arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=1-1, to=3-2]
  \arrow[from=1-1, to=4-1]
  \arrow[from=1-2, to=2-2]
  \arrow[from=1-3, to=1-2]
  \arrow[from=1-3, to=2-2]
  \arrow["\lrcorner"{anchor=center, pos=0.125, rotate=-90}, draw=none, from=1-3, to=3-2]
  \arrow[from=1-3, to=4-3]
  \arrow["f", from=2-2, to=3-2]
  \arrow[from=4-1, to=3-2]
  \arrow[from=4-1, to=4-2]
  \arrow[from=4-2, to=3-2]
  \arrow[from=4-3, to=3-2]
  \arrow[from=4-3, to=4-2]
\end{tikzcd}\]
~~~

<!--
```agda
module _ {oj ℓj oc ℓc}
  (J : Precategory oj ℓj)
  (C : Precategory oc ℓc)
  (pb : has-pullbacks C)
  where
  open Cat.Reasoning C
  open /-Obj
  open /-Hom
  open is-pullback
  private
    module C/ {X} = Cat.Reasoning (Slice C X)
```
-->

```agda
    step2 =
      ∀ (F G : Functor (J ▹ ▹) C) (α : F => G) → is-equifibred α
      → is-colimit▹ (cocone▹→cocone/ G) → is-colimit▹ (cocone▹→cocone/ F)
```

In the forwards direction, we use the uniqueness of pullbacks to
construct a natural isomorphism $f^* \circ G \cong F : \cJ^\triangleright
\to \cC/X$; since the pullback functor $f^*$ is assumed to preserve
colimits, we get that $F$ is colimiting.

```agda
    step1→2 : has-stable-colimits J C pb → step2
    step1→2 u F G α eq G-colim = F-colim where
      f = α .η (inr _)

      f*G≅F : Base-change pb f F∘ cocone▹→cocone/ G F∘ ▹-in
            ≅ⁿ cocone▹→cocone/ F F∘ ▹-in
      f*G≅F = iso→isoⁿ
        (λ j → C/.invertible→iso
          (record { map = eq _ .universal (sym (pb _ _ .Pullback.square))
                  ; com = eq _ .p₁∘universal })
          (Forget/-is-conservative (pullback-unique
            (rotate-pullback (eq _)) (pb _ _ .Pullback.has-is-pb))))
        λ f → ext (unique₂ (eq _)
          {p = sym (pb _ _ .Pullback.square) ∙ pushl (G .F-∘ _ _)}
          (pulll (sym (F .F-∘ _ _)) ∙ eq _ .p₁∘universal)
          (pulll (α .is-natural _ _ _) ∙ pullr (eq _ .p₂∘universal))
          (pulll (eq _ .p₁∘universal) ∙ pb _ _ .Pullback.p₂∘universal)
          (pulll (eq _ .p₂∘universal) ∙ pb _ _ .Pullback.p₁∘universal))

      f*G-colim : preserves-is-lan (Base-change pb f) G-colim
      f*G-colim = u f _ G-colim

      F-colim : is-colimit▹ (cocone▹→cocone/ F)
      F-colim = natural-isos→is-lan idni
        f*G≅F
        (!const-isoⁿ (C/.invertible→iso
          (record { map = eq _ .universal (sym (pb _ _ .Pullback.square))
                  ; com = eq _ .p₁∘universal })
          (Forget/-is-conservative (pullback-unique
            (rotate-pullback (eq _)) (pb _ _ .Pullback.has-is-pb)))))
        ( ap₂ _∘nt_ (Bifunctor.lrmap F∘-functor _ _) refl
        ∙ ext λ j → (idl _ ⟩∘⟨refl) ∙ unique₂ (eq _)
            {p = eq _ .square ∙ pushl (G .F-∘ _ _)}
            (pulll (eq _ .p₁∘universal) ∙∙ pulll (pb _ _ .Pullback.p₂∘universal) ∙∙ pb _ _ .Pullback.p₂∘universal)
            (pulll (eq _ .p₂∘universal) ∙∙ pulll (pb _ _ .Pullback.p₁∘universal) ∙∙ pullr (pb _ _ .Pullback.p₁∘universal))
            (sym (F .F-∘ _ _))
            (α .is-natural _ _ _))
        f*G-colim
```

For the converse direction, we build a natural transformation from the
pullback of $G$ to $G$ and show that it is equifibred using the
[[pasting law for pullbacks]]. The rest of the proof consists in
repackaging data between "obviously isomorphic" functors.

```agda
    step2→1 : step2 → has-stable-colimits J C pb
    step2→1 u f F {K} {eta} = {! trivial-is-colimit! ⊙ u _ _ α eq ⊙ trivial-is-colimit! !}
      where
        α : cocone/→cocone▹ (Base-change pb f F∘ cocone→cocone▹ eta)
         => cocone/→cocone▹ (cocone→cocone▹ eta)
        α .η (inl j) = pb _ _ .Pullback.p₁
        α .η (inr _) = f
        α .is-natural (inl x) (inl y) g = pb _ _ .Pullback.p₁∘universal
        α .is-natural (inl x) (inr _) g = sym (pb _ _ .Pullback.square)
        α .is-natural (inr _) (inr _) g = id-comm

        eq : is-equifibred α
        eq {inl x} {inl y} (lift g) = pasting-outer→left-is-pullback
          (rotate-pullback (pb _ _ .Pullback.has-is-pb))
          (subst₂ (λ x y → is-pullback C x f (pb _ _ .Pullback.p₁) y)
            (sym ((Base-change pb f F∘ cocone→cocone▹ eta) .F₁ g .com))
            (sym (cocone→cocone▹ eta .F₁ g .com))
            (rotate-pullback (pb _ _ .Pullback.has-is-pb)))
          (α .is-natural (inl x) (inl y) (lift g))
        eq {inl x} {inr _} g = rotate-pullback (pb _ _ .Pullback.has-is-pb)
        eq {inr _} {inr _} g = id-is-pullback
```

Next, we prove that this is equivalent to requiring that the top
diagram $\cJ^\triangleright \to \cC$ be colimiting if the bottom
diagram $\cJ^\triangleright \to \cC$ is colimiting, disregarding
the $X \to Y$ part entirely.

```agda
    step3 =
      ∀ (F G : Functor (J ▹ ▹) C) (α : F => G) → is-equifibred α
      → is-colimit▹ (G F∘ ▹-in) → is-colimit▹ (F F∘ ▹-in)
```

This follows from the characterisation of [[colimits in slice categories]]:
assuming that all $\cJ$-colimits exist in $\cC$, the forgetful functor
$\cC/X \to \cC$ both preserves and reflects colimits.

```agda
    module _ (J-colims : ∀ (F : Functor J C) → Colimit F) where
      colim/≃colim
        : (F : Functor (J ▹ ▹) C)
        → is-colimit▹ (cocone▹→cocone/ F) ≃ is-colimit▹ (F F∘ ▹-in)
      colim/≃colim F =
        prop-ext!
          (lifts→preserves-colimit (Forget/-lifts-colimits (J-colims _)))
          (Forget/-creates-colimits .reflects)
        ∙e {! trivial-colimit-equiv! !}

      step2≃3 : step2 ≃ step3
      step2≃3 = Π-ap-cod λ F → Π-ap-cod λ G → Π-ap-cod λ α → Π-ap-cod λ eq →
        →-ap (colim/≃colim G) (colim/≃colim F)
```

Finally, we show that this is equivalent to $\cC$ having universal colimits.
This follows easily by noticing that $\cJ^{\triangleright\triangleright}$
retracts onto $\cJ^\triangleright$.

```agda
    step3→4 : step3 → has-universal-colimits J C
    step3→4 u F G α eq = Equiv.to (→-ap (▹-retract G) (▹-retract F))
      (u _ _ (α ◂ ▹-join) (◂-equifibred ▹-join α eq))
      where
        ▹-retract
          : (F : Functor (J ▹) C)
          → is-colimit▹ ((F F∘ ▹-join) F∘ ▹-in) ≃ is-colimit▹ F
        ▹-retract F = {! trivial-colimit-equiv! !}

    step4→3 : has-universal-colimits J C → step3
    step4→3 u F G α eq = u _ _ (α ◂ ▹-in) (◂-equifibred ▹-in α eq)
```

This concludes our equivalence.

```agda
  stable≃universal
    : (∀ (F : Functor J C) → Colimit F)
    → has-stable-colimits J C pb ≃ has-universal-colimits J C
  stable≃universal J-colims =
       prop-ext! step1→2 step2→1
    ∙e step2≃3 J-colims
    ∙e prop-ext! step3→4 step4→3
```

## Examples

As a general class of examples, any [[locally cartesian closed category]]
has pullback-stable colimits, because the pullback functor has a [[right
adjoint]] and therefore preserves colimits.

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} (lcc : Locally-cartesian-closed C) where
  open Locally-cartesian-closed lcc
  open Finitely-complete has-is-lex
```
-->

```agda
  lcc→stable-colimits
    : ∀ {oj ℓj} {J : Precategory oj ℓj}
    → has-stable-colimits J C pullbacks
  lcc→stable-colimits f F = left-adjoint-is-cocontinuous
    (lcc→pullback⊣dependent-product C lcc f)
```
