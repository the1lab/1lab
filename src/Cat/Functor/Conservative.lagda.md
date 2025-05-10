<!--
```agda
open import Cat.Diagram.Colimit.Base
open import Cat.Diagram.Limit.Base
open import Cat.Morphism.Duality
open import Cat.Morphism
open import Cat.Prelude hiding (J)

import Cat.Functor.Reasoning as Func
import Cat.Reasoning as Cat
```
-->

```agda
module Cat.Functor.Conservative where
```

<!--
```agda
private variable
  o h o₁ h₁ : Level
  C D J : Precategory o h
open Precategory
open Functor
```
-->

# Conservative functors {defines="conservative conservative-functor"}

We say a functor is _conservative_ if it reflects isomorphisms. More concretely,
if $f : A \to B$ is some morphism $\cC$, and if $F(f)$ is an iso in $\cD$,
then $f$ must have already been an iso in $\cC$!

```agda
is-conservative : Functor C D → Type _
is-conservative {C = C} {D = D} F =
  ∀ {A B} {f : C .Hom A B}
  → is-invertible D (F .F₁ f) → is-invertible C f
```

As a general fact, conservative functors reflect limits and colimits that
they preserve (given those (co)limits exist in the first place!).

The rough proof sketch is as follows: let $K$ be some cone in $\cC$ such
that $F(K)$ is a limit in $\cD$, and $L$ a limit in $\cC$ of the same
diagram that is preserved by $F$.
By the universal property of $L$, there exists a map $\eta$ from the apex of $K$
to the apex of $L$ in $\cC$. Furthermore, as $F(K)$ is a limit in $\cD$, $F(\eta)$
becomes an isomorphism in $\cD$.
The situation is summarised by the following diagram, which shows how $F$
maps cones in $\cC$ to cones in $\cD$ (the coloured cones are assumed to
be limiting).

~~~{.quiver}
\[\begin{tikzcd}
  K & \textcolor{rgb,255:red,214;green,92;blue,214}{L} \\
  \textcolor{rgb,255:red,214;green,92;blue,214}{F(K)} & \textcolor{rgb,255:red,214;green,92;blue,214}{F(L)}
  \arrow[maps to, from=1-2, to=2-2]
  \arrow[maps to, from=1-1, to=2-1]
  \arrow[""{name=0, anchor=center, inner sep=0}, "\eta", from=1-1, to=1-2]
  \arrow[""{name=1, anchor=center, inner sep=0}, "\sim"', from=2-1, to=2-2]
  \arrow[shorten <=4pt, shorten >=4pt, maps to, from=0, to=1]
\end{tikzcd}\]
~~~

However, $F$ is conservative, which implies that
$\eta$ was an isomorphism in $\cC$ all along! This means that $K$ must be a limit
in $\cC$ as well (see `is-invertible→is-limitp`{.Agda}).

```agda
module _ {F : Functor C D} (conservative : is-conservative F) where
  private
    open _=>_
    module C = Cat C
    module D = Cat D
    module F = Func F

  conservative-reflects-limits
    : ∀ {Dia : Functor J C}
    → Limit Dia
    → preserves-limit F Dia
    → reflects-limit F Dia
  conservative-reflects-limits L-lim preservesa {K} {eps} FK-lim =
    is-invertible→is-limitp
      {K = Limit.Ext L-lim} {epsy = Limit.cone L-lim} (Limit.has-limit L-lim)
      (eps .η) (λ f → sym (eps .is-natural _ _ f) ∙ C.elimr (K .F-id)) refl
      $ conservative
      $ invert

    where
      module L-lim = Limit L-lim
      module FL-lim = is-limit (preservesa L-lim.has-limit)
      module FK-lim = is-limit FK-lim

      uinv : D.Hom (F .F₀ L-lim.apex) (F .F₀ (K .F₀ tt))
      uinv =
        FK-lim.universal
          (λ j → F .F₁ (L-lim.ψ j))
          (λ f → sym (F .F-∘ _ _) ∙ ap (F .F₁) (L-lim.commutes f))

      invert : D.is-invertible (F .F₁ (L-lim.universal (eps .η) _))
      invert =
        D.make-invertible uinv
          (FL-lim.unique₂ _ (λ j → FL-lim.commutes j)
            (λ j → F.pulll (L-lim.factors _ _) ∙ FK-lim.factors _ _)
            (λ j → D.idr _))
          (FK-lim.unique₂ _ (λ j → FK-lim.commutes j)
            (λ j → D.pulll (FK-lim.factors _ _) ∙ F.collapse (L-lim.factors _ _))
            (λ j → D.idr _))
```

<!--
```agda
  conservative→equiv :
    ∀ {A B} {f : C .Hom A B}
    → C.is-invertible f ≃ D.is-invertible (F .F₁ f)
  conservative→equiv = prop-ext! F.F-map-invertible conservative

  conservative^op : is-conservative F.op
  conservative^op inv
    = invertible→co-invertible C
    $ conservative
    $ co-invertible→invertible D inv
```
-->

<details>
<summary>
Clearly, if $F$ is conservative then so is $F\op$, so the statement
about colimits follows by duality.

```agda
  conservative-reflects-colimits
    : ∀ {Dia : Functor J C}
    → Colimit Dia
    → preserves-colimit F Dia
    → reflects-colimit F Dia
```
</summary>

```agda
  conservative-reflects-colimits C-colim preservesa {K} {eta} FK-colim =
    is-invertible→is-colimitp
      {K = Colimit.Ext C-colim} {etay = Colimit.cocone C-colim} (Colimit.has-colimit C-colim)
      (eta .η) (λ f → eta .is-natural _ _ f ∙ C.eliml (K .F-id)) refl
      $ conservative
      $ invert

    where
      module C-colim = Colimit C-colim
      module FC-colim = is-colimit (preservesa C-colim.has-colimit)
      module FK-colim = is-colimit FK-colim

      uinv : D.Hom (F .F₀ (K .F₀ tt)) (F .F₀ C-colim.coapex)
      uinv =
        FK-colim.universal
          (λ j → F .F₁ (C-colim.ψ j))
          (λ f → sym (F .F-∘ _ _) ∙ ap (F .F₁) (C-colim.commutes f))

      invert : D.is-invertible (F .F₁ (C-colim.universal (eta .η) _))
      invert =
        D.make-invertible uinv
          (FK-colim.unique₂ _ (λ j → FK-colim.commutes j)
            (λ j → D.pullr (FK-colim.factors _ _) ∙ F.collapse (C-colim.factors _ _))
            (λ j → D.idl _))
          (FC-colim.unique₂ _ (λ j → FC-colim.commutes j)
            (λ j → F.pullr (C-colim.factors _ _) ∙ FK-colim.factors _ _)
            (λ j → D.idl _))
```
</details>
