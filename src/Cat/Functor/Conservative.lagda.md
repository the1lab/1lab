<!--
```agda
open import Cat.Diagram.Limit.Base
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

# Conservative functors

We say a functor is _conservative_ if it reflects isomorphisms. More concretely,
if $f : A \to B$ is some morphism $\cC$, and if $F(f)$ is an iso in $\cD$,
then $f$ must have already been an iso in $\cC$!

```agda
is-conservative : Functor C D → Type _
is-conservative {C = C} {D = D} F =
  ∀ {A B} {f : C .Hom A B}
  → is-invertible D (F .F₁ f) → is-invertible C f
```

As a general fact, conservative functors reflect limits that they preserve
(given those limits exist in the first place!).

The rough proof sketch is as follows: Let $K$ be some cone in $C$ such that
$F(K)$ is a limit in $D$, and $L$ a limit in $C$ of the same diagram.
By the universal property of $L$, there exists a map $\eta$ from the apex of $K$
to the apex of $L$ in $C$. Furthermore, as $F(K)$ is a limit in $D$, $F(\eta)$
becomes an isomorphism in $D$. However, $F$ is conservative, which implies that
$\eta$ was an isomorphism in $C$ all along! This means that $K$ must be a limit
in $C$ as well (see `is-invertible→is-limitp`{.Agda}).

```agda
module _ {F : Functor C D} (conservative : is-conservative F) where
  private
    open _=>_
    module C = Cat C
    module D = Cat D
    module F = Func F

  conservative-reflects-limits : ∀ {Dia : Functor J C}
                               → (L : Limit Dia)
                               → preserves-limit F Dia
                               → reflects-limit F Dia
  conservative-reflects-limits L-lim preservesa {K} {eps} lim =
    is-invertible→is-limitp
      {K = Limit.Ext L-lim} {epsy = Limit.cone L-lim} (Limit.has-limit L-lim)
      (eps .η) (λ f → sym (eps .is-natural _ _ f) ∙ C.elimr (K .F-id)) refl
      $ conservative
      $ invert

    where
      module L-lim = Limit L-lim
      module FL-lim = is-limit (preservesa L-lim.has-limit)
      module lim = is-limit lim

      uinv : D.Hom (F .F₀ L-lim.apex) (F .F₀ (K .F₀ tt))
      uinv =
          (lim.universal
            (λ j → F .F₁ (L-lim.ψ j))
            (λ f → sym (F .F-∘ _ _) ∙ ap (F .F₁) (L-lim.commutes f)))

      invert : D.is-invertible (F .F₁ (L-lim.universal (eps .η) _))
      invert =
        D.make-invertible uinv
          (FL-lim.unique₂ _ (λ j → FL-lim.commutes j)
            (λ j → F.pulll (L-lim.factors _ _) ∙ lim.factors _ _)
            (λ j → D.idr _))
          (lim.unique₂ _ (λ j → lim.commutes j)
            (λ j → D.pulll (lim.factors _ _) ∙ F.collapse (L-lim.factors _ _))
            (λ j → D.idr _))
```
