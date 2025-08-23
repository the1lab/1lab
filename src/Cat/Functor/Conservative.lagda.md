<!--
```agda
open import Cat.Diagram.Colimit.Base
open import Cat.Diagram.Limit.Base
open import Cat.Functor.Kan.Unique
open import Cat.Functor.Naturality
open import Cat.Functor.Coherence
open import Cat.Functor.Kan.Base
open import Cat.Morphism.Duality
open import Cat.Functor.Compose
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
open lifts-limit
open creates-limit
open lifts-colimit
open creates-colimit
open creates-lan
open creates-ran
```
-->

# Conservative functors {defines="conservative conservative-functor"}

We say a functor is _conservative_ if it reflects [[isomorphisms]]. More concretely,
if $f : A \to B$ is some morphism $\cC$, and if $F(f)$ is an iso in $\cD$,
then $f$ must have already been an iso in $\cC$!

```agda
is-conservative : Functor C D → Type _
is-conservative {C = C} {D = D} F =
  ∀ {A B} {f : C .Hom A B}
  → is-invertible D (F .F₁ f) → is-invertible C f
```

## Conservative functors reflect (co)limits that they preserve

As a general fact, conservative functors [[reflect limits|reflected limit]]
and colimits that they preserve (given that those (co)limits exist in the
domain).

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
  conservative-reflects-limits L-lim preserves {K} {eps} FK-lim =
    is-invertible→is-limitp
      {K = Limit.Ext L-lim} {epsy = Limit.cone L-lim} (Limit.has-limit L-lim)
      (eps .η) (λ f → sym (eps .is-natural _ _ f) ∙ C.elimr (K .F-id)) refl
      $ conservative
      $ invert

    where
      module L-lim = Limit L-lim
      module FL-lim = is-limit (preserves L-lim.has-limit)
      module FK-lim = is-limit FK-lim

      uinv : D.Hom (F .F₀ L-lim.apex) (F .F₀ (K .F₀ tt))
      uinv =
        FK-lim.universal
          (λ j → F .F₁ (L-lim.ψ j))
          (λ f → sym (F .F-∘ _ _) ∙ ap (F .F₁) (L-lim.commutes f))

      invert : D.is-invertible (F .F₁ (L-lim.universal (eps .η) _))
      invert =
        D.make-invertible uinv
          (FL-lim.unique₂ FL-lim.ψ (λ j → FL-lim.commutes j)
            (λ j → F.pulll (L-lim.factors _ _) ∙ FK-lim.factors _ _)
            (λ j → D.idr _))
          (FK-lim.unique₂ FK-lim.ψ (λ j → FK-lim.commutes j)
            (λ j → D.pulll (FK-lim.factors _ _) ∙ F.collapse (L-lim.factors _ _))
            (λ j → D.idr _))
```

As a nice consequence, a conservative functor that [[lifts|lifted limit]]
a certain class of limits also [[creates|created limit]] those limits.

```agda
  conservative+lifts→creates-limits
    : ∀ {oj ℓj} {J : Precategory oj ℓj}
    → lifts-limits-of J F → creates-limits-of J F
  conservative+lifts→creates-limits F-lifts .has-lifts-limit = F-lifts
  conservative+lifts→creates-limits F-lifts .reflects lim =
    conservative-reflects-limits (lifted-lim .lifted) (lifts→preserves-limit lifted-lim) lim
    where lifted-lim = F-lifts (to-ran lim)
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
  conservative-reflects-colimits C-colim preserves {K} {eta} FK-colim =
    is-invertible→is-colimitp
      {K = Colimit.Ext C-colim} {etay = Colimit.cocone C-colim} (Colimit.has-colimit C-colim)
      (eta .η) (λ f → eta .is-natural _ _ f ∙ C.eliml (K .F-id)) refl
      $ conservative
      $ invert

    where
      module C-colim = Colimit C-colim
      module FC-colim = is-colimit (preserves C-colim.has-colimit)
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

  conservative+lifts→creates-colimits
    : ∀ {oj ℓj} {J : Precategory oj ℓj}
    → lifts-colimits-of J F → creates-colimits-of J F
  conservative+lifts→creates-colimits F-lifts .has-lifts-colimit = F-lifts
  conservative+lifts→creates-colimits F-lifts .reflects colim =
    conservative-reflects-colimits (lifted-colim .lifted) (lifts→preserves-colimit lifted-colim) colim
    where lifted-colim = F-lifts (to-lan colim)
```
</details>

## Conservative functors reflect Kan extensions that they preserve

We can generalise the results above to Kan extensions: conservative
functors automatically reflect any Kan extensions that exist and that
they preserve.

<!--
```agda
module _ {F : Functor C D} (conservative : is-conservative F) where
  private
    open _=>_
    module C = Cat C
    module D = Cat D
    module F = Func F
```
-->

```agda
  conservative-reflects-ran
    : ∀ {o ℓ} {J' : Precategory o ℓ} {p : Functor J J'} {Dia : Functor J C}
    → Ran p Dia
    → preserves-ran p Dia F
    → reflects-ran p Dia F

  conservative-reflects-lan
    : ∀ {o ℓ} {J' : Precategory o ℓ} {p : Functor J J'} {Dia : Functor J C}
    → Lan p Dia
    → preserves-lan p Dia F
    → reflects-lan p Dia F
```

We start with a lemma: if $F$ is a conservative
functor and $\alpha : G \To H$ is a natural transformation such that
$F \alpha : FG \To FH$ is invertible, then $\alpha$ is invertible;
this is immediate from the fact that invertibility of natural
transformations is a pointwise condition. Concisely, this means that
the [[postcomposition functor]] $F \circ -$ is conservative if $F$ is.

```agda
  conservative→postcompose-conservative
    : ∀ {o ℓ} {E : Precategory o ℓ}
    → is-conservative (postcompose F {D = E})
  conservative→postcompose-conservative inv =
    invertible→invertibleⁿ _ λ d →
      conservative (is-invertibleⁿ→is-invertible inv d)
```

<details>
<summary>The idea is then the same as for (co)limits.</summary>

```agda
  conservative-reflects-ran {p = p} {Dia} L-ran preserves {K} {eps} FK-ran =
    is-invertible→is-ran (Ran.has-ran L-ran)
    $ conservative→postcompose-conservative invert
    where
      module L-ran = Ran L-ran
      module FL-ran = is-ran (preserves L-ran.has-ran)
      module FK-ran = is-ran FK-ran

      F-eps : (F F∘ L-ran.Ext) F∘ p => F F∘ Dia
      F-eps = nat-assoc-from (F ▸ L-ran.eps)

      uinv : F F∘ L-ran.Ext => F F∘ K
      uinv = FK-ran.σ F-eps

      invert : is-invertibleⁿ (F ▸ L-ran.σ eps)
      invert = make-invertible _ uinv
        (FL-ran.σ-uniq₂ F-eps
          (ext λ j → sym $ F.pulll (L-ran.σ-comm ηₚ j) ∙ FK-ran.σ-comm ηₚ j)
          (ext λ j → sym (D.idr _)))
        (FK-ran.σ-uniq₂ (nat-assoc-from (F ▸ eps))
          (ext λ j → sym $ D.pulll (FK-ran.σ-comm ηₚ j) ∙ F.collapse (L-ran.σ-comm ηₚ j))
          (ext λ j → sym (D.idr _)))

  conservative-reflects-lan {p = p} {Dia} L-lan preserves {K} {eta} FK-lan =
    is-invertible→is-lan (Lan.has-lan L-lan)
    $ conservative→postcompose-conservative invert
    where
      module L-lan = Lan L-lan
      module FL-lan = is-lan (preserves L-lan.has-lan)
      module FK-lan = is-lan FK-lan

      F-eta : F F∘ Dia => (F F∘ L-lan.Ext) F∘ p
      F-eta = nat-assoc-to (F ▸ L-lan.eta)

      uinv : F F∘ K => F F∘ L-lan.Ext
      uinv = FK-lan.σ F-eta

      invert : is-invertibleⁿ (F ▸ L-lan.σ eta)
      invert = make-invertible _ uinv
        (FK-lan.σ-uniq₂ (nat-assoc-to (F ▸ eta))
          (ext λ j → sym $ D.pullr (FK-lan.σ-comm ηₚ j) ∙ F.collapse (L-lan.σ-comm ηₚ j))
          (ext λ j → sym (D.idl _)))
        (FL-lan.σ-uniq₂ F-eta
          (ext λ j → sym $ F.pullr (L-lan.σ-comm ηₚ j) ∙ FK-lan.σ-comm ηₚ j)
          (ext λ j → sym (D.idl _)))

  conservative+lifts→creates-ran
    : ∀ {o ℓ} {J' : Precategory o ℓ} {p : Functor J J'}
    → lifts-ran-along p F → creates-ran-along p F
  conservative+lifts→creates-ran F-lifts .has-lifts-ran = F-lifts
  conservative+lifts→creates-ran F-lifts .reflects ran =
    conservative-reflects-ran lifted-ran.lifted (lifts→preserves-ran lifted-ran) ran
    where
      lifted-ran = F-lifts (to-ran ran)
      module lifted-ran = lifts-ran lifted-ran

  conservative+lifts→creates-lan
    : ∀ {o ℓ} {J' : Precategory o ℓ} {p : Functor J J'}
    → lifts-lan-along p F → creates-lan-along p F
  conservative+lifts→creates-lan F-lifts .has-lifts-lan = F-lifts
  conservative+lifts→creates-lan F-lifts .reflects lan =
    conservative-reflects-lan lifted-lan.lifted (lifts→preserves-lan lifted-lan) lan
    where
      lifted-lan = F-lifts (to-lan lan)
      module lifted-lan = lifts-lan lifted-lan
```
</details>
