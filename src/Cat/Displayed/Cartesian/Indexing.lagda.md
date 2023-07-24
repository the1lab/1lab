<!--
```agda
{-# OPTIONS --lossy-unification #-}
open import Cat.Bi.Instances.Discrete
open import Cat.Displayed.Cartesian
open import Cat.Instances.Discrete
open import Cat.Instances.Functor
open import Cat.Displayed.Fibre
open import Cat.Displayed.Base
open import Cat.Bi.Base
open import Cat.Prelude

import Cat.Displayed.Reasoning
import Cat.Reasoning
import Cat.Morphism as Mor
import Cat.Displayed.Fibre.Reasoning
```
-->

```agda
module Cat.Displayed.Cartesian.Indexing
  {o ℓ o′ ℓ′} {B : Precategory o ℓ}
  (E : Displayed B o′ ℓ′)
  (cartesian : Cartesian-fibration E)
  where
```

<!--
```agda
open Cartesian-fibration cartesian
open Cat.Displayed.Reasoning E
open Cat.Reasoning B
open Cartesian-lift
open Displayed E
open is-cartesian
open Functor
private
  module Fib = Cat.Displayed.Fibre.Reasoning E
```
-->

# Reindexing for Cartesian fibrations

A [cartesian fibration] can be thought of as a [displayed category]
$\cE$ whose [fibre categories] $\cE^*(b)$ depend
([pseudo])functorially on the object $b : \cB$ from the base
category. A canonical example is [the canonical self-indexing]: If
$\cC$ is a category with [pullbacks], then each $b \xto{f} a :
\cC$ gives rise to [a functor] $\cC/a \to \cC/b$, the _change
of base_ along $f$.

[cartesian fibration]: Cat.Displayed.Cartesian.html
[displayed category]: Cat.Displayed.Base.html
[fibre categories]: Cat.Displayed.Fibre.html
[pseudo]: Cat.Bi.Base.html#pseudofunctors
[the canonical self-indexing]: Cat.Displayed.Instances.Slice.html
[pullbacks]: Cat.Diagram.Pullback.html
[a functor]: Cat.Functor.Pullback.html

```agda
module _ {𝒶 𝒷} (f : Hom 𝒶 𝒷) where
  base-change : Functor (Fibre E 𝒷) (Fibre E 𝒶)
  base-change .F₀ ob = has-lift f ob .x′
  base-change .F₁ {x} {y} vert = rebase f vert
```

<!--
```agda
  base-change .F-id {x} =
    sym $ has-lift.uniquep f x _ _ _ _ $
      idr′ _ ∙[] symP (idl′ _)

  base-change .F-∘ {x} {y} {z} f′ g′ =
    sym $ has-lift.uniquep f z _ _ _ _ $
      Fib.pulllf (has-lift.commutesp f z id-comm _)
      ∙[] pullr[] _ (has-lift.commutesp f y id-comm _)
      ∙[] pulll[] _ Fib.to-fibre
```
-->

Moreover, this assignment is _itself_ functorial in $f$: Along the
identity morphism, it's the same thing as not changing bases at all.

```agda
module _ {𝒶} where
  private
    module FC = Cat.Reasoning (Cat[ Fibre E 𝒶 , Fibre E 𝒶 ])
    module Fa = Cat.Reasoning (Fibre E 𝒶)

  base-change-id : base-change id FC.≅ Id
```

<details>
<summary> I'll warn you in advance that this proof is not for the faint
of heart. </summary>
```agda
  base-change-id = to-natural-iso mi where
    open make-natural-iso
    mi : make-natural-iso (base-change id) Id
    mi .eta x = has-lift.lifting id x
    mi .inv x = has-lift.universalv id x id′
    mi .eta∘inv x = cancel _ _ (has-lift.commutesv _ _ _)
    mi .inv∘eta x = sym $
      has-lift.uniquep₂ id x _ _ _ _ _
        (idr′ _)
        (Fib.cancellf (has-lift.commutesv _ _ _))
    mi .natural x y f =
      sym $ from-pathp $ cast[] $
        has-lift.commutesp id y id-comm _
        ∙[] Fib.to-fibre
```
</details>

And similarly, composing changes of base is the same thing as changing
base along a composite.

```agda
module _ {𝒶} {𝒷} {𝒸} (f : Hom 𝒷 𝒸) (g : Hom 𝒶 𝒷) where
  private
    module FC = Cat.Reasoning (Cat[ Fibre E 𝒸 , Fibre E 𝒶 ])
    module Fa = Cat.Reasoning (Fibre E 𝒶)

  base-change-comp : base-change (f ∘ g) FC.≅ (base-change g F∘ base-change f)
```

<details>
<summary> This proof is a truly nightmarish application of universal
properties and I recommend that nobody look at it, ever. </summary>.

```agda
  base-change-comp = to-natural-iso mi where
    open make-natural-iso
    mi : make-natural-iso (base-change (f ∘ g)) (base-change g F∘ base-change f)
    mi .eta x =
      has-lift.universalv g _ $ has-lift.universal f x g (has-lift.lifting (f ∘ g) x)
    mi .inv x =
      has-lift.universalv (f ∘ g) x (has-lift.lifting f _ ∘′ has-lift.lifting g _)
    mi .eta∘inv x =
      has-lift.uniquep₂ _ _ _ _ _ _ _
        (Fib.pulllf (has-lift.commutesv g _ _)
         ∙[] has-lift.uniquep₂ _ _ _ (idr _) refl _ _
           (pulll[] _ (has-lift.commutes _ _ _ _)
            ∙[] has-lift.commutesv _ _ _)
           refl)
        (idr′ _)
    mi .inv∘eta x =
      has-lift.uniquep₂ _ _ _ _ _ _ _
        (Fib.pulllf (has-lift.commutesv _ _ _)
         ∙[] pullr[] _ (has-lift.commutesv _ _ _)
         ∙[] has-lift.commutes _ _ _ _)
        (idr′ _)
    mi .natural x y f′ =
      ap hom[] $ cartesian→weak-monic E (has-lift.cartesian g _) _ _ $ cast[] $
        pulll[] _ (has-lift.commutesp g _ id-comm _)
        ∙[] pullr[] _ (has-lift.commutesv g _ _)
        ∙[] has-lift.uniquep₂ _ _ _ id-comm-sym _ _ _
          (pulll[] _ (has-lift.commutesp _ _ id-comm _)
           ∙[] pullr[] _ (has-lift.commutes _ _ _ _))
          (pulll[] _ (has-lift.commutes _ _ _ _)
           ∙[] has-lift.commutesp _ _ id-comm _)
        ∙[] pushl[] _ (symP (has-lift.commutesv g _ _))
```
</details>

<!--
```agda
-- Optimized natural iso, avoids a bunch of junk from composition.
base-change-square
  : ∀ {Γ Δ Θ Ψ : Ob}
  → {σ : Hom Γ Δ} {δ : Hom Γ Θ} {γ : Hom Δ Ψ} {τ : Hom Θ Ψ}
  → γ ∘ σ ≡ τ ∘ δ
  → natural-iso (base-change σ F∘ base-change γ) (base-change δ F∘ base-change τ)
base-change-square {σ = σ} {δ = δ} {γ = γ} {τ = τ} p =
  to-natural-iso ni where

  open make-natural-iso
  ni : make-natural-iso _ _ 
  ni .eta x =
    has-lift.universalv δ _ $
    has-lift.universal′ τ _ (sym p) $
    has-lift.lifting γ x ∘′ has-lift.lifting σ _
  ni .inv x =
    has-lift.universalv σ _ $
    has-lift.universal′ γ _ p $
    has-lift.lifting τ x ∘′ has-lift.lifting δ _
  ni .eta∘inv x =
    has-lift.uniquep₂ _ _ _ _ _ _ _
      (Fib.pulllf (has-lift.commutesv δ _ _)
       ∙[] has-lift.uniquep₂ τ x _ (idr _) refl _ _
         (pulll[] _ (has-lift.commutesp τ x (sym p) _)
          ∙[] pullr[] _ (has-lift.commutesv σ _ _)
          ∙[] has-lift.commutesp γ x p _)
         refl)
      (idr′ _)
  ni .inv∘eta x =
    has-lift.uniquep₂ _ _ _ _ _ _ _
      (Fib.pulllf (has-lift.commutesv σ _ _)
       ∙[] has-lift.uniquep₂ γ x _ (idr _) refl _ _
         (pulll[] _ (has-lift.commutesp γ _ p _)
          ∙[] pullr[] _ (has-lift.commutesv δ _ _)
          ∙[] has-lift.commutesp τ x (sym p) _)
         refl)
      (idr′ _)
  ni .natural x y f =
    has-lift.uniquep₂ _ _ _ _ _ _ _
      (Fib.pulllf (has-lift.commutesp δ _ id-comm _)
       ∙[] pullr[] _ (has-lift.commutesv δ _ _)
       ∙[] has-lift.uniquep τ y _ (idl _) (sym p ∙ sym (idl _)) _
         (pulll[] _ (has-lift.commutesp _ _ id-comm _ )
          ∙[] pullr[] _ (has-lift.commutesp _ _ (sym p) _)))
      (Fib.pulllf (has-lift.commutesv δ _ _)
       ∙[] has-lift.uniquep₂ τ y _ (idr _) _ _ _
         (pulll[] _ (has-lift.commutesp τ _ (sym p) _)
          ∙[] pullr[] _ (has-lift.commutesp σ _ id-comm _)
          ∙[] extendl[] _ (has-lift.commutesp γ _ id-comm _))
         (has-lift.commutesp τ _ (sym p ∙ sym (idl _ )) _))
```
-->
