<!--
```agda
open import Cat.Displayed.Instances.Factorisations
open import Cat.Instances.Shape.Interval
open import Cat.Instances.Coalgebras
open import Cat.Displayed.Section
open import Cat.Diagram.Comonad
open import Cat.Morphism.Lifts
open import Cat.Diagram.Monad
open import Cat.Prelude

import Cat.Reasoning

open Functor
open Section
open _=>_
```
-->

```agda
module Cat.Morphism.Factorisation.Algebraic where
```

# Algebraic weak factorisation systems

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} (F : Factorisation C) where
  open Cat.Reasoning C
  open Factorisation F
```
-->

:::{.definition #left-weak-factorisation-structure}
A **left weak factorisation structure** on a [[functorial
factorisation]] $F$ is an extension of the [[left factor functor]] $(L,
\eps)$ into a [[comonad]] on $\Arr{\cC}$.
:::

```agda
  record Lwfs-on : Type (o ⊔ ℓ) where
    field
      L-δ       : L => L F∘ L
      L-comonad : is-comonad L-ε L-δ

    open is-comonad L-comonad using (ε ; δ ; δ-unitl ; δ-unitr ; δ-assoc ; module counit ; module comult) public

    𝕃 : Comonad-on L
    𝕃 = record { has-is-comonad = L-comonad }
```

:::{.definition #right-weak-factorisation-structure}
A **right weak factorisation structure** on a [[functorial
factorisation]] $F$ is an extension of the [[right factor functor]] $(R,
\eta)$ into a [[monad]] on $\Arr{\cC}$.
:::

```agda
  record Rwfs-on : Type (o ⊔ ℓ) where
    field
      R-μ     : R F∘ R => R
      R-monad : is-monad R-η R-μ

    open is-monad R-monad using (η ; μ ; μ-unitl ; μ-unitr ; μ-assoc ; module unit ; module mult) public

    ℝ : Monad-on R
    ℝ = record { has-is-monad = R-monad }
```

:::{.definition #algebraic-weak-factorisation-system alias="awfs"}
An **algebraic weak factorisation system** on $\cC$ is a [[functorial
factorisation]] $F$ which is simultaneously equipped with [[left|left
weak factorisation structure]] and [[right weak factorisation
structures]].
:::

```agda
  record Awfs-on : Type (o ⊔ ℓ) where
    field
      awfsᴸ : Lwfs-on
      awfsᴿ : Rwfs-on

    open Lwfs-on awfsᴸ public
    open Rwfs-on awfsᴿ public
```

The most important consequence of $L$ being a comonad and $R$ being a
monad is that any map with an $L$-coalgebra structure lifts against maps
with $R$-algebras.

```agda
    L-R-lifts
      : ∀ {a b x y} {f : Hom a b} {g : Hom x y}
      → Coalgebra-on 𝕃 (_ , _ , f)
      → Algebra-on ℝ (_ , _ , g)
      → ∀ {u v} → v ∘ f ≡ g ∘ u → Lifting C f g u v
    L-R-lifts {f = f} {g = g} Lf Rg {u} {v} vf=gu = record where
      module f = Coalgebra-on Lf
      module g = Algebra-on Rg
      open Interpolant (F .S₁ record{ com = sym vf=gu })
        renaming (map to h ; sq₀ to α ; sq₁ to β)

      rem₁ : g ∘ g.ν .top ≡ ρ→ g
      rem₁ = g.ν .com ∙ eliml (intror refl ∙ ap bot g.ν-unit)

      rem₂ : f.ρ .bot ∘ f ≡ λ→ f
      rem₂ = sym (intror (introl refl ∙ ap top f.ρ-counit) ∙ f.ρ .com)

      fst = g.ν .top ∘ h ∘ f.ρ .bot
      snd = pullr (pullr rem₂) ∙ pushr (sym α) ∙ eliml (ap top g.ν-unit)
          , pulll rem₁ ∙ extendl β ∙ elimr (ap bot f.ρ-counit)
```

<!--
```agda
module Lwfs {o ℓ} {C : Precategory o ℓ} {F : Factorisation C} (Fl : Lwfs-on F) where
  open Cat.Reasoning C

  -- First a bunch of combinators (and projections, w/ display forms)
  -- for the comonad structure on a Lwfs that abstract away the square
  -- bits.
  private
    open module Ff = Factorisation F public
    module F = Lwfs-on Fl
  module _ {x y} (f : Hom x y) where open Homᵃ (F.δ (x , y , f)) renaming (bot to δ) public

  δˢ : ∀ {x y} (f : Hom x y) → Homᵃ C (λ→ f) (λ→ (λ→ f))
  δˢ f = F.δ (_ , _ , f)

  abstract
    δ-top : ∀ {x y} {f : Hom x y} → δˢ f .top ≡ id
    δ-top = introl refl ∙ ap top F.δ-unitl

    δ-unitl : ∀ {x y} {f : Hom x y} → Ff.map (L-ε .η (_ , _ , f)) ∘ δ f ≡ id
    δ-unitl = ap bot F.δ-unitl

    δ-unitr : ∀ {x y} {f : Hom x y} → ρ→ (λ→ f) ∘ δ f ≡ id
    δ-unitr = ap bot F.δ-unitr

    δ-assoc : ∀ {x y} {f : Hom x y} → Ff.map (δˢ f) ∘ δ f ≡ δ (λ→ f) ∘ δ f
    δ-assoc {f = f} = ap bot F.δ-assoc

    δ-nat
      : ∀ {u v x y} {f : Hom u v} {g : Hom x y} (σ : Homᵃ C f g)
      → Ff.map (L .F₁ σ) ∘ δ f ≡ δ g ∘ Ff.map σ
    δ-nat σ = sym (ap bot (F.comult.is-natural _ _ σ))
```
-->

## Lifts in a lwfs

```agda
  whisker-ρ : ∀ {u v w x} {f : Hom u v} {g : Hom w x} → Homᵃ C f g → Homᵃ C f (ρ→ g)
  whisker-ρ sq .top = λ→ _ ∘ sq .top
  whisker-ρ sq .bot = sq .bot
  whisker-ρ sq .com = pulll (sym (factors _)) ∙ sq .com

  lift-λρ
    : ∀ {u v w x} {f : Hom u v} {g : Hom w x} (σ : Homᵃ C (λ→ f) g)
    → Square-lift (whisker-ρ σ)
  lift-λρ {f = f} {g} σ = record { snd = α , β } where abstract
    α : (Ff.map σ ∘ δ f) ∘ λ→ f ≡ λ→ g ∘ σ .top
    α = pullr (sym (δˢ f .com) ∙ elimr δ-top) ∙ sym (F .S₁ σ .sq₀)

    β : ρ→ g ∘ Ff.map σ ∘ δ f ≡ σ .bot
    β = pulll (F .S₁ σ .sq₁) ∙ cancelr δ-unitr
```
