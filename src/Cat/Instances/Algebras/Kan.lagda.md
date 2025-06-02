<!--
```agda
open import Cat.Diagram.Monad.Action
open import Cat.Functor.Conservative
open import Cat.Functor.Adjoint.Kan
open import Cat.Functor.Coherence
open import Cat.Instances.Functor
open import Cat.Functor.Kan.Base
open import Cat.Displayed.Total
open import Cat.Diagram.Monad
open import Cat.Prelude

import Cat.Functor.Reasoning
import Cat.Reasoning

open Algebra-on
open Action-on
open Total-hom
open lifts-ran
open Functor
open _=>_
```
-->

```agda
module Cat.Instances.Algebras.Kan where
```

# Right Kan extensions in categories of algebras {defines="kan-extensions-in-categories-of-algebras"}

<!--
```agda
module _
    {o ℓ o' o'' ℓ' ℓ''}
    {C : Precategory o ℓ} {F : Functor C C} (M : Monad-on F)
    {J : Precategory o' ℓ'} {D : Precategory o'' ℓ''} (p : Functor J D)
    where

  private
    module EM = Cat.Reasoning (Eilenberg-Moore M)
    module C = Cat.Reasoning C
    module M = Monad-on M
    module p = Functor p
```
-->

The construction of [[limits in categories of algebras]] from limits in
the base category generalises to arbitrary [[right Kan extensions]].
We start by showing that the forgetful functor $U : \cC^M \to C$
[[lifts right Kan extensions]].

The setup is as follows: given a right Kan extension $\rm{Ext}$ of
$UG$ along $p$, we want to construct a right Kan extension $\rm{Ext}^M$
of $G$ along $p$.

~~~{.quiver}
\[\begin{tikzcd}
  {\mathcal{J}} & {\mathcal{C}^M} & {\mathcal{C}} \\
  {\mathcal{D}}
  \arrow["G", from=1-1, to=1-2]
  \arrow["p"', from=1-1, to=2-1]
  \arrow["U", from=1-2, to=1-3]
  \arrow["{\mathrm{Ext}^M}"{description}, dashed, from=2-1, to=1-2]
  \arrow["{\mathrm{Ext}}"', from=2-1, to=1-3]
\end{tikzcd}\]
~~~

```agda
  Forget-EM-lift-ran
    : ∀ {G : Functor J (Eilenberg-Moore M)}
    → Ran p (Forget-EM F∘ G)
    → Ran p G
  Forget-EM-lift-ran {G} ran-over = to-ran has-ran^M
    where
      open Ran ran-over
      module G = Functor G
      module MR = Cat.Functor.Reasoning F
```

The first step is to construct the functor $\rm{Ext}^M : \cD \to \cC^M$.
Since this Kan extension is supposed to be [[preserved|preserved Kan extension]] by
$U$, we know that $\rm{Ext}^M$ should lift $\rm{Ext}$ along $U$; hence,
thanks to the universal property of $\cC^M$, $\rm{Ext}^M$ is entirely
specified by the data of a [[monad action]] of $M$ on $\rm{Ext}$.

The natural transformation $M \circ \rm{Ext} \To \rm{Ext}$ is defined
using the universal property of $\rm{Ext}$: it suffices to give a
map $M \circ \rm{Ext} \circ p \To U \circ G$, which we construct as
in the following diagram:

~~~{.quiver}
\[\begin{tikzcd}
  && {\mathcal{C}} \\
  {\mathcal{J}} & {\mathcal{C}^M} & {\mathrm{C}} \\
  {\mathcal{D}}
  \arrow["G", from=2-1, to=2-2]
  \arrow["p"', from=2-1, to=3-1]
  \arrow[""{name=0, anchor=center, inner sep=0}, "U", from=2-2, to=1-3]
  \arrow["U"{description}, from=2-2, to=2-3]
  \arrow["M"', from=2-3, to=1-3]
  \arrow[Rightarrow, from=3-1, to=2-2]
  \arrow["{\mathrm{Ext}}"', from=3-1, to=2-3]
  \arrow[shorten >=2pt, Rightarrow, from=2-3, to=0]
\end{tikzcd}\]
~~~

```agda
      Ext-action : Action-on M Ext
      Ext-action .α = σ $
        nat-unassoc-from (Forget-EM-action M .α ◂ G) ∘nt
        nat-assoc-from (F ▸ eps)
```

Checking the algebra laws involves the uniqueness part of the universal
property and some tedious computations.

```agda
      Ext-action .α-unit = σ-uniq₂ eps eq (ext λ _ → sym (C.idr _))
        where
          eq : eps ≡ eps ∘nt (Ext-action .α ∘nt nat-idl-from (M.unit ◂ Ext) ◂ p)
          eq = ext λ j → sym $
            eps .η j C.∘ Ext-action .α .η (p.₀ j) C.∘ M.η (Ext.₀ (p.₀ j)) ≡⟨ C.extendl (σ-comm ηₚ j) ⟩
            G.₀ j .snd .ν C.∘ M.M₁ (eps .η j) C.∘ M.η (Ext.₀ (p.₀ j))     ≡˘⟨ C.refl⟩∘⟨ M.unit .is-natural _ _ _ ⟩
            G.₀ j .snd .ν C.∘ M.η (G.₀ j .fst) C.∘ eps .η j               ≡⟨ C.cancell (G.₀ j .snd .ν-unit) ⟩
            eps .η j                                                      ∎

      Ext-action .α-mult = σ-uniq₂ _ eq refl
        where
          eq : _ ≡ eps ∘nt ((Ext-action .α ∘nt nat-unassoc-from (M.mult ◂ Ext)) ◂ p)
          eq = ext λ j →
            eps .η j C.∘ Ext-action .α .η (p.₀ j) C.∘ M.M₁ (Ext-action .α .η (p.₀ j)) ≡⟨ C.extendl (σ-comm ηₚ j) ⟩
            G.₀ j .snd .ν C.∘ M.M₁ (eps .η j) C.∘ M.M₁ (Ext-action .α .η (p.₀ j))     ≡⟨ C.refl⟩∘⟨ MR.weave (σ-comm ηₚ j) ⟩
            G.₀ j .snd .ν C.∘ M.M₁ (G.₀ j .snd .ν) C.∘ M.M₁ (M.M₁ (eps .η j))         ≡˘⟨ C.extendl (G.₀ j .snd .ν-mult) ⟩
            G.₀ j .snd .ν C.∘ M.μ (G.₀ j .fst) C.∘ M.M₁ (M.M₁ (eps .η j))             ≡⟨ C.refl⟩∘⟨ M.mult .is-natural _ _ _ ⟩
            G.₀ j .snd .ν C.∘ M.M₁ (eps .η j) C.∘ M.μ (Ext.₀ (p.₀ j))                 ≡˘⟨ C.extendl (σ-comm ηₚ j) ⟩
            eps .η j C.∘ Ext-action .α .η (p.₀ j) C.∘ M.μ (Ext.₀ (p.₀ j))             ∎

      Ext^M : Functor D (Eilenberg-Moore M)
      Ext^M = EM-universal M Ext-action
```

The universal natural transformation $\rm{Ext} \circ p \To U \circ  G$
extends to a natural transformation $\rm{Ext}^M \circ p \To G$.

```agda
      eps^M : Ext^M F∘ p => G
      eps^M .η j .hom = eps .η j
      eps^M .η j .preserves = σ-comm ηₚ j
      eps^M .is-natural _ _ _ = ext (eps .is-natural _ _ _)
```

It remains to check universality, which is another short computation.

```agda
      has-ran^M : is-ran p G Ext^M eps^M
      has-ran^M .is-ran.σ {M = X} c =
        EM-2-cell' M σ^M (σ-uniq₂ _ refl eq)
        where
          module X = Functor X

          σ^M : Forget-EM F∘ X => Ext
          σ^M = σ (nat-assoc-from (Forget-EM ▸ c))

          eq : _ ≡ eps ∘nt ((Ext-action .α ∘nt (F ▸ σ^M)) ◂ p)
          eq = ext λ j →
            eps .η j C.∘ σ^M .η (p.₀ j) C.∘ X.₀ (p.₀ j) .snd .ν             ≡⟨ C.pulll (σ-comm ηₚ j) ⟩
            c .η j .hom C.∘ X.₀ (p.₀ j) .snd .ν                             ≡⟨ c .η j .preserves ⟩
            G.₀ j .snd .ν C.∘ M.M₁ (c .η j .hom)                            ≡˘⟨ C.refl⟩∘⟨ MR.collapse (σ-comm ηₚ j) ⟩
            G.₀ j .snd .ν C.∘ M.M₁ (eps .η j) C.∘ M.M₁ (σ^M .η (p.₀ j))     ≡˘⟨ C.extendl (σ-comm ηₚ j) ⟩
            eps .η j C.∘ Ext-action .α .η (p.₀ j) C.∘ M.M₁ (σ^M .η (p.₀ j)) ∎

      has-ran^M .is-ran.σ-comm {β = c} = ext (unext σ-comm)
      has-ran^M .is-ran.σ-uniq {X} {σ' = σ'} eq =
        reext! (σ-uniq {σ' = U∘σ'} (reext! eq))
        where
          U∘σ' : Forget-EM F∘ X => Ext
          U∘σ' = cohere! (Forget-EM ▸ σ')
```

Since $U$ is a right adjoint, this Kan extension is automatically
preserved; and since $U$ is conservative, we can conclude that it
[[creates right Kan extensions]].

```agda
  Forget-EM-preserves-ran
    : ∀ {G : Functor J (Eilenberg-Moore M)}
    → preserves-ran p G Forget-EM
  Forget-EM-preserves-ran = right-adjoint→preserves-ran Free-EM⊣Forget-EM

  Forget-EM-lifts-ran : lifts-ran-along p (Forget-EM {M = M})
  Forget-EM-lifts-ran ran .lifted = Forget-EM-lift-ran ran
  Forget-EM-lifts-ran ran .preserved = Forget-EM-preserves-ran
    (Ran.has-ran (Forget-EM-lift-ran ran))

  Forget-EM-creates-ran : creates-ran-along p (Forget-EM {M = M})
  Forget-EM-creates-ran = conservative+lifts→creates-ran
    Forget-EM-is-conservative Forget-EM-lifts-ran
```
