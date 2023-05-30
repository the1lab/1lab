<!--
```agda
open import Cat.Displayed.Base
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Cartesian.Indexing
open import Cat.Displayed.Functor
open import Cat.Displayed.Instances.Slice
open import Cat.Displayed.Total

open import Cat.Diagram.Comonad
open import Cat.Diagram.Pullback
open import Cat.Instances.Slice
open import Cat.Prelude

import Cat.Reasoning
import Cat.Displayed.Reasoning
```
-->

```agda
module Cat.Displayed.Comprehension
  {o ℓ o' ℓ'} {B : Precategory o ℓ}
  (E : Displayed B o' ℓ')
  where
```

<!--
```agda
open Cat.Reasoning B
open Displayed E
open Cat.Displayed.Reasoning E
open Functor
open _=>_
open Total-hom
open /-Obj
open Slice-hom
```
-->

# Comprehension Categories

Fibrations provide an excellent categorical framework for studying logic
and type theory, as they give us the tools required to describe objects
in a context, and substitutions between them. However, this framework
is missing a key ingredient: we have no way to describe context extension!

Before giving a definition, it is worth pondering what context extension
*does*. Consider some context $\Gamma$, and type
$\Gamma \vdash A\; \mathrm{type}$; context extension yields a new context
$\Gamma.A$ extended with a fresh variable of type $A$,
along with a substitution $\pi : \Gamma.A \to A$ that forgets this fresh
variable.

We also have a notion of substitution extension: Given any substitution
$\sigma : \Gamma \to \Delta$, types $\Gamma \vdash A\; \mathrm{type}$ and
$\Delta \vdash B\; \mathrm{type}$, and term
$\Gamma.A \vdash t : B[\sigma]$, there exists some substitution
$\sigma. t : \Gamma.A \to \Delta.B$ such that the following square commutes.

~~~{.quiver}
\begin{tikzcd}
  {\Gamma.A} && {\Delta.B} \\
  \\
  \Gamma && \Delta
  \arrow["\sigma", from=3-1, to=3-3]
  \arrow["\pi"', from=1-1, to=3-1]
  \arrow["{\sigma.t}", from=1-1, to=1-3]
  \arrow["\pi"', from=1-3, to=3-3]
\end{tikzcd}
~~~

Furthermore, when the term $t$ is simply a variable from $\Gamma$, this
square is a pullback square!

Now that we've got a general idea of how context extension ought to
behave, we can begin to categorify. Our first step is to replace the
category of contexts with an arbitrary category $\cB$, and the types
with some [fibration] $\cE$. We can then encode context extension
via a functor from $\cE$ to the [codomain fibration]. This is a somewhat
opaque definition, so it's worth unfolding somewhat. Note that the action
of such a functor on objects takes some object $x$ over $\Gamma$ in $\cE$
to a pair of an object we will suggestively name $\Gamma.A$ in $\cB$,
along with a map $\Gamma.A \to \Gamma$. Thus, the action on objects
yields both the extended context *and* the projection substitution. If we
inspect the action on morphisms of $\cE$, we see that it takes some
map $t : X \to_{\sigma} Y$ over $\sigma$ to a map $\sigma.t$ in $\cB$,
such that the following square commutes:

[fibration]: Cat.Displayed.Cartesian.html
[codomain fibration]: Cat.Displayed.Instances.Slices.html

~~~{.quiver}
\begin{tikzcd}
  {\Gamma.A} && {\Delta.B} \\
  \\
  \Gamma && \Delta
  \arrow["\sigma", from=3-1, to=3-3]
  \arrow["\pi"', from=1-1, to=3-1]
  \arrow["{\sigma.t}", from=1-1, to=1-3]
  \arrow["\pi"', from=1-3, to=3-3]
\end{tikzcd}
~~~

Note that this is the exact same square as above!

Furthermore, this functor ought to be [fibred]; this captures the
situation where extending a substitution with a variable yields a
pullback square.

[fibred]: Cat.Displayed.Functor.html

We call such a fibred functor a **comprehension structure** on $\cE$[^1].

[^1]: Other sources call such fibrations **comprehension categories**,
but this is a bit of a misnomer, as they are structures on fibrations!

```agda
Comprehension : Type _
Comprehension = Vertical-fibred-functor E (Slices B)
```

Now, let's make all that earlier intuition formal. Let $\cE$ be a fibration,
and $P$ be a comprehension structure on $\cE$. We begin by defining
context extensions, along with their associated projections.


```agda
module Comprehension (fib : Cartesian-fibration E) (P : Comprehension) where opaque
  open Vertical-fibred-functor P
  open Cartesian-fibration fib

  _⨾_ : ∀ Γ → Ob[ Γ ] → Ob
  Γ ⨾ x = F₀′ x .domain

  infixl 5 _⨾_

  _[_] : ∀ {Γ Δ} → Ob[ Δ ] → Hom Γ Δ → Ob[ Γ ]
  x [ σ ] =  base-change E fib σ .F₀ x

  πᶜ : ∀ {Γ x} → Hom (Γ ⨾ x) Γ
  πᶜ {x = x} = F₀′ x .map
```

As $\cE$ is a fibration, we can reindex along the projection to obtain a
notion of weakening.

```agda
  weaken : ∀ {Γ} → (x : Ob[ Γ ]) → Ob[ Γ ] → Ob[ Γ ⨾ x ]
  weaken x y = y [ πᶜ ]
```

Furthermore, if $y$ is an object over $\Gamma$, then we have a map over
`πᶜ` between from the weakened form of $y$ to $y$.


```agda
  πᶜ′ : ∀ {Γ} {x y : Ob[ Γ ]} → Hom[ πᶜ ] (weaken x y) y
  πᶜ′ = has-lift.lifting πᶜ _
```

Next, we define extension of substitutions, and show that they commute
with projections.

```agda
  _⨾ˢ_ : ∀ {Γ Δ x y} (σ : Hom Γ Δ) → Hom[ σ ] x y → Hom (Γ ⨾ x) (Δ ⨾ y)
  σ ⨾ˢ f = F₁′ f .to

  infixl 5 _⨾ˢ_

  sub-proj : ∀ {Γ Δ x y} {σ : Hom Γ Δ} → (f : Hom[ σ ] x y) → πᶜ ∘ (σ ⨾ˢ f) ≡ σ ∘ πᶜ
  sub-proj f = sym $ F₁′ f .commute
```

Crucially, when $f$ is cartesian, then the above square is a pullback.

```agda
  sub-pullback
    : ∀ {Γ Δ x y} {σ : Hom Γ Δ} {f : Hom[ σ ] x y}
    → is-cartesian E σ f
    → is-pullback B πᶜ σ (σ ⨾ˢ f) πᶜ
  sub-pullback {f = f} cart = cartesian→pullback B (F-cartesian f cart)
```

We also obtain a map over $\sigma.f$ between the weakenings of $x$ and
$y$, which also commutes with projections.

```agda
  _⨾ˢ′_
    : ∀ {Γ Δ x y} (σ : Hom Γ Δ) → (f : Hom[ σ ] x y)
    → Hom[ σ ⨾ˢ f ] (weaken x x) (weaken y y)
  σ ⨾ˢ′ f = has-lift.universal′ πᶜ _ (sub-proj f) (f ∘′ πᶜ′)

  infixl 5 _⨾ˢ′_

  sub-proj′
    : ∀ {Γ Δ x y} {σ : Hom Γ Δ} → (f : Hom[ σ ] x y)
    → πᶜ′ ∘′ (σ ⨾ˢ′ f) ≡[ sub-proj f ] f ∘′ πᶜ′
  sub-proj′ f = has-lift.commutesp πᶜ _ (sub-proj _) (f ∘′ πᶜ′)
```

If we extend the identity substitution with the identity morphism, we
obtain the identity morphism.

```agda
  sub-id : ∀ {Γ x} → id {Γ} ⨾ˢ id′ {Γ} {x} ≡ id
  sub-id = ap to F-id′

  sub-id′ : ∀ {Γ x} → (id ⨾ˢ′ id′) ≡[ sub-id {Γ} {x} ] id′
  sub-id′ = symP $ has-lift.uniquep πᶜ _ _ (symP sub-id) (sub-proj id′) id′ $
    idr′ _ ∙[] symP (idl′ _)
```

Furthermore, extending a substitution with a pair of composites is the
same as composing the two extensions.

```agda
  sub-comp
    : ∀ {Γ Δ Ψ x y z}
    → {σ : Hom Δ Ψ} {δ : Hom Γ Δ} {f : Hom[ σ ] y z} {g : Hom[ δ ] x y}
    → (σ ∘ δ) ⨾ˢ (f ∘′ g) ≡ (σ ⨾ˢ f) ∘ (δ ⨾ˢ g)
  sub-comp {σ = σ} {δ = δ} {f = f} {g = g} = ap to F-∘′

  sub-comp′
    : ∀ {Γ Δ Ψ x y z}
    → {σ : Hom Δ Ψ} {δ : Hom Γ Δ} {f : Hom[ σ ] y z} {g : Hom[ δ ] x y}
    → ((σ ∘ δ) ⨾ˢ′ (f ∘′ g)) ≡[ sub-comp ] (σ ⨾ˢ′ f) ∘′ (δ ⨾ˢ′ g)
  sub-comp′ = symP $ has-lift.uniquep πᶜ _ _ (symP sub-comp) (sub-proj _) _ $
    pulll[] _ (sub-proj′ _)
    ∙[] extendr[] _ (sub-proj′ _)
```

Note that we can extend the operation of context extension to a functor
from the [total category] of $\cE$ to $\cB$, that takes every pair
$(\Gamma, A)$ to $\Gamma.A$

[total category]: Cat.Displayed.Total.html

```agda
  Extend : Functor (∫ E) B
  Extend .F₀ (Γ , x) = Γ ⨾ x
  Extend .F₁ (total-hom σ f) = σ ⨾ˢ f
  Extend .F-id = ap to F-id′
  Extend .F-∘ f g = ap to F-∘′
```

There is also a natural transformation from this functor into the
projection out of the total category of $\cE$, where each component
of is a projection $\Gamma.A \to \Gamma$.

```agda
  proj : Extend => πᶠ E
  proj .η (Γ , x) = πᶜ
  proj .is-natural (Γ , x) (Δ , y) (total-hom σ f) =
    sub-proj f
```
