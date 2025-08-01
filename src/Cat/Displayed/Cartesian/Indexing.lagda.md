<!--
```agda
open import Cat.Bi.Instances.Discrete
open import Cat.Displayed.Cartesian
open import Cat.Instances.Discrete
open import Cat.Instances.Functor
open import Cat.Displayed.Fibre
open import Cat.Displayed.Base
open import Cat.Bi.Base
open import Cat.Prelude

import Cat.Displayed.Fibre.Reasoning
import Cat.Displayed.Reasoning
import Cat.Reasoning
import Cat.Morphism as Mor

open Pseudofunctor
open Lax-functor
open _=>_
```
-->

```agda
module Cat.Displayed.Cartesian.Indexing
  {o ℓ o' ℓ'} {B : Precategory o ℓ}
  (E : Displayed B o' ℓ')
  (cartesian : Cartesian-fibration E)
  where
```

<!--
```agda
open Cartesian-fibration E cartesian
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

# Reindexing for cartesian fibrations {defines="base-change"}

A [[cartesian fibration]] can be thought of as a [[displayed category]]
$\cE$ whose [[fibre categories]] $\cE^*(b)$ depend
([[pseudo|pseudofunctor]])functorially
on the object $b : \cB$ from the base category. A canonical example is
the [[canonical self-indexing]]: If $\cC$ is a
category with [[pullbacks]], then each $b \xto{f} a : \cC$ gives rise to
[[a functor|pullback functor]] $\cC/a \to \cC/b$, the _change of base_
along $f$.

```agda
module _ {𝒶 𝒷} (f : Hom 𝒶 𝒷) where
  base-change : Functor (Fibre E 𝒷) (Fibre E 𝒶)
  base-change .F₀ ob = f ^* ob
  base-change .F₁ {x} {y} vert = rebase f vert
```

<!--
```agda
  base-change .F-id {x} =
    sym $ π*.uniquep _ _ _ _ $
      idr' _ ∙[] symP (idl' _)

  base-change .F-∘ {x} {y} {z} f' g' =
    sym $ π*.uniquep _ _ _ _ $
      Fib.pulllf (π*.commutesp id-comm _)
      ∙[] pullr[] _ (π*.commutesp id-comm _)
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
    mi .eta x = π* id x
    mi .inv x = π*.universalv id'
    mi .eta∘inv x = cancel _ _ (π*.commutesv _)
    mi .inv∘eta x = sym $ π*.uniquep₂ _ _ _ _ _
      (idr' _)
      (Fib.cancellf (π*.commutesv _))
    mi .natural x y f =
      sym $ from-pathp $ cast[] $
        π*.commutesp id-comm _
        ∙[] Fib.to-fibre
```
</details>

And similarly, composing changes of base is the same thing as changing
base along a composite.

<!--
```agda
  ^*-id-to : ∀ {x} → Hom[ id {𝒶} ] (id ^* x) x
  ^*-id-to = π* _ _

  ^*-id-from : ∀ {x} → Hom[ id {𝒶} ] x (id ^* x)
  ^*-id-from = π*.universalv id'

^*-comp-from
  : ∀ {a b c} {z} {f : Hom b c} {g : Hom a b}
  → Hom[ id ] (g ^* (f ^* z)) ((f ∘ g) ^* z)
^*-comp-from {z = z} {f = f} {g = g} =
  π*.universalv (π* f z ∘' π* g (f ^* z))

^*-comp-to
  : ∀ {a b c} {z} {f : Hom b c} {g : Hom a b}
  → Hom[ id ] ((f ∘ g) ^* z) (g ^* (f ^* z))
^*-comp-to {z = z} {f = f} {g = g} = π*.universalv (π*.universal g (π* (f ∘ g) z))

^*-comp
  : ∀ {a b c} {z} {f : Hom b c} {g : Hom a b}
  → ((f ∘ g) ^* z) Fib.≅ (g ^* (f ^* z))
^*-comp = Fib.make-iso ^*-comp-to ^*-comp-from
  (π*.uniquep₂ _ _ _ _ _
    (Fib.pulllf (π*.commutesv _) ∙[]
      π*.uniquep₂ _ (idr _) refl _ _
        (pulll[] _ (π*.commutes _ _) ∙[]
          π*.commutesv _) refl)
    (idr' _))
  (π*.uniquep₂ _ _ _ _ _
    (Fib.pulllf (π*.commutesv _)
      ∙[] pullr[] _ (π*.commutesv _)
      ∙[] π*.commutes _ _)
    (idr' _))

^*-comp-to-natural
  : ∀ {a b c} {f : Hom b c} {g : Hom a b} {x y : Ob[ c ]} (f' : Hom[ id ] x y)
  → rebase g (rebase f f') Fib.∘ ^*-comp-to ≡ ^*-comp-to Fib.∘ rebase (f ∘ g) f'
^*-comp-to-natural {f = f} {g = g} f' =
  ap hom[] $ cartesian→weak-monic E (π*.cartesian) _ _ _ $ cast[] $
    pulll[] _ (π*.commutesp id-comm _)
    ∙[] pullr[] _ (π*.commutesv _)
    ∙[] π*.uniquep₂ _ id-comm-sym _ _ _
      (pulll[] _ (π*.commutesp id-comm _)
        ∙[] pullr[] _ (π*.commutes _ _))
      (pulll[] _ (π*.commutes _ _)
        ∙[] π*.commutesp id-comm _)
    ∙[] pushl[] _ (symP (π*.commutesv _))
```
-->

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
    mi .eta x = ^*-comp-to
    mi .inv x = ^*-comp-from
    mi .eta∘inv x = ^*-comp .Fib.invl
    mi .inv∘eta x = ^*-comp .Fib.invr
    mi .natural x y f' = ^*-comp-to-natural f'
```
</details>

In order to assemble this into a [[pseudofunctor]] out of $\cB\op$
(seen as a [[locally discrete bicategory]]) into $\Cat$, we start by
bundling up all the base changes into a functor between $\hom$ categories.
We also prove a lemma that will be useful later, relating base changes
along equal morphisms.

```agda
base-changes : ∀ {a b}
  → Functor (Locally-discrete (B ^op) .Prebicategory.Hom a b)
            Cat[ Fibre E a , Fibre E b ]
base-changes = Disc'-adjunct base-change

base-change-coherence
  : ∀ {a b} {b' : Ob[ b ]} {f g : Hom a b} (p : f ≡ g)
  → π* g b' ∘' base-changes .F₁ p .η b'
  ≡[ idr _ ∙ sym p ] π* f b'
base-change-coherence {b' = b'} {f} = J
  (λ g p → π* g b' ∘' base-changes .F₁ p .η b'
         ≡[ idr _ ∙ sym p ] π* f b')
  (elimr' refl Regularity.reduce!)
```

We have enough data to start defining our pseudofunctor:

<!--
```agda
private
  module FC {a} {b} = Cat.Reasoning (Cat[ Fibre E a , Fibre E b ])
```
-->

```agda
Fibres : Pseudofunctor (Locally-discrete (B ^op)) (Cat o' ℓ')
Fibres .lax .P₀ = Fibre E
Fibres .lax .P₁ = base-changes
Fibres .lax .compositor = Disc-natural₂
  λ (f , g) → base-change-comp g f .Mor.from
Fibres .lax .unitor = base-change-id .Mor.from
Fibres .unitor-inv = FC.iso→invertible (base-change-id FC.Iso⁻¹)
Fibres .compositor-inv f g =
  FC.iso→invertible (base-change-comp g f FC.Iso⁻¹)
```

It remains to verify that this data is *coherent*, which is so tedious
that it serves as a decent self-contained motivation for displayed
categories.

<details>
<summary>You've been warned.</summary>

We start with the `left-unit`{.Agda}. In the diagram below, we have
to show that the composite vertical morphism over $b$ is equal to
the identity over $b$. By the uniqueness property of cartesian lifts,
it suffices to show that the composites with the lift of $f$ are equal,
which is witnessed by the commutativity of the whole diagram.

~~~{.quiver}
\[\begin{tikzcd}
  {f^*a'} \\
  {\id^*f^*a'} & {f^*a'} \\
  {(f \circ \id)^*a'} \\
  {f^*a'} && {a'} \\
  b && a
  \arrow["f", from=5-1, to=5-3]
  \arrow["{\rm{lift}(f)}"', from=4-1, to=4-3]
  \arrow[maps to, from=4-3, to=5-3]
  \arrow[maps to, from=4-1, to=5-1]
  \arrow["{\lambda^*a'}"', color={rgb,255:red,214;green,92;blue,92}, from=3-1, to=4-1]
  \arrow["{\rm{lift}(f \circ \id)}"{pos=0.4}, from=3-1, to=4-3]
  \arrow["\gamma"', color={rgb,255:red,214;green,92;blue,92}, from=2-1, to=3-1]
  \arrow["\upsilon"', color={rgb,255:red,214;green,92;blue,92}, from=1-1, to=2-1]
  \arrow["{\rm{lift}(f)}", from=2-2, to=4-3]
  \arrow["{\rm{lift}(\id)}"', from=2-1, to=2-2]
  \arrow["\id", from=1-1, to=2-2]
\end{tikzcd}\]
~~~

The bottom triangle is our `base-change-coherence`{.Agda} lemma, the
middle square is by definition of the compositor and the top triangle
is by definition of the unitor.

```agda
Fibres .lax .left-unit f = ext λ a' →
  π*.uniquep₂ _ refl refl _ _
    (Fib.pulllf (base-change-coherence (idr f))
    ∙[] Fib.pulllf (π*.commutesv _)
    ∙[] (refl⟩∘'⟨ Fib.eliml (base-change id .F-id))
    ∙[] pullr[] _ (π*.commutesv id'))
    refl
```

For the `right-unit`{.Agda}, we proceed similarly. The diagram below
shows that the composite on the left, composed with the lift of $f$,
is equal to the lift of $f$.

~~~{.quiver}
\[\begin{tikzcd}
  {f^*a'} && {a'} \\
  {f^*\id^*a'} && {\id^*a'} \\
  {(\id \circ f)^*a'} \\
  {f^*a'} && {a'} \\
  b && a
  \arrow["f", from=5-1, to=5-3]
  \arrow["{\rm{lift}(f)}"', from=4-1, to=4-3]
  \arrow[maps to, from=4-3, to=5-3]
  \arrow[maps to, from=4-1, to=5-1]
  \arrow["{\rho^*a'}"', color={rgb,255:red,214;green,92;blue,92}, from=3-1, to=4-1]
  \arrow["{\rm{lift}(\id \circ f)}"{pos=0.2}, from=3-1, to=4-3]
  \arrow["\gamma"', color={rgb,255:red,214;green,92;blue,92}, from=2-1, to=3-1]
  \arrow["{f^*\upsilon}"', color={rgb,255:red,214;green,92;blue,92}, from=1-1, to=2-1]
  \arrow["{\rm{lift}(\id)}"{description}, from=2-3, to=4-3]
  \arrow["{\rm{lift}(f)}"', from=2-1, to=2-3]
  \arrow["{\rm{lift}(f)}", from=1-1, to=1-3]
  \arrow["\upsilon"', from=1-3, to=2-3]
  \arrow["\id", curve={height=-30pt}, from=1-3, to=4-3]
\end{tikzcd}\]
~~~

The bottom triangle is `base-change-coherence`{.Agda}, the middle square
is by definition of the compositor, the outer triangle is by definition
of the unitor, and the top square is by definition of `rebase`{.Agda}
(the action of $f^*$ on morphisms).

```agda
Fibres .lax .right-unit f = ext λ a' →
  π*.uniquep₂ _ refl _ _ _
    (Fib.pulllf (base-change-coherence (idl f))
    ∙[] Fib.pulllf (π*.commutesv _)
    ∙[] (refl⟩∘'⟨ Fib.idr _)
    ∙[] extendr[] id-comm (π*.commutesp _ _)
    ∙[] (π*.commutesv id' ⟩∘'⟨refl))
    (idr' _ ∙[] symP (idl' _))
```

Last but definitely not least, the `hexagon`{.Agda} witnessing the
coherence of associativity follows again by uniqueness of cartesian
lifts, by the commutativity of the following diagram.

~~~{.quiver}
\[\begin{tikzcd}
  {f^*g^*h^*a'} &&&&&& {f^*g^*h^*a'} \\
  {f^*g^*h^*a'} & {g^*h^*a'} &&&& {g^*h^*a'} & {(gf)^*h^*a'} \\
  {f^*(hg)^*a'} & {(hg)^*a'} & {h^*a'} && {h^*a'} && {(h(gf))^*a'} \\
  {((hg)f)^*a'} &&& {a'} &&& {((hg)f)^*a'} \\
  d & c & b & a & b & c & d
  \arrow["f", from=5-1, to=5-2]
  \arrow["g", from=5-2, to=5-3]
  \arrow["h", from=5-3, to=5-4]
  \arrow[maps to, from=4-4, to=5-4]
  \arrow[maps to, from=4-1, to=5-1]
  \arrow["{\rm{lift}((hg)f)}"', from=4-1, to=4-4]
  \arrow[""{name=0, anchor=center, inner sep=0}, from=3-3, to=4-4]
  \arrow["{\rm{lift}(g)}", from=2-2, to=3-3]
  \arrow["{\rm{lift}(f)}", from=1-1, to=2-2]
  \arrow["\gamma", color={rgb,255:red,214;green,92;blue,92}, from=2-7, to=3-7]
  \arrow["\id"', color={rgb,255:red,92;green,92;blue,214}, from=1-1, to=2-1]
  \arrow["{f^*\gamma}"', color={rgb,255:red,92;green,92;blue,214}, from=2-1, to=3-1]
  \arrow["\gamma"', color={rgb,255:red,92;green,92;blue,214}, from=3-1, to=4-1]
  \arrow["{\rm{lift}(hg)}"'{pos=0.1}, from=3-2, to=4-4]
  \arrow["{\rm{lift}(f)}"', from=3-1, to=3-2]
  \arrow["{\rm{lift}(f)}"', from=2-1, to=2-2]
  \arrow["\gamma"', from=2-2, to=3-2]
  \arrow["{\alpha^*a'}", color={rgb,255:red,214;green,92;blue,92}, from=3-7, to=4-7]
  \arrow["\gamma", color={rgb,255:red,214;green,92;blue,92}, from=1-7, to=2-7]
  \arrow["h"', from=5-5, to=5-4]
  \arrow["g"', from=5-6, to=5-5]
  \arrow["f"', from=5-7, to=5-6]
  \arrow[maps to, from=4-7, to=5-7]
  \arrow["{\rm{lift}((hg)f)}", from=4-7, to=4-4]
  \arrow[""{name=1, anchor=center, inner sep=0}, from=3-5, to=4-4]
  \arrow["{\rm{lift}(g)}"', from=2-6, to=3-5]
  \arrow["{\rm{lift}(f)}"', from=1-7, to=2-6]
  \arrow["{\rm{lift}(h(gf))}"{pos=0.2}, from=3-7, to=4-4]
  \arrow["{\rm{lift}(gf)}"{pos=0.3}, from=2-7, to=3-5]
  \arrow[Rightarrow, no head, from=1-1, to=1-7]
  \arrow[Rightarrow, no head, from=2-2, to=2-6]
  \arrow[Rightarrow, no head, from=3-3, to=3-5]
  \arrow["{\rm{lift}(h)}"{description}, shift left=2, draw=none, from=0, to=1]
\end{tikzcd}\]
~~~

```agda
Fibres .lax .hexagon f g h = ext λ a' →
  π*.uniquep₂ _ refl _ _ _
    (Fib.pulllf (base-change-coherence (assoc h g f))
    ∙[] Fib.pulllf (π*.commutesv _)
    ∙[] (refl⟩∘'⟨ Fib.eliml (base-change (g ∘ f) .F-id))
    ∙[] extendr[] _ (π*.commutesv _))
    (Fib.pulllf (π*.commutesv _)
    ∙[] (refl⟩∘'⟨ Fib.idr _) ∙[] (refl⟩∘'⟨ Fib.idr _)
    ∙[] extendr[] id-comm (π*.commutesp _ _)
    ∙[] (π*.commutesv _ ⟩∘'⟨refl))
```
</details>

<!--
```agda
-- Optimized natural iso, avoids a bunch of junk from composition.
opaque
  base-change-square
    : ∀ {Γ Δ Θ Ψ : Ob}
    → {σ : Hom Γ Δ} {δ : Hom Γ Θ} {γ : Hom Δ Ψ} {τ : Hom Θ Ψ}
    → γ ∘ σ ≡ τ ∘ δ
    → ∀ x' → Hom[ id ]
      (base-change σ .F₀ (base-change γ .F₀ x'))
      (base-change δ .F₀ (base-change τ .F₀ x'))
  base-change-square {σ = σ} {δ = δ} {γ = γ} {τ = τ} p x' =
    π*.universalv $
    π*.universal' (sym p) $
    π* γ x' ∘' π* σ _

  base-change-square-lifting
    : ∀ {Γ Δ Θ Ψ : Ob}
    → {σ : Hom Γ Δ} {δ : Hom Γ Θ} {γ : Hom Δ Ψ} {τ : Hom Θ Ψ}
    → (p : γ ∘ σ ≡ τ ∘ δ) (x' : Ob[ Ψ ])
    → π* τ x' ∘' π* δ (base-change τ .F₀ x') ∘' base-change-square p x'
    ≡[ ap (τ ∘_) (idr _) ∙ sym p ] π* γ x' ∘' π* σ _
  base-change-square-lifting {σ = σ} {δ = δ} {γ = γ} {τ = τ} p x' =
    cast[] $
    apd (λ _ → π* τ x' ∘'_) (π*.commutesv _)
    ∙[] π*.commutesp (sym p) _

  base-change-square-natural
    : ∀ {Γ Δ Θ Ψ : Ob}
    → {σ : Hom Γ Δ} {δ : Hom Γ Θ} {γ : Hom Δ Ψ} {τ : Hom Θ Ψ}
    → (p : γ ∘ σ ≡ τ ∘ δ)
    → ∀ {x' y'} (f' : Hom[ id ] x' y')
    → base-change-square p y' ∘' base-change σ .F₁ (base-change γ .F₁ f')
    ≡ base-change δ .F₁ (base-change τ .F₁ f') ∘' base-change-square p x'
  base-change-square-natural {σ = σ} {δ = δ} {γ = γ} {τ = τ} p f' =
    π*.uniquep₂ _ _ _ _ _
      (pulll[] _ (π*.commutesv _)
       ∙[] π*.uniquep₂ _ (idr _) _ _ _
         (pulll[] _ (π*.commutesp (sym p) _)
          ∙[] pullr[] _ (π*.commutesp id-comm _)
          ∙[] extendl[] _ (π*.commutesp id-comm _))
         (π*.commutesp (sym p ∙ sym (idl _ )) _))
      (pulll[] _ (π*.commutesp id-comm _)
       ∙[] pullr[] _ (π*.commutesv _)
       ∙[] π*.uniquep _ (idl _) (sym p ∙ sym (idl _)) _
         (pulll[] _ (π*.commutesp id-comm _ )
          ∙[] pullr[] _ (π*.commutesp (sym p) _)))

  base-change-square-inv
    : ∀ {Γ Δ Θ Ψ : Ob}
    → {σ : Hom Γ Δ} {δ : Hom Γ Θ} {γ : Hom Δ Ψ} {τ : Hom Θ Ψ}
    → (p : γ ∘ σ ≡ τ ∘ δ)
    → ∀ x' → base-change-square p x' ∘' base-change-square (sym p) x' ≡[ idl _ ] id'
  base-change-square-inv {σ = σ} {δ = δ} {γ = γ} {τ = τ} p x' =
    π*.uniquep₂ _ _ _ _ _
      (pulll[] _ (π*.commutesv _)
       ∙[] π*.uniquep₂ _ (idr _) refl _ _
         (pulll[] _ (π*.commutesp (sym p) _)
          ∙[] pullr[] _ (π*.commutesv _)
          ∙[] π*.commutesp p _)
         refl)
      (idr' _)

base-change-square-ni
  : ∀ {Γ Δ Θ Ψ : Ob}
  → {σ : Hom Γ Δ} {δ : Hom Γ Θ} {γ : Hom Δ Ψ} {τ : Hom Θ Ψ}
  → γ ∘ σ ≡ τ ∘ δ
  → (base-change σ F∘ base-change γ) ≅ⁿ (base-change δ F∘ base-change τ)
base-change-square-ni {σ = σ} {δ = δ} {γ = γ} {τ = τ} p =
  to-natural-iso ni where

  open make-natural-iso
  ni : make-natural-iso _ _
  ni .eta = base-change-square p
  ni .inv = base-change-square (sym p)
  ni .eta∘inv x = from-pathp $ base-change-square-inv p x
  ni .inv∘eta x = from-pathp $ base-change-square-inv (sym p) x
  ni .natural x y f = sym $ Fib.over-fibre (base-change-square-natural p f)
```
-->
