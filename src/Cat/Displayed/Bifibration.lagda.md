<!--
```agda
open import Cat.Functor.Adjoint.Hom
open import Cat.Instances.Functor
open import Cat.Displayed.Fibre
open import Cat.Functor.Adjoint
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Cocartesian.Indexing
import Cat.Displayed.Cartesian.Indexing
import Cat.Displayed.Cocartesian.Weak
import Cat.Displayed.Fibre.Reasoning
import Cat.Displayed.Cartesian.Weak
import Cat.Displayed.Cocartesian
import Cat.Displayed.Cartesian
import Cat.Displayed.Reasoning
import Cat.Reasoning
```
-->

```agda
module Cat.Displayed.Bifibration
  {o ℓ o' ℓ'} {ℬ : Precategory o ℓ} (ℰ : Displayed ℬ o' ℓ') where
```

<!--
```agda
open Cat.Displayed.Cocartesian ℰ
open Cat.Displayed.Cocartesian.Weak ℰ
open Cat.Displayed.Cartesian ℰ
open Cat.Displayed.Cartesian.Weak ℰ
open Cat.Displayed.Reasoning ℰ

open Cat.Reasoning ℬ
open Displayed ℰ
open Functor
open _⊣_
open _=>_
private
  module Fib = Cat.Displayed.Fibre.Reasoning ℰ
```
-->


# Bifibrations {defines="bifibration"}

A [[displayed category]] $\cE \liesover \cB$ is a **bifibration** if is
it both a [[fibration|cartesian fibration]] and an opfibration. This
means that $\cE$ is equipped with both [reindexing] and [opreindexing]
functors, which allows us to both restrict and extend along morphisms $X
\to Y$ in the base.

Note that a bifibration is *not* the same as a "profunctor valued in
categories". Those are a distinct concept, called **two-sided
fibrations**.

[reindexing]: Cat.Displayed.Cartesian.Indexing.html
[opreindexing]: Cat.Displayed.Cocartesian.Indexing.html

<!--
[TODO: Reed M, 31/01/2023] Link to two-sided fibration
when that page is written.
-->

```agda
record is-bifibration : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ') where
  field
    fibration : Cartesian-fibration
    opfibration : Cocartesian-fibration

  module fibration = Cartesian-fibration fibration
  module opfibration = Cocartesian-fibration opfibration
```

# Bifibrations and adjoints

If $\cE$ is a bifibration, then its opreindexing functors are [[left
adjoints]] to its reindexing functors.  To show this, it will suffice to
construct natural isomorphism between $\cE_{y}(u_{*}(-),-)$ and
$\cE_{x}(-,u^{*}(-))$. However, we have already shown that
$\cE_{y}(u_{*}(-),-)$ and $\cE_{x}(-,u^{*}(-))$ are both naturally
isomorphic to $\cE_{u}(-,-)$[^proof], so all we need to do is compose these
natural isomorphisms!

[^proof]: see `opfibration→hom-iso`{.Agda} and `fibration→hom-iso`{.Agda}.

```agda
module _ (bifib : is-bifibration) where
  open is-bifibration bifib
  open Cat.Displayed.Cartesian.Indexing ℰ fibration
  open Cat.Displayed.Cocartesian.Indexing ℰ opfibration

  cobase-change⊣base-change
    : ∀ {x y} (f : Hom x y)
    → cobase-change f ⊣ base-change f
  cobase-change⊣base-change {x} {y} f =
    hom-natural-iso→adjoints $
      (opfibration→hom-iso opfibration f ni⁻¹) ∘ni fibration→hom-iso fibration f
```

In fact, if $\cE \liesover \cB$ is a cartesian fibration where every
reindexing functor has a left adjoint, then $\cE$ is a bifibration!

Since $\cE$ is a fibration, every $u : x \to y$ in $\cB$ induces a
natural isomorphism $\cE_{u}(x',-) \simeq \cE_{x}(x', u^{*}(-))$, by the
universal property of [[cartesian lifts]]. If $u^{*}$ additionally has a
left adjoint $L_{u}$, we have natural isomorphisms

$$
\cE_{u}(x',-) \simeq \cE_{x}(x',u^{*}(-)) \simeq \cE_{y}(L_{u}(x')-)\text{,}
$$

which implies $\cE$ `is a weak opfibration`{.Agda
id=`hom-iso→weak-opfibration}; and any weak opfibration that's also a
fibration is a proper opfibration.

```agda
module _ (fib : Cartesian-fibration) where
  open Cartesian-fibration fib
  open Cat.Displayed.Cartesian.Indexing ℰ fib

  left-adjoint-base-change→opfibration
    : (L : ∀ {x y} → (f : Hom x y) → Functor (Fibre ℰ x) (Fibre ℰ y))
    → (∀ {x y} → (f : Hom x y) → (L f ⊣ base-change f))
    → Cocartesian-fibration
  left-adjoint-base-change→opfibration L adj =
    cartesian+weak-opfibration→opfibration fib $
    hom-iso→weak-opfibration L λ u →
      fibration→hom-iso-from fib u ∘ni (adjunct-hom-iso-from (adj u) _ ni⁻¹)
```

<!--
```agda
  left-adjoint-base-change→bifibration
    : (L : ∀ {x y} → (f : Hom x y) → Functor (Fibre ℰ x) (Fibre ℰ y))
    → (∀ {x y} → (f : Hom x y) → (L f ⊣ base-change f))
    → is-bifibration
  left-adjoint-base-change→bifibration L adj .is-bifibration.fibration =
    fib
  left-adjoint-base-change→bifibration L adj .is-bifibration.opfibration =
    left-adjoint-base-change→opfibration L adj
```
-->

## Adjoints from cocartesian maps

Let $f : X \to Y$ be a morphism in $\cB$, and let $L : \cE_{X} \to
\cE_{Y}$ be a functor. If we are given a natural transformation $\eta :
\Id \to f^{*} \circ L$ with $\overline{f} \circ \eta$ cocartesian,
then $L$ is a left adjoint to $f^{*}$.

```agda
  cocartesian→left-adjoint-base-change
    : ∀ {x y} {L : Functor (Fibre ℰ x) (Fibre ℰ y)} {f : Hom x y}
    → (L-unit : Id => base-change f F∘ L)
    → (∀ x → is-cocartesian (f ∘ id) (has-lift.lifting f (L .F₀ x) ∘' L-unit .η x))
    → L ⊣ base-change f
```

We will construct the adjunction by constructing a natural equivalence
of $\hom$-sets

$$\cE_{X}{L A, B} \simeq \cE_{Y}{A, f^{*}B}\text{.}$$

The map $v \mapsto f^{*}(v) \circ \eta$ gives us the forward direction
of this equivalence, so all that remains is to find an inverse. Since
$\overline{f}\circ\eta$ is cocartesian, it satisfies a _mapping-out_
universal property: if $v : A \to f^{*} B$ is a vertical map in $\cE$,
we can construct a vertical map $LA \to B$ by factoring $\overline{f}
\circ v$ through the cocartesian $\overline{f} \circ \eta$; The actual
_universal property_ says that this factorising process is an
equivalence.

~~~{.quiver}
\begin{tikzcd}
  &&& B \\
  A && LA \\
  &&& Y \\
  X && Y
  \arrow["{\overline{f} \circ \eta}", from=2-1, to=2-3]
  \arrow["f"', from=4-1, to=4-3]
  \arrow[lies over, from=2-1, to=4-1]
  \arrow[lies over, from=2-3, to=4-3]
  \arrow[dashed, from=2-3, to=1-4]
  \arrow["id"', from=4-3, to=3-4]
  \arrow[lies over, from=1-4, to=3-4]
  \arrow["{\overline{f} \circ v}", curve={height=-12pt}, from=2-1, to=1-4]
  \arrow["f", curve={height=-12pt}, from=4-1, to=3-4]
\end{tikzcd}
~~~

```agda
  cocartesian→left-adjoint-base-change {x = x} {y = y} {L = L} {f = f} L-unit cocart =
    hom-iso→adjoints (λ v → base-change f .F₁ v Fib.∘ L-unit .η _)
      precompose-equiv equiv-natural where
      module cocart x = is-cocartesian (cocart x)
      module f* = Functor (base-change f)

      precompose-equiv
        : ∀ {x' : Ob[ x ]} {y' : Ob[ y ]}
        → is-equiv {A = Hom[ id ] (F₀ L x') y'} (λ v → f*.₁ v Fib.∘ L-unit .η x')
      precompose-equiv {x'} {y'} = is-iso→is-equiv $ iso
        (λ v → cocart.universalv _ (has-lift.lifting f _ ∘' v))
        (λ v → has-lift.uniquep₂ _ _ _ _ refl _ _
          (Fib.pulllf (has-lift.commutesp f _ id-comm _)
          ∙[] symP (assoc' _ _ _)
          ∙[] cocart.commutesv x' _)
          refl)
        (λ v → symP $ cocart.uniquep x' _ _ _ _ $
          assoc' _ _ _
          ∙[] Fib.pushlf (symP $ has-lift.commutesp f _ id-comm _))
```

<details>
<summary>Futhermore, this equivalence is natural, but that's a very tedious proof.
</summary>

```agda
      equiv-natural
        : hom-iso-natural {L = L} {R = base-change f} (λ v → f*.₁ v Fib.∘ L-unit .η _)
      equiv-natural g h k =
        has-lift.uniquep₂ _ _ _ _ _ _ _
          (Fib.pulllf (has-lift.commutesp f _ id-comm _)
           ∙[] pushl[] _ (pushl[] _ (to-pathp⁻ (smashr _ _))))
          (Fib.pulllf (has-lift.commutesp f _ id-comm _)
           ∙[] extendr[] _ (Fib.pulllf (Fib.pulllf (has-lift.commutesp f _ id-comm _)))
           ∙[] extendr[] _ (pullr[] _ (to-pathp (L-unit .is-natural _ _ h)))
           ∙[] pullr[] _ (Fib.pulllf (extendr[] _ (has-lift.commutesp f _ id-comm _))))
```
</details>
