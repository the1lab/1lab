---
description: |
  We characterise the *reflective subcategory* inclusions: the fully
  faithful functors which have a left adjoint, equivalently which induce
  an idempotent monad. We show that every reflective subcategory
  inclusion is a monadic functor.
---

<!--
```agda
open import Cat.Functor.Adjoint.Properties
open import Cat.Functor.Adjoint.Monadic
open import Cat.Functor.Equivalence
open import Cat.Functor.Properties
open import Cat.Instances.Functor
open import Cat.Displayed.Total
open import Cat.Functor.Adjoint
open import Cat.Diagram.Monad
open import Cat.Prelude

import Cat.Functor.Reasoning as Func
import Cat.Reasoning
```
-->

```agda
module Cat.Functor.Adjoint.Reflective where
```

<!--
```agda
private variable
  o o' ℓ ℓ' : Level
  C D : Precategory o ℓ
  L ι : Functor C D
open Functor
open _=>_
open ∫Hom
```
-->

# Reflective subcategories

Occasionally, [full subcategory] inclusions (hence [[fully faithful
functors]], like the inclusion of [[abelian groups]] into the
category of all [[groups]] or the inclusion $\Props \mono \Sets$)
participate in an adjunction

[full subcategory]: Cat.Functor.FullSubcategory.html

~~~{.quiver}
\[\begin{tikzcd}
  \mathcal{C} & \mathcal{D.}
  \arrow[""{name=0, anchor=center, inner sep=0}, "\iota"', shift right=2, hook, from=1-1, to=1-2]
  \arrow[""{name=1, anchor=center, inner sep=0}, "L"', shift right=2, from=1-2, to=1-1]
  \arrow["\dashv"{anchor=center, rotate=-90}, draw=none, from=1, to=0]
\end{tikzcd}\]
~~~

:::{.definition #reflective-subcategory}
When this is the case, we refer to the [[left adjoint]] functor $L$ as
the **reflector**, and $\iota$ exhibits $\cC$ as a **reflective
subcategory** of $\cD$. Reflective subcategory inclusions are of
particular importance because they are [[monadic functors]]: they
exhibit $\cC$ as the category of algebras for an
([[idempotent|idempotent monad]]) monad on $\cD$.
:::

```agda
is-reflective : L ⊣ ι → Type _
is-reflective {ι = ι} adj = is-fully-faithful ι
```

The first thing we will prove is that the counit map $\eps : L\iota o
\to o$ of a reflexive subcategory inclusion is invertible. Luckily, we
have developed enough general theory to make this almost immediate:

- $ι$ is full, so the counit must be a [[split monomorphism]].
- $ι$ is faithful, so the counit must be a [[epimorphism]].
- Every morphism that is simultaneously split monic and epic is
  invertible.

```agda
module
  _ {C : Precategory o ℓ} {D : Precategory o' ℓ'} {L : Functor C D} {ι : Functor D C}
    (adj : L ⊣ ι) (ι-ff : is-reflective adj)
  where
  private
    module DD = Cat.Reasoning Cat[ D , D ]
    module C = Cat.Reasoning C
    module D = Cat.Reasoning D
    module L = Func L
    module ι = Func ι
    module ιL = Func (ι F∘ L)
    module Lι = Func (L F∘ ι)
    module ι-ff {x} {y} = Equiv (_ , ι-ff {x} {y})
  open _⊣_ adj

  is-reflective→counit-is-invertible : ∀ {o} → D.is-invertible (ε o)
  is-reflective→counit-is-invertible {o} =
    D.split-monic+epic→invertible
      (right-full→counit-split-monic adj (ff→full {F = ι} ι-ff))
      (right-faithful→counit-epic adj (ff→faithful {F = ι} ι-ff))

```

<!--
```agda
  is-reflective→counit-is-iso : ∀ {o} → Lι.₀ o D.≅ o
  is-reflective→counit-is-iso {o} = morp where
    morp : L.₀ (ι.₀ o) D.≅ o
    morp =
      D.invertible→iso (ε _) $
      D.split-monic+epic→invertible
        (right-full→counit-split-monic adj (ff→full {F = ι} ι-ff))
        (right-faithful→counit-epic adj (ff→faithful {F = ι} ι-ff))

  is-reflective→counit-iso : (L F∘ ι) ≅ⁿ Id
  is-reflective→counit-iso = DD.invertible→iso counit invs where
    invs = invertible→invertibleⁿ counit λ x →
      is-reflective→counit-is-invertible

  η-comonad-commute : ∀ {x} → unit.η (ι.₀ (L.₀ x)) ≡ ι.₁ (L.₁ (unit.η x))
  η-comonad-commute {x} = C.right-inv-unique
    (F-map-iso ι is-reflective→counit-is-iso)
    zag
    (sym (ι.F-∘ _ _) ∙ ap ι.₁ zig ∙ ι.F-id)

  is-reflective→unit-right-is-iso : ∀ {o} → C.is-invertible (unit.η (ι.₀ o))
  is-reflective→unit-right-is-iso {o} = C.make-invertible (ι-ff.to (ε _))
    (unit.is-natural _ _ _ ∙∙ ap₂ C._∘_ refl η-comonad-commute ∙∙ ιL.annihilate zag)
    zag

  is-reflective→left-unit-is-iso : ∀ {o} → D.is-invertible (L.₁ (unit.η o))
  is-reflective→left-unit-is-iso {o} = D.make-invertible
    (ε _)
    (sym (counit.is-natural _ _ _) ∙ ap₂ D._∘_ refl (ap L.₁ (sym η-comonad-commute)) ∙ zig)
    zig
```
-->

We can now prove that the adjunction $L \dashv \iota$ is monadic.

```agda
is-reflective→is-monadic
  : ∀ {L : Functor C D} {ι : Functor D C}
  → (adj : L ⊣ ι) → is-reflective adj → is-monadic adj
is-reflective→is-monadic {C = C} {D = D} {L = L} {ι} adj ι-ff = eqv where
```

<!--
```agda
  module EM = Cat.Reasoning (Eilenberg-Moore (R∘L adj))
  module C = Cat.Reasoning C
  module D = Cat.Reasoning D
  module L = Functor L
  module ι = Functor ι
  open Algebra-on
  open _⊣_ adj

  Comp : Functor D (Eilenberg-Moore (R∘L adj))
  Comp = Comparison-EM adj
  module Comp = Functor Comp
```
-->

It suffices to show that the comparison functor $D \to C^{\iota L}$ is
fully faithful and [[split essentially surjective]]. For full
faithfulness, observe that it's always faithful; The fullness comes from
the assumption that $\iota$ is ff.

```agda
  comp-ff : is-fully-faithful Comp
  comp-ff {x} {y} = is-iso→is-equiv λ where
    .is-iso.from alg → equiv→inverse ι-ff (alg .fst)
    .is-iso.rinv x → ext (equiv→counit ι-ff _)
    .is-iso.linv x → equiv→unit ι-ff _
```

To show that the comparison functor is split essentially surjective,
suppose we have an object $o$ admitting the structure of an
$\iota L$-algebra; We will show that $o \cong \iota Lo$ as $\iota
L$-algebras. Note that $\iota L(o)$ admits a canonical (free) algebra
structure. The algebra map $\nu : \iota L(o) \to o$ provides an algebra
morphism from $\iota L(o) \to o$ and the morphism $o \to \iota L(o)$ can
be taken to be adjunction unit $\eta$.

The crucial lemma in establishing that these are inverses is that
$\eta_{\iota Lx} = \iota L(\eta_x)$, which follows because both of those
morphisms are right inverses to $\iota \eps_x$ which is an isomorphism
because $\eps$ is.

```agda
  comp-seso : is-split-eso Comp
  comp-seso (ob , alg) = L.₀ ob , isom where
    Lo→o : Algebra-hom (R∘L adj) (Comp.₀ (L.₀ ob)) (ob , alg)
    Lo→o .fst = alg .ν
    Lo→o .snd = alg .ν-mult

    o→Lo : Algebra-hom (R∘L adj) (ob , alg) (Comp.₀ (L.₀ ob))
    o→Lo .fst = unit.η _
    o→Lo .snd =
        unit.is-natural _ _ _
      ∙ ap₂ C._∘_ refl (η-comonad-commute adj ι-ff)
      ∙ sym (ι.F-∘ _ _)
      ∙ ap ι.₁ (sym (L.F-∘ _ _) ∙∙ ap L.₁ (alg .ν-unit) ∙∙ L.F-id)
      ∙ sym (ap₂ C._∘_ refl (sym (η-comonad-commute adj ι-ff)) ∙ zag ∙ sym ι.F-id)

    isom : Comp.₀ (L.₀ ob) EM.≅ (ob , alg)
    isom = EM.make-iso Lo→o o→Lo
      (ext (alg .ν-unit))
      (ext (
          unit.is-natural _ _ _
        ∙∙ ap₂ C._∘_ refl (η-comonad-commute adj ι-ff)
        ∙∙ sym (ι.F-∘ _ _)
        ∙∙ ap ι.₁ (sym (L.F-∘ _ _) ∙∙ ap L.₁ (alg .ν-unit) ∙∙ L.F-id)
        ∙∙ ι.F-id))

  eqv : is-equivalence Comp
  eqv = ff+split-eso→is-equivalence comp-ff comp-seso
```

## Constructing reflective subcategories

Earlier, we saw that any reflective subcategory has an invertible counit.
We will now prove the converse: if the counit of an adjunction is
invertible, then the left adjoint is a reflector.

<!--
```agda
module _
  {C : Precategory o ℓ} {D : Precategory o' ℓ'}
  {L : Functor C D} {R : Functor D C}
  (adj : L ⊣ R)
  where
  private
    module C = Cat.Reasoning C
    module D = Cat.Reasoning D
    module [D,D] = Cat.Reasoning Cat[ D , D ]
    module L = Func L
    module R = Func R
    module RL = Func (R F∘ L)
    module LR = Func (L F∘ R)
    open _⊣_ adj
```
-->

Again, the sea has risen to meet us:

- [[A right adjoint is faithful if and only if the counit is epic|faithful-adjoint]].
- [[A right adjoint full if and only if the counit is split monic|full-adjoint]].

If the counit is invertible, then it is clearly both split monic and epic,
and thus the corresponding right adjoint must be fully faithful.

```agda
  is-counit-iso→is-reflective : is-invertibleⁿ counit → is-reflective adj
  is-counit-iso→is-reflective counit-iso =
    full+faithful→ff R
      R-full
      R-faithful
    where
      R-full : is-full R
      R-full =
        counit-split-monic→right-full adj $
        D.invertible→to-split-monic $
        is-invertibleⁿ→is-invertible counit-iso _

      R-faithful : is-faithful R
      R-faithful =
        counit-epic→right-faithful adj $
        D.invertible→epic $
        is-invertibleⁿ→is-invertible counit-iso _
```

Furthermore, if we have *any* natural isomorphism $\alpha : LR \iso
\Id$, then the left adjoint is a reflector! To show this, we will
construct an inverse to the counit; our previous result will then ensure
that $F$ is fully faithful.

To begin, recall that isos have the 2-out-of-3 property. Thus it
suffices to show that $\eps \circ \alpha$ is invertible. Next, note that
we can transfer the comonad structure on $LR$ onto a comonad structure
on $\Id$ by repeatedly composing with $\alpha$; this yields a natural
transformation $\delta : \Id \to \Id$ that is a right inverse to $\eps
\circ \alpha$.

Finally, all natural transformations $\Id \to \Id$ commute with one
another, so $\delta$ is also a right inverse, and $\eps \circ \alpha$ is
invertible.

```agda
  LR-iso→is-reflective : (L F∘ R) ≅ⁿ Id → is-reflective adj
  LR-iso→is-reflective α =
    is-counit-iso→is-reflective $
    [D,D].invertible-cancell
      ([D,D].iso→invertible (α [D,D].Iso⁻¹))
      ([D,D].make-invertible δ right-ident right-ident⁻¹)
    where
      module α = Isoⁿ α

      δ : Id {C = D} => Id
      δ .η x = α.to .η x D.∘ α.to .η (L.₀ (R.₀ x)) D.∘ L.₁ (unit.η (R.₀ x)) D.∘ α.from .η x
      δ .is-natural x y f =
          D.extendr (D.extendr (D.extendr (α.from .is-natural _ _ _)))
        ∙ D.pushl (D.pushr (D.pushr (L.weave (unit .is-natural _ _ _))))
        ∙ D.pushl (D.pushr (α.to .is-natural _ _ _))
        ∙ D.pushl (α.to .is-natural _ _ _)

      right-ident : (counit ∘nt α.from) ∘nt δ ≡ idnt
      right-ident = ext λ x →
          D.cancel-inner (α.invr ηₚ _)
        ∙ D.pulll (sym $ α.to .is-natural _ _ _)
        ∙ D.cancel-inner (L.annihilate zag)
        ∙ α.invl ηₚ _

      right-ident⁻¹ : δ ∘nt (counit ∘nt α.from) ≡ idnt
      right-ident⁻¹ = id-nat-commute δ (counit ∘nt α.from) ∙ right-ident
```
