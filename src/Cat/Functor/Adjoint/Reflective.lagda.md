---
description: |
  We characterise the *reflective subcategory* inclusions: the fully
  faithful functors which have a left adjoint, equivalently which induce
  an idempotent monad. We show that every reflective subcategory
  inclusion is a monadic functor.
---

<!--
```agda
open import Cat.Functor.Adjoint.Monadic
open import Cat.Functor.Equivalence
open import Cat.Functor.Properties
open import Cat.Instances.Functor
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
  F G : Functor C D
open Functor
open _=>_
```
-->

# Reflective subcategories

Occasionally, [full subcategory] inclusions (hence [[fully faithful
functors]] --- like the inclusion of [[abelian groups]] into the category of
all [[groups]], or the inclusion $\Props \mono \Sets$) participate in an
adjunction

[full subcategory]: Cat.Functor.FullSubcategory.html

~~~{.quiver}
\[\begin{tikzcd}
  \mathcal{C} & \mathcal{D}
  \arrow[""{name=0, anchor=center, inner sep=0}, "\iota"', shift right=2, hook, from=1-1, to=1-2]
  \arrow[""{name=1, anchor=center, inner sep=0}, "L"', shift right=2, from=1-2, to=1-1]
  \arrow["\dashv"{anchor=center, rotate=-90}, draw=none, from=1, to=0]
\end{tikzcd}\]
~~~

:::{.definition #reflective-subcategory}
When this is the case, we refer to the [[left adjoint]] functor $L$ as the
**reflector**, and $\iota$ exhibits $\cC$ as a **reflective
subcategory** of $\cD$. Reflective subcategory inclusions are of
particular importance because they are [monadic functors]: They exhibit
$\cC$ as the category of algebras for an ([[idempotent|idempotent monad]])
monad on $\cD$.
:::

[monadic functors]: Cat.Functor.Adjoint.Monadic.html

```agda
is-reflective : F ⊣ G → Type _
is-reflective {G = G} adj = is-fully-faithful G
```

The first thing we will prove is that the counit map $\eps : FGo \to o$
of a reflexive subcategory inclusion is an isomorphism. Since $G$ is
fully faithful, the unit map $\eta_{Go} : Go \to GFGo$ corresponds to a
map $o \to FGo$, and this map can be seen to be a left- and right-
inverse to $\eps$ applying the triangle identities.

```agda
module
  _ {C : Precategory o ℓ} {D : Precategory o' ℓ'} {F : Functor C D} {G : Functor D C}
    (adj : F ⊣ G) (g-ff : is-reflective adj)
  where
  private
    module DD = Cat.Reasoning Cat[ D , D ]
    module C = Cat.Reasoning C
    module D = Cat.Reasoning D
    module F = Func F
    module G = Func G
    module GF = Func (G F∘ F)
    module FG = Func (F F∘ G)
    module g-ff {x} {y} = Equiv (_ , g-ff {x} {y})
  open _⊣_ adj

  is-reflective→counit-is-iso : ∀ {o} → FG.₀ o D.≅ o
  is-reflective→counit-is-iso {o} = morp where
    morp : F.₀ (G.₀ o) D.≅ o
    morp = D.make-iso (ε _) (g-ff.from (unit.η _)) invl invr
      where abstract
      invl : ε o D.∘ g-ff.from (unit.η (G.₀ o)) ≡ D.id
      invl = fully-faithful→faithful {F = G} g-ff (
        G.₁ (ε o D.∘ _)                 ≡⟨ G.F-∘ _ _ ⟩
        G.₁ (ε o) C.∘ G.₁ (g-ff.from _) ≡⟨ C.refl⟩∘⟨  g-ff.ε _ ⟩
        G.₁ (ε o) C.∘ unit.η (G.₀ o)    ≡⟨ zag ∙ sym G.F-id ⟩
        G.₁ D.id                        ∎)

      invr : g-ff.from (unit.η (G.₀ o)) D.∘ ε o ≡ D.id
      invr = fully-faithful→faithful {F = G} g-ff (ap G.₁ (
        g-ff.from _ D.∘ ε _             ≡˘⟨ counit.is-natural _ _ _ ⟩
        ε _ D.∘ F.₁ (G.₁ (g-ff.from _)) ≡⟨ D.refl⟩∘⟨ F.⟨ g-ff.ε _ ⟩ ⟩
        ε _ D.∘ F.₁ (unit.η _)          ≡⟨ zig ⟩
        D.id                            ∎))

  is-reflective→counit-iso : (F F∘ G) DD.≅ Id
  is-reflective→counit-iso = DD.invertible→iso counit invs where
    invs = invertible→invertibleⁿ counit λ x →
      D.iso→invertible (is-reflective→counit-is-iso {o = x})
```

<!--
```agda
  η-comonad-commute : ∀ {x} → unit.η (G.₀ (F.₀ x)) ≡ G.₁ (F.₁ (unit.η x))
  η-comonad-commute {x} = C.right-inv-unique
    (F-map-iso G is-reflective→counit-is-iso)
    zag
    (sym (G.F-∘ _ _) ∙ ap G.₁ zig ∙ G.F-id)

  is-reflective→unit-G-is-iso : ∀ {o} → C.is-invertible (unit.η (G.₀ o))
  is-reflective→unit-G-is-iso {o} = C.make-invertible (g-ff.to (ε _))
    (unit.is-natural _ _ _ ·· ap₂ C._∘_ refl η-comonad-commute ·· GF.annihilate zag)
    zag

  is-reflective→F-unit-is-iso : ∀ {o} → D.is-invertible (F.₁ (unit.η o))
  is-reflective→F-unit-is-iso {o} = D.make-invertible
    (ε _)
    (sym (counit.is-natural _ _ _) ∙ ap₂ D._∘_ refl (ap F.₁ (sym η-comonad-commute)) ∙ zig)
    zig
```
-->

We can now prove that the adjunction $L \dashv \iota$ is monadic.

```agda
is-reflective→is-monadic
  : ∀ {F : Functor C D} {G : Functor D C}
  → (adj : F ⊣ G) → is-reflective adj → is-monadic adj
is-reflective→is-monadic {C = C} {D = D} {F = F} {G} adj g-ff = eqv where
```

<!--
```agda
  module EM = Cat.Reasoning (Eilenberg-Moore C (L∘R adj))
  module C = Cat.Reasoning C
  module D = Cat.Reasoning D
  module F = Functor F
  module G = Functor G
  open Algebra-hom
  open Algebra-on
  open _⊣_ adj

  Comp : Functor D (Eilenberg-Moore C (L∘R adj))
  Comp = Comparison adj
  module Comp = Functor Comp
```
-->

It suffices to show that the comparison functor $D \to C^GF$ is fully
faithful and [[split essentially surjective]]. For full faithfulness,
observe that it's always faithful; The fullness comes from the
assumption that $G$ is ff.

```agda
  comp-ff : is-fully-faithful Comp
  comp-ff {x} {y} = is-iso→is-equiv isom where
    open is-iso
    isom : is-iso _
    isom .inv alg = equiv→inverse g-ff (alg .morphism)
    isom .rinv x = Algebra-hom-path _ (equiv→counit g-ff _)
    isom .linv x = equiv→unit g-ff _

```

To show that the comparison functor is split essentially surjective,
suppose we have an object $o$ admitting the structure of an
$GF$-algebra; We will show that $o \cong GFo$ as $GF$-algebras --- note
that $GF(o)$ admits a canonical (free) algebra structure. The algebra
map $\nu : GF(o) \to o$ provides an algebra morphism from $GF(o) \to o$,
and the morphism $o \to GF(o)$ is can be taken to be adjunction unit
$\eta$.

The crucial lemma in establishing that these are inverses is that
$\eta_{GFx} = GF(\eta_x)$, which follows because both of those morphisms
are right inverses to $G\eps_x$, which is an isomorphism because $\eps$
is.

```agda
  comp-seso : is-split-eso Comp
  comp-seso (ob , alg) = F.₀ ob , isom where
    Fo→o : Algebra-hom _ (L∘R adj) (Comp.₀ (F.₀ ob)) (ob , alg)
    Fo→o .morphism = alg .ν
    Fo→o .commutes = sym (alg .ν-mult)

    o→Fo : Algebra-hom _ (L∘R adj) (ob , alg) (Comp.₀ (F.₀ ob))
    o→Fo .morphism = unit.η _
    o→Fo .commutes =
        unit.is-natural _ _ _
      ∙ ap₂ C._∘_ refl (η-comonad-commute adj g-ff)
      ∙ sym (G.F-∘ _ _)
      ∙ ap G.₁ (sym (F.F-∘ _ _) ·· ap F.₁ (alg .ν-unit) ·· F.F-id)
      ∙ sym (ap₂ C._∘_ refl (sym (η-comonad-commute adj g-ff)) ∙ zag ∙ sym G.F-id)

    isom : Comp.₀ (F.₀ ob) EM.≅ (ob , alg)
    isom = EM.make-iso Fo→o o→Fo
      (Algebra-hom-path _ (alg .ν-unit))
      (Algebra-hom-path _ (
          unit.is-natural _ _ _
        ·· ap₂ C._∘_ refl (η-comonad-commute adj g-ff)
        ·· sym (G.F-∘ _ _)
        ·· ap G.₁ (sym (F.F-∘ _ _) ·· ap F.₁ (alg .ν-unit) ·· F.F-id)
        ·· G.F-id))

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
  {F : Functor C D} {G : Functor D C}
  (adj : F ⊣ G)
  where
  private
    module C = Cat.Reasoning C
    module D = Cat.Reasoning D
    module [D,D] = Cat.Reasoning Cat[ D , D ]
    module F = Func F
    module G = Func G
    module GF = Func (G F∘ F)
    module FG = Func (F F∘ G)
    open _⊣_ adj
```
-->

Let $\eps\inv$ be the (natural) inverse to the counit, and let
$f : \cC(G(X), G(Y))$. We can obtain a map $\cD(X,Y)$ by conjugating
with $\eps$ and its inverse.

```agda
  is-counit-iso→is-reflective : is-invertibleⁿ counit → is-reflective adj
  is-counit-iso→is-reflective counit-iso =
    is-iso→is-equiv $
      iso (λ f → ε _ D.∘ F.₁ f D.∘ ε⁻¹ _)
```

Proving that this conjugation forms an equivalence involves the usual
adjoint yoga. For the forward direction, we need to show that
$G(\eps \circ F(f) \circ \eps\inv) = f$; if we take the right adjunct,
this transforms our goal into $\eps \circ F(G(\eps \circ F(f) \circ \eps\inv)) = \eps \circ F(f)$.

From here, we can repeatedly apply naturality to commute the $\eps$
all the way to the end of the chain of morphisms. This yields
$\eps \circ F(f) \circ \eps\inv \circ \eps$, which is equal to
$\eps \circ F(f)$, as $\eps\inv$ is an inverse.

```agda
        (λ f → Equiv.injective (_ , R-adjunct-is-equiv adj) $
          ε _ D.∘ F.₁ (G.₁ (ε _ D.∘ F.₁ f D.∘ ε⁻¹ _))   ≡⟨ FG.popl (counit .is-natural _ _ _) ⟩
          (ε _ D.∘ ε _) D.∘ F.₁ (G.₁ (F.₁ f D.∘ ε⁻¹ _)) ≡⟨ D.extendr (FG.shufflel (counit .is-natural _ _ _)) ⟩
          (ε _ D.∘ F.₁ f) D.∘ ε _ D.∘ F.₁ (G.₁ (ε⁻¹ _)) ≡⟨ D.elimr (counit .is-natural _ _ _ ∙ counit-iso.invr ηₚ _) ⟩
          ε _ D.∘ F.₁ f                                 ∎)
```

The reverse direction follows from a quick application of naturality.

```agda
        (λ f →
          ε _ D.∘ F.₁ (G.₁ f) D.∘ ε⁻¹ _ ≡⟨ D.pulll (counit.is-natural _ _ _) ⟩
          (f D.∘ ε _) D.∘ ε⁻¹ _         ≡⟨ D.cancelr (counit-iso.invl ηₚ _) ⟩
          f                             ∎)
    where
      module counit-iso = is-invertibleⁿ counit-iso
      ε⁻¹ = counit-iso.inv .η
```

Furthermore, if we have *any* natural isomorphism $\alpha : FG \iso \Id$, then
the left adjoint is a reflector! To show this, we will construct an
inverse to the counit; our previous result will then ensure that $F$
is fully faithful.

To begin, recall that isos have the 2-out-of-3 property, so it suffices
to show that $\eps \circ \alpha$ is invertible. Next, note that we can
transfer the comonad structure on $FG$ onto a comonad structure on $\Id$
by repeatedly composing with $\alpha$; this yields a natural transformation
$\delta : \Id \to \Id$ that is a right inverse to $\eps \circ \alpha$.

Finally, all natural transformations $\Id \to \Id$ commute with one another,
so $\delta$ is also a right inverse, and $\eps \circ \alpha$ is invertible.

```agda
  FG-iso→is-reflective : (F F∘ G) ≅ⁿ Id → is-reflective adj
  FG-iso→is-reflective α =
    is-counit-iso→is-reflective $
    [D,D].invertible-cancell
      ([D,D].iso→invertible (α [D,D].Iso⁻¹))
      ([D,D].make-invertible δ right-ident right-ident⁻¹)
    where
      module α = Isoⁿ α

      δ : Id {C = D} => Id
      δ .η x = α.to .η x D.∘ α.to .η (F.F₀ (G.₀ x)) D.∘ F.₁ (unit.η (G.₀ x)) D.∘ α.from .η x
      δ .is-natural x y f =
          D.extendr (D.extendr (D.extendr (α.from .is-natural _ _ _)))
        ∙ D.pushl (D.pushr (D.pushr (F.weave (unit .is-natural _ _ _))))
        ∙ D.pushl (D.pushr (α.to .is-natural _ _ _))
        ∙ D.pushl (α.to .is-natural _ _ _)

      right-ident : (counit ∘nt α.from) ∘nt δ ≡ idnt
      right-ident = ext λ x →
          D.cancel-inner (α.invr ηₚ _)
        ∙ D.pulll (sym $ α.to .is-natural _ _ _)
        ∙ D.cancel-inner (F.annihilate zag)
        ∙ α.invl ηₚ _

      right-ident⁻¹ : δ ∘nt (counit ∘nt α.from) ≡ idnt
      right-ident⁻¹ = id-nat-commute δ (counit ∘nt α.from) ∙ right-ident
```
