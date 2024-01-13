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

~~~{.quiver .short-15}
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
$\cC$ as the category of algebras for an (idempotent) monad on
$\cD$.
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
    morp = D.make-iso (counit.ε _) (g-ff.from (unit.η _)) invl invr
      where abstract
      invl : counit.ε o D.∘ g-ff.from (unit.η (G.₀ o)) ≡ D.id
      invl = fully-faithful→faithful {F = G} g-ff (
        G.₁ (counit.ε o D.∘ _)                 ≡⟨ G.F-∘ _ _ ⟩
        G.₁ (counit.ε o) C.∘ G.₁ (g-ff.from _) ≡⟨ C.refl⟩∘⟨  g-ff.ε _ ⟩
        G.₁ (counit.ε o) C.∘ unit.η (G.₀ o)    ≡⟨ zag ∙ sym G.F-id ⟩
        G.₁ D.id                               ∎)

      invr : g-ff.from (unit.η (G.₀ o)) D.∘ counit.ε o ≡ D.id
      invr = fully-faithful→faithful {F = G} g-ff (ap G.₁ (
        g-ff.from _ D.∘ counit.ε _             ≡˘⟨ counit.is-natural _ _ _ ⟩
        counit.ε _ D.∘ F.₁ (G.₁ (g-ff.from _)) ≡⟨ D.refl⟩∘⟨ F.⟨ g-ff.ε _ ⟩ ⟩
        counit.ε _ D.∘ F.₁ (unit.η _)          ≡⟨ zig ⟩
        D.id                                   ∎))

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
  is-reflective→unit-G-is-iso {o} = C.make-invertible (g-ff.to (counit.ε _))
    (unit.is-natural _ _ _ ·· ap₂ C._∘_ refl η-comonad-commute ·· GF.annihilate zag)
    zag

  is-reflective→F-unit-is-iso : ∀ {o} → D.is-invertible (F.₁ (unit.η o))
  is-reflective→F-unit-is-iso {o} = D.make-invertible
    (counit.ε _)
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
