---
description: |
  Properties of adjoints.
---
<!--
```agda
open import Cat.Functor.Properties
open import Cat.Functor.Adjoint
open import Cat.Functor.Compose
open import Cat.Prelude

import Cat.Functor.Reasoning
import Cat.Natural.Reasoning
import Cat.Reasoning
```
-->
```agda
module Cat.Functor.Adjoint.Properties where
```

# Basic properties of adjoints

This file contains a collection of basic results about adjoint functors,
particularly focusing on when a left/right adjoint is [[faithful]], [[full]],
etc.

<!--
```agda
module _
  {oc ℓc od ℓd}
  {C : Precategory oc ℓc}
  {D : Precategory od ℓd}
  {L : Functor C D} {R : Functor D C}
  (L⊣R : L ⊣ R)
  where
  private
    module C = Cat.Reasoning C
    module D = Cat.Reasoning D
    module L = Cat.Functor.Reasoning L
    module R = Cat.Functor.Reasoning R
    open _⊣_ L⊣R
```
-->

## Faithful adjoints {defines="faithful-adjoint"}

Let $L \dashv R$ be a pair of adjoint functors. The following conditions
are equivalent:

1. $L$ is [[faithful]].
2. The unit of the adjunction is [[monic]].
3. $L$ reflects monomorphisms.

Let's start with (1 ⇒ 2). Suppose that $L$ is faithful, and that
$\eta \circ f = \eta \circ g$. $L$ is faithful, so it suffices to
show that $L(f) = L(g)$. Moreover, $L$ is a left adjoint, so it suffices
to show that the [[adjuncts]] $R(L(f)) \circ \eta$ and $R(L(g)) \circ \eta$
are equal. Finally, $\eta$ is natural, so it suffices to show that
$\eta \circ f = \eta \circ g$, which is exactly our hypothesis.

```agda
  left-faithful→unit-monic
    : is-faithful L
    → ∀ {x} → C.is-monic (η x)
  left-faithful→unit-monic faithful {x} f g ηf=ηg =
    faithful $ L-adjunct.injective L⊣R (unit.naturall ηf=ηg)
```

Proving that (2 ⇒ 1) is similarly easy. Suppose the unit is monic, and
$L(f) = L(g)$. As $\eta$ is monic, it suffices to show that
$\eta \circ f = \eta \circ g$. Additionally, $\eta$ is natural, so it
suffices to show that $R(L(f)) \circ \eta = R(L(g)) \circ \eta$, which
follows directly from our hypothesis.

```agda
  unit-monic→left-faithful
    : (∀ {x} → C.is-monic (η x))
    → is-faithful L
  unit-monic→left-faithful η-monic {x} {y} {f} {g} Lf=Lg =
    η-monic f g $ unit.viewr R.⟨ Lf=Lg ⟩
```

Next, let's show that (3 ⇒ 2). This follows from a very short calculation.

```agda
  left-reflects-monos→unit-monic
    : (∀ {x y} {f : C.Hom x y} → D.is-monic (L.₁ f) → C.is-monic f)
    → ∀ {x} → C.is-monic (η x)
  left-reflects-monos→unit-monic L-reflect {x} =
    L-reflect λ f g p →
      f                               ≡⟨ D.introl zig ⟩
      (ε (L.₀ x) D.∘ L.₁ (η x)) D.∘ f ≡⟨ D.extendr p ⟩
      (ε (L.₀ x) D.∘ L.₁ (η x)) D.∘ g ≡⟨ D.eliml zig ⟩
      g ∎
```

In general, [faithful functors reflect monomorphisms] so we get (1 ⇒ 3)
for free, finishing the proof.

[faithful functors reflect monomorphisms]: Cat.Functor.Morphism.html#faithful-functors

We also obtain dual results for faithful right adjoints, but we
omit the (nearly identical) proofs.

```agda
  right-faithful→counit-epic
    : is-faithful R
    → ∀ {x} → D.is-epic (ε x)

  counit-epic→right-faithful
    : (∀ {x} → D.is-epic (ε x))
    → is-faithful R

  right-reflects-epis→counit-epic
    : (∀ {x y} {f : D.Hom x y} → C.is-epic (R.₁ f) → D.is-epic f)
    → ∀ {x} → D.is-epic (ε x)
```

<!--
```agda
  right-faithful→counit-epic faithful {x} f g fε=gε =
    faithful $ R-adjunct.injective L⊣R $ counit.naturalr fε=gε

  counit-epic→right-faithful ε-epic {x} {y} {f} {g} Rf=Rg =
    ε-epic f g $ counit.viewl L.⟨ Rf=Rg ⟩

  right-reflects-epis→counit-epic R-reflect {x} =
    R-reflect λ f g p →
      C.intror zag ·· C.extendl p ·· C.elimr zag
```
-->

## Full adjoints {defines="full-adjoint"}

A left adjoint $L \dashv R$ is [[full]] if and only if the unit is a
split epimorphism.

For the forward direction, suppose that $L$ is full. We can then find
a $f : R(L(X)) \to X$ in the fibre of $L$ over $\eps_{L(X)} : L(R(L(X))) \to L(X)$.
Moreover, $f$ is a section of $\eta_{X}$; EG: $\eta \circ f = \id$.
By the usual [[adjunct]] yoga, it suffices to show that

$$
\eps_{L(X)} \circ L(\eta_{X} \circ f) = \eps_{L(X)} \circ L(id)
$$

which follows from a short calculation.

```agda
  left-full→unit-split-epic
    : is-full L
    → ∀ {x} → C.is-split-epic (η x)
  left-full→unit-split-epic full {x} = do
    (f , p) ← full (ε (L.₀ x))
    pure $ C.make-section f $
      R-adjunct.injective L⊣R $
        ε (L.₀ x) D.∘ L.₁ (η x C.∘ f) ≡⟨ L.removel zig ⟩
        L.F₁ f                        ≡⟨ p ⟩
        ε (L.₀ x)                     ≡⟨ D.intror L.F-id ⟩
        ε (L.₀ x) D.∘ L.₁ C.id        ∎
```

For the reverse direction, suppose that every component
the unit has a section, and let $f : L(X) \to L(Y)$. In particular,
$\eta_{Y}$ must have a section $s : R(L(Y)) \to Y$. Next, note that
thee composite $s \circ R(f) \circ \eta$ is a morphism $X \to Y$, so
all that remains is to check that $L(s \circ R(f) \circ \eta) = f$.

Now, $L$ is left adjoint, so we can take the adjunct of both sides
of this equality, reducing the problem to showing that

$$
R(L(s \circ R(f) \circ \eta)) \circ \eta = R(f) \circ \eta
$$

Next, $\eta$ is natural, so we can re-arrange our equation like so.
$$
\eta \circ s \circ R(f) \circ \eta = R(f) \circ \eta
$$

Finally, $\eta \circ s = id$, as $s$ is a section.

```agda
  unit-split-epic→left-full
    : (∀ {x} → C.is-split-epic (η x))
    → is-full L
  unit-split-epic→left-full η-split-epic {x} {y} f = do
    s ← η-split-epic {y}
    let module s = C.has-section s
    let in-im : L.₁ (s.section C.∘ L-adjunct L⊣R f) ≡ f
        in-im = L-adjunct.injective L⊣R $
          R.₁ (L.₁ (s.section C.∘ R.₁ f C.∘ η _)) C.∘ η _ ≡˘⟨ unit.is-natural _ _ _ ⟩
          η _ C.∘ s.section C.∘ R.F₁ f C.∘ η _            ≡⟨ C.cancell s.is-section ⟩
          R.₁ f C.∘ η _                                   ∎
    pure (s.section C.∘ L-adjunct L⊣R f , in-im)
```

Dual results hold for full right adjoints and split monos.

```agda
  right-full→counit-split-monic
    : is-full R
    → ∀ {x} → D.is-split-monic (ε x)

  counit-split-monic→right-full
    : (∀ {x} → D.is-split-monic (ε x))
    → is-full R
```

<!--
```agda
  right-full→counit-split-monic full {x} = do
    (f , p) ← full (η (R.₀ x))
    pure $ D.make-retract f $
      L-adjunct.injective L⊣R $
        R.₁ (f D.∘ ε x) C.∘ η (R.₀ x) ≡⟨ R.remover zag ⟩
        R.F₁ f                        ≡⟨ p ⟩
        η (R.₀ x)                     ≡⟨ C.introl R.F-id ⟩
        R.₁ D.id C.∘ η (R.F₀ x)       ∎

  counit-split-monic→right-full ε-split-monic {x} {y} f = do
    r ← ε-split-monic {x}
    let module r = D.has-retract r
    pure $
      R-adjunct L⊣R f D.∘ r.retract ,
      R-adjunct.injective L⊣R (counit.is-natural _ _ _ ∙ D.cancelr r.is-retract)
```
-->
