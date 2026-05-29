<!--
```agda
open import Cat.Functor.Equivalence.Path
open import Cat.Functor.Equivalence
open import Cat.Instances.Slice
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Instances.Slice.Twice {o ℓ} {C : Precategory o ℓ} where
```

<!--
```agda
open Cat.Reasoning C
open Functor
open /-Obj
open /-Hom
private variable
  a b : Ob
```
-->

# Iterated slice categories {defines="iterated-slice"}

An **iterated slice category**, something like $(\cC/B)/f$ for $f : A
\to B$ (regarded as an object over $B$), is something slightly
mind-bending to consider at face value: the objects are _families of
families-over-$B$_, indexed by the family $f$? It sounds like there's a
lot of room for complexity here, and that's only considering one
iteration!

Fortunately, there's actually _no such thing_. The slice of $\cC/B$ over
$f$ is isomorphic to the slice $\cC/A$, by a functor which is remarkably
simple to define, too. That's because the data of an object in
$(\cC/B)/f$ consists of a morphism $h : X \to B$, a morphism $g : X \to
A$, and a proof $p : h = fg$. But by [[contractibility of singletons]],
the pair $(h, p)$ is redundant! The only part that actually matters is
the morphism $g : X \to A$.

One direction of the isomorphism inserts the extra (redundant!)
information, by explicitly writing out $h = fg$ and setting $p = \refl$.
Its inverse simply discards the redundant information. We construct both
of the functors here, in components.

We construct the functor $(\cC/B)/f \to \cC/A$ and show that it is
an isomorphism.

```agda
Twice-slice : (f : Hom a b) → Functor (Slice (Slice C b) (cut f)) (Slice C a)
Twice-slice _ .F₀ x .dom = x .dom .dom
Twice-slice _ .F₀ x .map = x .map .map

Twice-slice _ .F₁ h .map = h .map .map
Twice-slice _ .F₁ h .com = ap map (h .com)

Twice-slice _ .F-id    = ext refl
Twice-slice _ .F-∘ _ _ = ext refl

Twice≃Slice : (f : Hom a b) → is-precat-iso (Twice-slice f)
Twice≃Slice f .is-precat-iso.has-is-iso = is-iso→is-equiv λ where
  .is-iso.from o .dom .dom → o .dom
  .is-iso.from o .dom .map → f ∘ o .map
  .is-iso.from o .map .map → o .map
  .is-iso.from o .map .com → refl
  .is-iso.rinv o           → /-Obj-path refl refl
  .is-iso.linv o           → /-Obj-path (/-Obj-path refl (o .map .com)) (/-Hom-pathp _ _ refl)
Twice≃Slice f .is-precat-iso.has-is-ff {x} {y} = is-iso→is-equiv λ where
  .is-iso.from g .map .map → g .map
  .is-iso.from g .map .com → car (sym (y .map .com)) ∙∙ pullr (g .com) ∙∙ x .map .com
  .is-iso.from g .com      → ext (g .com)
  .is-iso.rinv _           → ext refl
  .is-iso.linv _           → ext refl

open module Twice≃Slice {a} {b} (f : Hom a b) =
  is-equivalence (is-precat-iso→is-equivalence (Twice≃Slice f))
  renaming (F⁻¹ to Slice-twice; F⊣F⁻¹ to Twice⊣Slice) using () public

Twice≡Slice : (f : Hom a b) → Slice (Slice C b) (cut f) ≡ Slice C a
Twice≡Slice f = Precategory-path (Twice-slice f) (Twice≃Slice f)
```
