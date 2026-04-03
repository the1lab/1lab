<!--
```agda
open import Cat.Functor.Naturality
open import Cat.Functor.Bifunctor
open import Cat.Instances.Product
open import Cat.Functor.Base
open import Cat.Bi.Solver
open import Cat.Bi.Base
open import Cat.Prelude

import Cat.Bi.Reasoning as Br
import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Bi.Lax-functor.Hom {o h ℓ} (C : Prebicategory o h ℓ) where
```

# The bicategorical Hom functor {defines="bicategorical-hom-functor"}

<!--
```agda
open Br C
open Hom hiding (id)

open Functor
open _=>_

private
  module Cat = Prebicategory (Cat h ℓ)
  module Lf  = Lax-functor
  module Pf  = Pseudofunctor
```
-->

The [[Hom functor]], which assigns to a pair of objects the set of
morphisms between them, has a direct analogue in bicategories.  In a
bicategory $\bf{C}$, the morphisms between two objects form a category
instead of a set, so in this setting we get a $\bf{Cat}$-valued
pseudofunctor.

Here, we define the covariant mapping $\hom(X,-)$ for a fixed object $X$
in $\bf{C}$.  The action of this pseudofunctor on 1-cells must take a
1-cell $f : A \to B$ in $\bf{C}$ to a functor $\hom(X,f) : \hom(X,A) \to
\hom(X,B)$, and this action itself should be functorial.  In other
words, we need a bifunctor $\hom(A,B) × \hom(X,A) \to \hom(X,B)$.  But
we already have such a bifunctor: the composition bifunctor of $\bf{C}$!

To complete this into a pseudofunctor, we must give a compositor natural
isomorphism with components $\hom(X,-)_1(f)\hom(X,-)(g) \To
\hom(X,-)_1(fg)$, and a unitor $\id \To \hom(X,-)_1(\id)$.  With
$\hom(X,-)$ acting by composition, we can unfold the definitions to see
that each component of the compositor should itself be a natural
transformation, with components $f(gh) \To (fg)h$, and similarly the
unitor should be a natural transformation with components $\id \To \id
h$.  Luckily, we have such natural transformations available to us: the
associator and left unitor in $\bf{C}$.

```agda
module _ (X : Ob) where

  Hom-from-bi : Pseudofunctor C (Cat h ℓ)
  Hom-from-bi = pf module Hom-from-bi where
    compositor
      : ∀ {A B C}
      → Uncurry Cat.compose F∘ (compose {X} {B} {C} F× compose {X} {A} {B})
      => compose F∘ Uncurry compose
    compositor .η (f , g)              = ▶-assoc.from
    compositor .is-natural _ _ (α , β) = ext λ h →
         extendl (◀-assoc.to .is-natural _ _ _)
      ∙∙ cdr (◀-▶-comm.from .is-natural _ _ _) ∙∙ ◀.pulll refl

    lf : Lax-functor C (Cat h ℓ)
    lf .Lf.P₀            = Hom X
    lf .Lf.P₁            = compose
    lf .Lf.compositor    = compositor
    lf .Lf.unitor        = unitor-l.to
    lf .Lf.hexagon f g h = ext λ _ → bicat! C
    lf .Lf.right-unit f  = ext λ _ → bicat! C
    lf .Lf.left-unit f   = ext λ _ → bicat! C

    pf : Pseudofunctor _ _
    pf .Pf.lax              = lf
    pf .Pf.unitor-inv       = Cr.iso→invertible Cat[ _ , _ ] unitor-l
    pf .Pf.compositor-inv _ = Cr.iso→invertible Cat[ _ , _ ] (▶-assoc ni⁻¹)
```

Note that if we unpack the definition, we see that the covariant action
of the $\hom$-functor works by postcomposition, just like in a
precategory.
