<!--
```agda
open import Cat.Prelude

import Cat.Diagram.Equaliser
import Cat.Diagram.Zero
```
-->

```agda
module Cat.Diagram.Equaliser.Kernel {o ℓ} (C : Precategory o ℓ) where
```

<!--
```agda
open import Cat.Reasoning C

open Cat.Diagram.Equaliser C
open Cat.Diagram.Zero C
```
-->

# Kernels

In a category with equalisers and a zero object $0$, a **kernel** of a
morphism $f : a \to b$ is an equaliser of $f$ and the zero morphism $0 :
a \to b$, hence a subobject $\mathrm{ker}(f) \mono a$ of the domain of
$f$.

~~~{.quiver .short-15}
\[\begin{tikzcd}
  {\ker(f)} & a & b
  \arrow["0", shift left=1, from=1-2, to=1-3]
  \arrow["f"', shift right=1, from=1-2, to=1-3]
  \arrow[hook, from=1-1, to=1-2]
\end{tikzcd}\]
~~~

```agda
module _ (∅ : Zero) where
  open Zero ∅

  is-kernel : ∀ {a b ker} (f : Hom a b) (k : Hom ker a) → Type _
  is-kernel f = is-equaliser f zero→

  kernels-are-subobjects
    : ∀ {a b ker} {f : Hom a b} (k : Hom ker a)
    → is-kernel f k → is-monic k
  kernels-are-subobjects = is-equaliser→is-monic

  record Kernel {a b} (f : Hom a b) : Type (o ⊔ ℓ) where
    field
      {ker} : Ob
      kernel : Hom ker a
      has-is-kernel : is-kernel f kernel
    open is-equaliser has-is-kernel public
```

**Lemma**: Let $\cC$ be a category with equalisers and a zero object.
In $\cC$, the kernel of a kernel is zero. First, note that if a
category has a choice of zero object and a choice of equaliser for any
pair of morphisms, then it has canonically-defined choices of kernels:

```agda
module Canonical-kernels
  (zero : Zero) (eqs : ∀ {a b} (f g : Hom a b) → Equaliser f g) where
  open Zero zero
  open Kernel

  Ker : ∀ {a b} (f : Hom a b) → Kernel zero f
  Ker f .ker           = _
  Ker f .kernel        = eqs f zero→ .Equaliser.equ
  Ker f .has-is-kernel = eqs _ _ .Equaliser.has-is-eq
```

We now show that the maps $! : \ker\ker f \to \emptyset$ and $¡ :
\emptyset \to \ker\ker f$ are inverses. In one direction the composite
is in $\emptyset \to \emptyset$, so it is trivially unique. In the other
direction, we have maps $\ker\ker f \to \ker\ker f$, which, since $\ker$
is a limit, are uniquely determined _if_ they are cone homomorphisms.

```agda
  Ker-of-ker≃∅ : ∀ {a b} (f : Hom a b) → Ker (Ker f .kernel) .ker ≅ ∅
  Ker-of-ker≃∅ f = make-iso ! ¡ (!-unique₂ _ _) p where
    module Kf = Kernel (Ker f)
    module KKf = Kernel (Ker (Ker f .kernel))
```

The calculation is straightforward enough: The hardest part is showing
that $\ker f \circ \ker \ker f = 0$ (here we are talking about the
inclusion maps, not the objects) --- but recall that $\ker \ker f$
equalises $\ker f$ and $0$, so we have

$$
\ker f \circ \ker \ker f =
0 \circ \ker \ker f =
0
$$

```agda
    p : ¡ ∘ ! ≡ id
    p = KKf.unique₂ (zero-comm _ _) (zero-∘l _)
          (Kf.unique₂ (extendl (zero-comm _ _))
                      (pulll KKf.equal ∙ idr _)
                      (zero-comm _ _))
```
