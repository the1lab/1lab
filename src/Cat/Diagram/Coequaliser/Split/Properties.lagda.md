```agda
open import Cat.Prelude

open import Cat.Diagram.Limit.Finite

import Cat.Diagram.Coequaliser.Split as SplitCoeq
import Cat.Diagram.Pullback
import Cat.Diagram.Congruence
import Cat.Reasoning
import Cat.Functor.Reasoning

module Cat.Diagram.Coequaliser.Split.Properties where
```

# Properties of split coequalizers

This module proves some general properties of [split coequalisers].

[split coequalisers]: Cat.Diagram.Coequaliser.Split.html

## Absoluteness

The property of being a split coequaliser is a purely diagrammatic one, which has
the lovely property of being preserved by _all_ functors. We call such colimits
**absolute**.

```agda
module _ {o o′ ℓ ℓ′}
         {C : Precategory o ℓ} {D : Precategory o′ ℓ′}
         (F : Functor C D) where
```
<!--
```agda
  private
    module C = Cat.Reasoning C
    module D = Cat.Reasoning D
    open Cat.Functor.Reasoning F
    open SplitCoeq
    variable
      A B E : C.Ob 
      f g e s t : C.Hom A B
```
-->

The proof follows the fact that functors preserve diagrams, and reduces to a bit
of symbol shuffling.

```agda
  is-split-coequaliser-absolute
    : is-split-coequaliser C f g e s t
    → is-split-coequaliser D (F₁ f) (F₁ g) (F₁ e) (F₁ s) (F₁ t)
  is-split-coequaliser-absolute
    {f = f} {g = g} {e = e} {s = s} {t = t} split-coeq = F-split-coeq
    where
      open is-split-coequaliser split-coeq

      F-split-coeq : is-split-coequaliser D _ _ _ _ _
      F-split-coeq .coequal = weave coequal
      F-split-coeq .rep-section = annihilate rep-section
      F-split-coeq .witness-section = annihilate witness-section
      F-split-coeq .commute = weave commute
```

## Split Epis and Kernel Pairs

We've already seen one way to construct a split coequalizer from a split epimorphism,
via `is-split-epic→is-split-coequalizer`{.Agda}. However, this is not the only way!
A somewhat more intuitive construction can be used which involves taking the kernel
pair of some split epimorphism $e : B \to C$.

```agda
module _ {o ℓ} {C : Precategory o ℓ} where
  open Cat.Reasoning C
  open Cat.Diagram.Pullback C
  open SplitCoeq C
```

First, some preliminaries. We can construct a morphism from $B$ into the kernel
pair of $e$ by like so:

~~~{.quiver}
\[\begin{tikzcd}
	B \\
	& A & B \\
	& B & C
	\arrow[from=2-2, to=3-2]
	\arrow[from=2-2, to=2-3]
	\arrow["e"', from=2-3, to=3-3]
	\arrow["e", from=3-2, to=3-3]
	\arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=2-2, to=3-3]
	\arrow[color={rgb,255:red,214;green,92;blue,92}, dashed, from=1-1, to=2-2]
	\arrow["id"', curve={height=12pt}, from=1-1, to=3-2]
	\arrow["{s \circ e}", curve={height=-12pt}, from=1-1, to=2-3]
\end{tikzcd}\]
~~~

Using our intuition of split coequalisers as quotients with representatives,
this map will pair up an element of $b$ with it's representative.

```agda
  private
    represent
      : ∀ {A B C} {p₁ p₂ : Hom A B} {e : Hom B C} {s : Hom C B}
      → (kp : is-pullback p₁ e p₂ e)
      → (section : s is-section-of e)
      → Hom B A
    represent {e = e} {s = s} kp section = limiting commutes where
        open is-pullback kp
        abstract
          commutes : e ∘ id ≡ e ∘ s ∘ e
          commutes = 
            e ∘ id    ≡⟨ id-comm ⟩
            id ∘ e    ≡⟨ pushl (sym section) ⟩
            e ∘ s ∘ e ∎
```

This map lets us construct the following split coequaliser:
~~~{.quiver}
\[\begin{tikzcd}
	A & B & C
	\arrow["{p_1}", shift left=3, from=1-1, to=1-2]
	\arrow["{p_2}"', shift right=3, from=1-1, to=1-2]
	\arrow["r"{description}, from=1-2, to=1-1]
	\arrow["e", shift left=2, from=1-2, to=1-3]
	\arrow["s", shift left=2, from=1-3, to=1-2]
\end{tikzcd}\]
~~~

All of the required commuting squares exist due to our clever choice
of map into the kernel pair.

```agda
  is-split-epic→is-split-coequalizer-of-kernel-pair
    : ∀ {A B C} {p₁ p₂ : Hom A B} {e : Hom B C} {s : Hom C B}
    → (kp : is-pullback p₁ e p₂ e)
    → (section : s is-section-of e)
    → is-split-coequaliser p₁ p₂ e s (represent kp section)
  is-split-epic→is-split-coequalizer-of-kernel-pair
    {p₁ = p₁} {p₂ = p₂} {e = e} {s = s} kp section = split-coeq where
      open is-pullback kp
      open is-split-coequaliser

      split-coeq : is-split-coequaliser _ _ _ _ _
      split-coeq .coequal = square
      split-coeq .rep-section = section
      split-coeq .witness-section = p₁∘limiting
      split-coeq .commute = sym p₂∘limiting
```

We also provide a bundled form of this lemma.

```agda
  split-epic→split-coequalizer-of-kernel-pair
    : ∀ {B C} {e : Hom B C}
    → (kp : Pullback e e)
    → is-split-epic e
    → Split-coequaliser (Pullback.p₁ kp) (Pullback.p₂ kp)
  split-epic→split-coequalizer-of-kernel-pair
    {e = e} kp split-epic = split-coeq where
      open Pullback kp
      open is-split-epic split-epic
      open Split-coequaliser
   
      split-coeq : Split-coequaliser _ _
      split-coeq .coapex = _
      split-coeq .coeq = e
      split-coeq .rep = split
      split-coeq .witness = represent has-is-pb section
      split-coeq .has-is-split-coeq =
        is-split-epic→is-split-coequalizer-of-kernel-pair has-is-pb section
```


## Congruences and Quotients

When motivating split coequalisers, we discussed how they arise naturally from
quotients equipped with a choice of representatives of equivalence classes.
Let's go the other direction, and show that split coequalizers induce [quotients].
The rough idea of the construction is that we can construct an idempotent $A \to A$
that takes every $a : A$ to it's canonical representative, and then to take
the kernel pair of that morphism to construct a congruence.

[quotients]: Cat.Diagram.Congruence.html#quotient-objects
[kernel pair]: Cat.Diagram.Congruence.html#quotient-objects

```agda
module _ {o ℓ}
         {C : Precategory o ℓ}
         (fc : Finitely-complete C)
         where
```

<!--
```agda
  open Cat.Reasoning C
  open Cat.Diagram.Pullback C
  open Cat.Diagram.Congruence fc
  open SplitCoeq C
  open Finitely-complete fc
  open Cart
```
-->

```agda
  split-coequaliser→is-quotient-of 
    : ∀ {R A A/R} {i r : Hom R A} {q : Hom A A/R}
        {rep : Hom A/R A} {witness : Hom A R}
      → is-split-coequaliser i r q rep witness
      → is-quotient-of (Kernel-pair (r ∘ witness)) q
  split-coequaliser→is-quotient-of
    {i = i} {r = r} {q = q} {rep = rep} {witness = witness} split-coeq =
    is-split-coequaliser→is-coequalizer quotient-split
      where
        open is-split-coequaliser split-coeq
        module R′ = Pullback (pullbacks (r ∘ witness) (r ∘ witness))
```

We will need to do a bit of symbol munging to get the right split coequaliser here,
as the morphisms don't precisely line up due to the fact that we want to be working
with the kernel pair, not `R`.

However, we first prove a small helper lemma. If we use the intuition of `R`
as a set of pairs of elements and their canonical representatives, then this
lemma states that the representative of $a : A$ is the same as the representative _of_
the representative of $a$.

```agda
        same-rep : (r ∘ witness) ∘ i ≡ (r ∘ witness) ∘ r
        same-rep =
          (r ∘ witness) ∘ i ≡˘⟨ commute ⟩∘⟨refl ⟩
          (rep ∘ q) ∘ i     ≡⟨ extendr coequal ⟩
          (rep ∘ q) ∘ r     ≡⟨ commute ⟩∘⟨refl ⟩
          (r ∘ witness) ∘ r ∎
```

Now, onto the meat of the proof. This is mostly mindless algebraic manipulation
to get things to line up correctly.

```agda
        quotient-split :
          is-split-coequaliser
            (π₁ ∘ ⟨ R′.p₁ , R′.p₂ ⟩) (π₂ ∘ ⟨ R′.p₁ , R′.p₂ ⟩)
            q rep (R′.limiting same-rep ∘ witness)
        quotient-split .coequal = retract→is-monic rep-section _ _ $
          rep ∘ q ∘ π₁ ∘ ⟨ R′.p₁ , R′.p₂ ⟩ ≡⟨ refl⟩∘⟨ refl⟩∘⟨ π₁∘⟨⟩ ⟩
          rep ∘ q ∘ R′.p₁                  ≡⟨ pulll commute ⟩
          (r ∘ witness) ∘ R′.p₁            ≡⟨ R′.square ⟩
          (r ∘ witness) ∘ R′.p₂            ≡⟨ pushl (sym commute) ⟩
          rep ∘ q ∘ R′.p₂                  ≡˘⟨ refl⟩∘⟨ refl⟩∘⟨ π₂∘⟨⟩ ⟩
          rep ∘ q ∘ π₂ ∘ ⟨ R′.p₁ , R′.p₂ ⟩ ∎
        quotient-split .rep-section = rep-section
        quotient-split .witness-section =
          (π₁ ∘ ⟨ R′.p₁ , R′.p₂ ⟩) ∘ R′.limiting same-rep ∘ witness ≡⟨ π₁∘⟨⟩ ⟩∘⟨refl ⟩
          R′.p₁ ∘ R′.limiting same-rep ∘ witness                    ≡⟨ pulll R′.p₁∘limiting ⟩
          i ∘ witness                                               ≡⟨ witness-section ⟩
          id ∎
        quotient-split .commute =
          rep ∘ q                                                   ≡⟨ commute ⟩
          r ∘ witness                                               ≡⟨ pushl (sym R′.p₂∘limiting) ⟩
          R′.p₂ ∘ R′.limiting same-rep ∘ witness                    ≡˘⟨ π₂∘⟨⟩ ⟩∘⟨refl ⟩
          (π₂ ∘ ⟨ R′.p₁ , R′.p₂ ⟩) ∘ R′.limiting same-rep ∘ witness ∎
```

