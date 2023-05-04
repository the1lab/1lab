<!--
```agda
open import Cat.Displayed.Instances.Pullback
open import Cat.Displayed.Instances.Slice
open import Cat.Displayed.Composition
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Functor
open import Cat.Diagram.Pullback
open import Cat.Displayed.Total
open import Cat.Instances.Slice
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Reasoning
import Cat.Reasoning
```
-->

```agda
module Cat.Displayed.Instances.DisplayedFamilies
  {o ℓ o' ℓ'} {B : Precategory o ℓ} (E : Displayed B o' ℓ')
  where
```

<!--
```agda
open Cat.Reasoning B
open Cat.Displayed.Reasoning E
open Functor

open Total-hom
open /-Obj
open Slice-hom
```
-->

# The Displayed Family Fibration

The [family fibration] is a critical part of the theory of fibrations,
as it acts as a stepping off point for generalizing structure found
in 1-categories to structures in fibrations. However, it is deeply
entangled in the meta-theory, as it uses the fact that the type of
objects of a precategory is, well, a type.

[family fibration]: Cat.Displayed.Instances.Family.html

If we wish to generalize some 1-categorical phenomena, we will need
a version of the family fibration that represents families
**internal** to a fibration, where objects should be $\cB$-indexed
families of $\cE$ objects. To construct such a fibration, we recall
that every family $P : X \to \ty$ is equivalent to the total space
of it's fibres (see [here] for more details). It's quite rare for
$\cB$ to have something that looks like a universe, but it **does**
have enough structure to talk about fibres! We can consider a morphism
$\cB(a, x)$ to be a sort of "generalized family" over $x$, where $a$ is
playing the role of the total space. Objects $a' : \cE_{a}$ over $a$
then encode an $x$-indexed family of $\cE$ objects.

[here]: 1Lab.Univalence.html#object-classifiers

This is all quite abstract, so let's look at an example. Consider
some category $\cE$ fibred over $\Sets$. There is already a natural notion
of an $I$-indexed family of $\cE$-objects here; namely, a map
$P : I \to \set$ and a map $X : (i : I) \to \cE_{P(i)}$.
To see that we obtain the definition from before, note that we can turn
this family of sets into a map $\mathrm{fst} : \Sigma (i : I) P(i) \to I$ by
taking the total space of $P$. Furthermore, $\Sigma (i : I) P(i)$
is a set, so we can consider the space of objects $\cE_{\Sigma (i : I) P(i)}$.
We can embed each $X(i) : E_{P(i)}$ into $\cE_{\Sigma (i : I) P(i)}$
by reindexing along the second projection $\Sigma (i : I) P(i) \to P(i)$

To show the reverse direction, suppose we have some function $f : A \to I$,
along with an object $\cE_{A}$. We can obtain a family of sets $f^{-1} : I \to \set$
by taking the fibres of $f$. Furthermore, note that for each $i : I$, we
have a map $f^{-1}(i) \to A$ from the fibre of $f$ at $A$ to $A$; reindexing
along this map yields an object $\cE_{f^{-1}(i)}$ as desired.

Now that we are armed with the intuition, on with the construction!
Recall that the object objects over $x : \cB$ shall be triples
$(a : \cB) \times \cB(a, x) \times \cE_{a}$, and morphisms
$f : (a, f, a') \to (b, g, b')$ over $u : x \to y$ are given by triples
$(k : \cB(a, b)) \times (u \circ f = g \circ k) \times \cE_{k}(a', b')$.
The first portion of this data can be obtained by using the
[codomain fibration] over $\cB$. The remaining data involving $\cE$ is
then added by composing the codomain fibration with the [base change]
of $\cE$ along the functor $\mathrm{Dom} : \int B^{\to} \to B$ that takes
the domain of a morphism in the arrow category (which **is** the total
category of the codomain fibration).

[codomain fibration]: Cat.Displayed.Instances.Slice.html
[base change]: Cat.Displayed.Instances.Pullback.html

```agda
Dom : Functor (∫ (Slices B)) B
Dom .F₀ f = f .snd .domain
Dom .F₁ sq = sq .preserves .to
Dom .F-id = refl
Dom .F-∘ _ _ = refl

Disp-family : Displayed B (o ⊔ ℓ ⊔ o') (ℓ ⊔ ℓ')
Disp-family = Slices B D∘ Change-of-base Dom E

private
  module Disp-family = Displayed Disp-family
```

Now, that was quite a bit of abstract nonsense, so let's verify that
the nonsense actually makes sense by characterizing the objects and
morphisms of our category. As expected, objects consist of the triples
described above.

```agda
fam-over : ∀ {x} → (a : Ob) → Hom a x → Ob[ a ] → Disp-family.Ob[ x ]
fam-over a f a' .fst .domain = a
fam-over a f a' .fst .map = f
fam-over a f a' .snd = a'

module Fam-over {x} (P : Disp-family.Ob[ x ]) where

  tot : Ob
  tot = P .fst .domain

  fam : Hom tot x
  fam = P .fst .map

  tot′ : Ob[ tot ]
  tot′ = P .snd

open Fam-over
```

We glossed over the morphisms above, so let's go more into detail here.
A morphism between displayed families $P, Q$ is given by a map between
$\cB$-valued total spaces; this map must commute with the family structure
on $P$ and $Q$. Finally, we have a map between the $\cE$-valued total
spaces.

```agda
module Fam-over-hom
  {x y} {u : Hom x y} {P : Disp-family.Ob[ x ]} {Q : Disp-family.Ob[ y ]}
  (fᵢ : Disp-family.Hom[ u ] P Q)
  where

  map-tot : Hom (tot P) (tot Q)
  map-tot = fᵢ .fst .to

  fam-square : u ∘ fam P ≡ fam Q ∘ map-tot
  fam-square = fᵢ .fst .commute

  map-tot′ : Hom[ map-tot ] (tot′ P) (tot′ Q)
  map-tot′ = fᵢ .snd

open Fam-over-hom

fam-over-hom
  : ∀ {x y} {u : Hom x y} {P : Disp-family.Ob[ x ]} {Q : Disp-family.Ob[ y ]}
  → (f : Hom (tot P) (tot Q))
  → u ∘ fam P ≡ fam Q ∘ f
  → Hom[ f ] (tot′ P) (tot′ Q)
  → Disp-family.Hom[ u ] P Q
fam-over-hom f p f' .fst .to = f
fam-over-hom f p f' .fst .commute = p
fam-over-hom f p f' .snd = f'
```

## As a fibration

If $\cE$ is a fibration, and $\cB$ has all pullbacks, then the category of displayed
families is also a fibration. This follows by more abstract nonsense. In fact, this
proof is **why** we defined it using abstract nonsense!

```agda
module _
  (fib : Cartesian-fibration E)
  (pb : ∀ {x y z} (f : Hom x y) (g : Hom z y) → Pullback B f g)
  where

  Disp-family-fibration : Cartesian-fibration Disp-family
  Disp-family-fibration =
    fibration-∘ (Codomain-fibration B pb) (Change-of-base-fibration Dom E fib)
```

## Constant Families

There is a vertical functor from $\cE$ to the category of $\cE$-valued
families that takes each $\cE_{x}$ to the constant family.

```agda
ConstDispFam : Vertical-functor E Disp-family
ConstDispFam .Vertical-functor.F₀′ {x = x} x' =
  fam-over x id x'
ConstDispFam .Vertical-functor.F₁′ {f = f} f' =
  fam-over-hom f id-comm f'
ConstDispFam .Vertical-functor.F-id′ =
  Slice-pathp B refl refl ,ₚ sym (transport-refl _)
ConstDispFam .Vertical-functor.F-∘′ =
  Slice-pathp B refl refl ,ₚ sym (transport-refl _)
```

This functor is in fact fibred, though the proof is somewhat involved!

```agda
ConstDispFam-fibred : is-vertical-fibred ConstDispFam
ConstDispFam-fibred {a = a} {b} {a′} {b′} {f = f} f′ f′-cart = cart where
  open Vertical-functor ConstDispFam
  module f′ = is-cartesian f′-cart
  open is-cartesian
```

We begin by fixing some notation for the constant family on `b′`.

```agda
  Δb′ : Disp-family.Ob[ b ]
  Δb′ = fam-over b id b′
```

Next, a short yet crucial lemma: if we have a displayed family
over $x$, a map $m : \cB(x, a)$, and a morphism of displayed families
from $P$ to the constant family on $b'$, then we can construct a map
from the displayed total space of $P$ to $a'$. This is constructed via
the universal map of the cartesian morphism $f'$.

```agda
  coh : ∀ {x : Ob} {P : Disp-family.Ob[ x ]}
      → (m : Hom x a) (h′ : Disp-family.Hom[ f ∘ m ] P Δb′)
      → f ∘ (m ∘ fam P) ≡ map-tot h′
  coh m h′ = assoc _ _ _ ∙ fam-square h′ ∙ idl _

  tot-univ : {x : Ob} {P : Disp-family.Ob[ x ]} (m : Hom x a)
    → (h′ : Disp-family.Hom[ f ∘ m ] P Δb′)
    → Hom[ m ∘ fam P ] (tot′ P) a′
  tot-univ {P = P} m h′ =
    f′.universal (m ∘ fam P) $ hom[ coh m h′ ]⁻ (map-tot′ h′)
```

We can use this lemma to construct a universal map in $\cE$.

```agda
  cart : is-cartesian Disp-family f (F₁′ f′)
  cart .universal {u′ = u′} m h′ =
    fam-over-hom (m ∘ fam u′) (sym (idl _)) (tot-univ m h′)
```

Commutivity and uniqueness follow from the fact that $f'$ is cartesian.

```agda
  cart .commutes {x} {P} m h′ =
    Σ-path (Slice-pathp B _ (coh m h′)) $ from-pathp $ cast[] $
      hom[] (f′ ∘′ map-tot′ (cart .universal m h′)) ≡[]⟨ ap hom[] (f′.commutes _ _) ⟩
      hom[] (hom[] (map-tot′ h′))                   ≡[ coh m h′ ]⟨ to-pathp⁻ (hom[]-∙ _ _ ∙ reindex _ _) ⟩
      map-tot′ h′ ∎
  cart .unique {x} {P} {m = m} {h′ = h′} m′ p =
    Σ-path (Slice-pathp B refl (sym (fam-square m′ ∙ idl _)))
    $ f′.unique _ $ from-pathp⁻ $ cast[] {q = coh m h′} $
      f′ ∘′ hom[] (map-tot′ m′) ≡[]⟨ to-pathp (smashr _ (ap (f ∘_) (fam-square m′ ∙ idl _)) ∙ reindex _ _) ⟩
      hom[] (f′ ∘′ map-tot′ m′) ≡[]⟨ ap map-tot′ p ⟩
      map-tot′ h′               ∎
```

We also provide a bundled version of this functor.

```agda
ConstDispFamVf : Vertical-fibred-functor E Disp-family
ConstDispFamVf .Vertical-fibred-functor.vert = ConstDispFam
ConstDispFamVf .Vertical-fibred-functor.F-cartesian = ConstDispFam-fibred
```
