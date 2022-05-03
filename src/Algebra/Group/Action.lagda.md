```agda
open import Algebra.Group.Cat.Base
open import Algebra.Prelude
open import Algebra.Group

open import Cat.Instances.Delooping

import Cat.Functor.Reasoning as Functor-kit

module Algebra.Group.Action where
```

<!--
```agda
open Functor
```
-->

# Group actions

A useful way to think about [groups] is to think of their elements as
encoding "symmetries" of a particular object. For a concrete example,
consider the group $(\bb{R}, +, 0)$ of real numbers under addition, and
consider the unit circle^[this is _not_ the higher inductive type [$S^1$],
but rather the usual definition of the circle as a subset of $\ca{C}$.]
sitting in $\bb{C}$. Given a real number $x : \bb{R}$, we can consider
the "action" on the circle defined by

[groups]: Algebra.Group.html
[$S^1$]: 1Lab.HIT.S1.html

$$
a \mapsto e^{ix}a\text{,}
$$

which "visually" has the effect of rotating the point $a$ so it lands
$x$ radians around the circle, in the counterclockwise direction. Each
$x$-radian rotation has an inverse, given by rotation $x$ radians in the
clockwise direction; but observe that this is the same as rotating $-x$
degrees counterclockwise. Addiitonally, observe that rotating by zero
radians does nothing to the circle.

We say that $\bb{R}$ _acts_ on the circle by counterclockwise rotation;
What this means is that to each element $x : \bb{R}$, we assign a map
$\bb{C} \to \bb{C}$ in a way _compatible_ with the group structure:
Additive inverses "translate to" inverse maps, addition translates to
function composition, and the additive identity is mapped to the
identity function. Note that since $\bb{C}$ is a set, this is
equivalently a [group homomorphism]

$$
\bb{R} \to \id{Sym}(\bb{C})\text{,}
$$

where the codomain is the [group of symmetries] of $\bb{C}$. But what if
we want a group $G$ to act on an object $X$ of a more general
[category], rather than an object of $\sets$?

[group homomorphism]: Algebra.Group.html#group-homomorphisms
[group of symmetries]: Algebra.Group.html#symmetric-groups
[category]: Cat.Base.html

## Automorphism groups

The answer is that, for an object $X$ of some category $\ca{C}$, the
collection of all [isomorphisms] $X \cong X$ forms a group under
composition, generalising the construction of $\id{Sym}(X)$ to objects
beyond sets! We give refer to a "self-isomorphism" as an
**automorphism**, and denote their group by $\id{Aut}(X)$.

[isomorphisms]: Cat.Morphism.html#isos

```agda
module _ {o ℓ} (C : Precategory o ℓ) where
  private module C = Cat C

  Aut : C.Ob → Group _
  Aut X = (X C.≅ X) ,
    make-group C.≅-is-set C.id-iso (λ g f → f C.∘Iso g) C._Iso⁻¹
      (λ _ _ _ → C.≅-pathp refl refl (sym (C.assoc _ _ _)))
      (λ x → C.≅-pathp refl refl (x .C._≅_.invr))
      (λ x → C.≅-pathp refl refl (x .C._≅_.invl))
      (λ x → C.≅-pathp refl refl (C.idl _))
```

Suppose we have a category $\ca{C}$, an object $X : \ca{C}$, and a group
$G$; A **$G$-action on $X$** is a group homomorphism $G \to
\id{Aut}(X)$.

```agda
  Action : Group ℓ → C.Ob → Type _
  Action G X = Groups.Hom G (Aut X)
```

# As functors

Recall that we defined the [delooping] of a [monoid] $M$ into a category
as the category $\bf{B}M$ with a single object $\bull$, and $\hom(\bull,
\bull) = M$. If we instead deloop a group $G$ into a group $\bf{B}G$,
then functors $F : \bf{B}G \to \ca{C}$ correspond precisely to actions
of $G$ on the object $F(\bull)$!

[delooping]: Cat.Instances.Delooping.html
[monoid]: Algebra.Monoid.html

```agda
  Functor→action
    : {G : Group ℓ} (F : Functor (B (Group-on.underlying-monoid (G .snd) .snd)) C)
    → Action G (F .F₀ tt)
  Functor→action {G = G} F .fst el =
    C.make-iso (F .F₁ el) (F .F₁ (el ⁻¹))
               (F.annihilate inverser)
               (F.annihilate inversel)
    where
      open Group-on (G .snd)
      module F = Functor-kit F
  Functor→action F .snd .Group-hom.pres-⋆ x y = C.≅-pathp refl refl (F .F-∘ _ _)

  Action→functor
    : {G : Group ℓ} {X : C.Ob} (A : Action G X)
    → Functor (B (Group-on.underlying-monoid (G .snd) .snd)) C
  Action→functor {X = X} A .F₀ _ = X
  Action→functor A .F₁ e = A .fst e .C.to
  Action→functor A .F-id = ap C.to (Group-hom.pres-id (A .snd))
  Action→functor A .F-∘ f g = ap C.to (Group-hom.pres-⋆ (A .snd) _ _)
```
