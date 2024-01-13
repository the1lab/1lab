<!--
```agda
open import Algebra.Group.Cat.Base
open import Algebra.Prelude
open import Algebra.Group

open import Cat.Instances.Delooping

import Cat.Functor.Reasoning as Functor-kit
```
-->

```agda
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
but rather the usual definition of the circle as a subset of $\bb{C}$.]
sitting in $\bb{C}$. Given a real number $x : \bb{R}$, we can consider
the "action" on the circle defined by

[groups]: Algebra.Group.html
[$S^1$]: Homotopy.Space.Circle.html

$$
a \mapsto e^{ix}a\text{,}
$$

which "visually" has the effect of rotating the point $a$ so it lands
$x$ radians around the circle, in the counterclockwise direction. Each
$x$-radian rotation has an inverse, given by rotation $x$ radians in the
clockwise direction; but observe that this is the same as rotating $-x$
degrees counterclockwise. Additionally, observe that rotating by zero
radians does nothing to the circle.

We say that $\bb{R}$ _acts_ on the circle by counterclockwise rotation;
What this means is that to each element $x : \bb{R}$, we assign a map
$\bb{C} \to \bb{C}$ in a way _compatible_ with the group structure:
Additive inverses "translate to" inverse maps, addition translates to
function composition, and the additive identity is mapped to the
identity function. Note that since $\bb{C}$ is a set, this is
equivalently a [group homomorphism]

$$
\bb{R} \to \rm{Sym}(\bb{C})\text{,}
$$

where the codomain is the [group of symmetries] of $\bb{C}$. But what if
we want a group $G$ to act on an object $X$ of a more general
[category], rather than an object of $\Sets$?

[group homomorphism]: Algebra.Group.html#group-homomorphisms
[group of symmetries]: Algebra.Group.html#symmetric-groups
[category]: Cat.Base.html

## Automorphism groups

The answer is that, for an object $X$ of some category $\cC$, the
collection of all [isomorphisms] $X \cong X$ forms a group under
composition, generalising the construction of $\rm{Sym}(X)$ to objects
beyond sets! We refer to a "self-isomorphism" as an
**automorphism**, and denote their group by $\rm{Aut}(X)$.

[isomorphisms]: Cat.Morphism.html#isos

```agda
module _ {o ℓ} (C : Precategory o ℓ) where
  private module C = Cat C

  Aut : C.Ob → Group _
  Aut X = to-group mg where
    mg : make-group (X C.≅ X)
    mg .make-group.group-is-set = C.≅-is-set
    mg .make-group.unit = C.id-iso
    mg .make-group.mul g f = g C.∘Iso f
    mg .make-group.inv = C._Iso⁻¹
    mg .make-group.assoc x y z = C.≅-pathp refl refl (sym (C.assoc _ _ _))
    mg .make-group.invl x = C.≅-pathp refl refl (x .C.invl)
    mg .make-group.idl x = C.≅-pathp refl refl (C.idr _)
```

Suppose we have a category $\cC$, an object $X : \cC$, and a group
$G$; A **$G$-action on $X$** is a group homomorphism $G \to
\rm{Aut}(X)$.

```agda
  Action : Group ℓ → C.Ob → Type _
  Action G X = Groups.Hom G (Aut X)
```

# As functors

Recall that we defined the [delooping] of a [monoid] $M$ into a category
as the category $\bf{B}M$ with a single object $\bull$, and $\hom(\bull,
\bull) = M$. If we instead deloop a group $G$ into a group $\bf{B}G$,
then functors $F : \bf{B}G \to \cC$ correspond precisely to actions
of $G$ on the object $F(\bull)$!

[delooping]: Cat.Instances.Delooping.html
[monoid]: Algebra.Monoid.html

<!--
```agda
  module _ {G : Group ℓ} where
    private BG = B (Group-on.underlying-monoid (G .snd) .snd) ^op
```
-->

```agda
    Functor→action : (F : Functor BG C) → Action G (F .F₀ tt)
    Functor→action F .hom it = C.make-iso
        (F .F₁ it) (F .F₁ (it ⁻¹))
        (F.annihilate inversel) (F.annihilate inverser)
      where
        open Group-on (G .snd)
        module F = Functor-kit F
    Functor→action F .preserves .is-group-hom.pres-⋆ x y = C.≅-pathp refl refl (F .F-∘ _ _)

    Action→functor : {X : C.Ob} (A : Action G X) → Functor BG C
    Action→functor {X = X} A .F₀ _ = X
    Action→functor A .F₁ e = (A # e) .C.to
    Action→functor A .F-id = ap C.to (is-group-hom.pres-id (A .preserves))
    Action→functor A .F-∘ f g = ap C.to (is-group-hom.pres-⋆ (A .preserves) _ _)
```

After constructing these functions in either direction, it's easy enough
to show that they are inverse equivalences, but we must be careful about
the codomain: rather than taking "$X$ with a $G$-action" for any
particular $X$, we take the _total space_ of $\cC$-objects equipped
with $G$-actions.

After this small correction, the proof is almost definitional: after
applying the right helpers for pushing paths inwards, we're left with
`refl`{.Agda} at all the leaves.

```agda
    Functor≃action : is-equiv {B = Σ _ (Action G)} λ i → _ , Functor→action i
    Functor≃action = is-iso→is-equiv λ where
      .is-iso.inv (x , act) → Action→functor act
      .is-iso.rinv x → Σ-pathp refl $
        total-hom-pathp _ _ _ (funext (λ i → C.≅-pathp _ _ refl))
          (is-prop→pathp (λ i → is-group-hom-is-prop) _ _)
      .is-iso.linv x → Functor-path (λ _ → refl) λ _ → refl
```
