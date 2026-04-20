<!--
```agda
open import Algebra.Group.Cat.FinitelyComplete
open import Algebra.Group.Cat.Base
open import Algebra.Group.Solver
open import Algebra.Group

open import Cat.Instances.Delooping
open import Cat.Instances.Functor
open import Cat.Displayed.Total
open import Cat.Displayed.Thin
open import Cat.Instances.Sets
open import Cat.Diagram.Zero
open import Cat.Prelude

import Cat.Functor.Reasoning as Functor-kit
import Cat.Reasoning as Cat
```
-->

```agda
module Algebra.Group.Action where
```

<!--
```agda
open is-group-hom
open Functor
```
-->

# Group actions {defines="group-action"}

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
a \mapsto e^{ix}a
$$,

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
equivalently a [[group homomorphism]]

$$
\bb{R} \to \rm{Sym}(\bb{C})
$$,

where the codomain is the [[group of symmetries|symmetric group]] of $\bb{C}$. But what if
we want a group $G$ to act on an object $X$ of a more general
[[category]], rather than an object of $\Sets$?

## Automorphism groups {defines="automorphism-group"}

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
    mg .make-group.group-is-set = hlevel 2
    mg .make-group.unit = C.id-iso
    mg .make-group.mul f g = g C.∘Iso f
    mg .make-group.inv = C._Iso⁻¹
    mg .make-group.assoc x y z = ext (sym (C.assoc _ _ _))
    mg .make-group.invl x = ext (x .C.invl)
    mg .make-group.idl x = ext (C.idr _)
```

Suppose we have a category $\cC$, an object $X : \cC$, and a group
$G$; A **$G$-action on $X$** is a group homomorphism $G \to
\rm{Aut}(X)$.

```agda
  Action : Group ℓ → C.Ob → Type _
  Action G X = Groups.Hom G (Aut X)
```

::: note
Since we've defined $f \star g = g \circ f$ in the automorphism group,
our definition corresponds to *right* actions. If we had defined
$f \star g = f \circ g$ instead, we would get *left* actions.
Of course, the two definitions are formally dual, so it does not
really matter.
:::

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
    Functor→action F .fst it = C.make-iso
        (F .F₁ it) (F .F₁ (it ⁻¹))
        (F.annihilate inversel) (F.annihilate inverser)
      where
        open Group-on (G .snd)
        module F = Functor-kit F
    Functor→action F .snd .is-group-hom.pres-⋆ x y = ext (F .F-∘ _ _)

    Action→functor : {X : C.Ob} (A : Action G X) → Functor BG C
    Action→functor {X = X} A .F₀ _ = X
    Action→functor A .F₁ e = (A · e) .C.to
    Action→functor A .F-id = ap C.to (is-group-hom.pres-id (A .snd))
    Action→functor A .F-∘ f g = ap C.to (is-group-hom.pres-⋆ (A .snd) _ _)
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
      .is-iso.from (x , act) → Action→functor act
      .is-iso.linv x → Functor-path (λ _ → refl) λ _ → refl
      .is-iso.rinv x → Σ-pathp refl $
        ∫Hom-pathp _ _ _ (funext (λ i → C.≅-pathp _ _ refl))
          (is-prop→pathp (λ i → is-group-hom-is-prop) _ _)
```

# Examples of actions

:::{.definition #trivial-action}
For any group $G$, category $\cC$ and object $X : \cC$, we have the
**trivial action** of $G$ on $X$ which maps every element to the
identity automorphism. It can be defined simply as the [[zero morphism]]
$G \to \rm{Aut}(X)$.
:::

```agda
module _ {o ℓ} {C : Precategory o ℓ} (G : Group ℓ) where
  trivial-action : ∀ X → Action C G X
  trivial-action X = Zero.zero→ ∅ᴳ
```

:::{.definition #principal-action}
Any group $G$ acts on itself on the right in two ways: first, $G$ acts on its
underlying set by multiplication on the right. This is sometimes called
the **principal action** or the **(right-)regular action**, and is the
basis for [[Cayley's theorem]].
:::

<!--
```agda
module _ {ℓ} (G : Group ℓ) where
  private module G = Group-on (G .snd)
```
-->

```agda
  principal-action : Action (Sets ℓ) G (G .fst)
  principal-action .fst x = equiv→iso ((G._⋆ x) , G.⋆-equivr x)
  principal-action .snd .pres-⋆ x y = ext λ z → G.associative
```

$G$ also acts on itself *as a group* by **conjugation**. An automorphism
of $G$ that arises from conjugation with an element of $G$ is called an
**inner automorphism**.

```agda
  conjugation-action : Action (Groups ℓ) G G
  conjugation-action .fst x = total-iso
    ((λ y → x G.⁻¹ G.⋆ y G.⋆ x) , ∘-is-equiv (G.⋆-equivl (x G.⁻¹)) (G.⋆-equivr x))
    (record { pres-⋆ = λ y z → group! G })
  conjugation-action .snd .pres-⋆ x y = ext λ z → group! G
```
