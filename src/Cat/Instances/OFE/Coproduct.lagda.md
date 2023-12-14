<!--
```agda
open import Cat.Displayed.Univalence.Thin
open import Cat.Diagram.Coproduct
open import Cat.Displayed.Total
open import Cat.Instances.OFE
open import Cat.Prelude

open import Data.Sum.Base
```
-->

```agda
module Cat.Instances.OFE.Coproduct where
```

# Coproducts of OFEs

The [category of OFEs][OFE] admits binary [coproducts]. Unlike the
[construction of products][ofe-prod], in which we could define the
approximations $(a, b) \within{n} (a', b')$ by lifting those of the
factor OFEs, the definition of coproducts requires a fair bit more
busywork.

[OFE]: Cat.Instances.OFE.html
[coproducts]: Cat.Diagram.Coproduct.html
[ofe-prod]: Cat.Instances.OFE.Product.html



<!--
```agda
open OFE-Notation

module _ {ℓa ℓb ℓa' ℓb'} {A : Type ℓa} {B : Type ℓb} (O : OFE-on ℓa' A) (P : OFE-on ℓb' B)
  where
  private
    instance
      _ = O
      _ = P
    module O = OFE-on O
    module P = OFE-on P
    open OFE-H-Level O
    open OFE-H-Level P
```
-->

To get it right, let's use the computational interpretation of OFEs.
Having done no steps of computation, we have not yet managed to
distinguish the left summand from the right summand. Motivated by this,
and to satisfy the boundedness axiom, we simply define $x \within{0} y$
to be the unit type everywhere.

Having taken some positive number of steps, it is possible to
distinguish the summands, and we must do so, defining the relations by
cases. The relations $\rm{in}_d(x) \within{1+n} \rm{in}_d(y)$, where $d
\in {l,r}$ ranges over the coproduct injections, are defined to be $x
\within{1+n} y$. Note the index: we do not want to take a step back! In
case the summands are mismatched, e.g. $\rm{inr}(x) \within{1+n}
\rm{inl}(y)$, we give back the bottom type: we have taken enough steps
that it is impossible for them to be equal.

```agda
  ⊎-OFE : OFE-on (ℓa' ⊔ ℓb') (A ⊎ B)
  ⊎-OFE .within zero p q = Lift (ℓa' ⊔ ℓb') ⊤
  ⊎-OFE .within (suc n) (inl x) (inl y) = Lift ℓb' (x ≈[ suc n ] y)
  ⊎-OFE .within (suc n) (inr x) (inr y) = Lift ℓa' (x ≈[ suc n ] y)
  ⊎-OFE .within (suc n) (inl x) (inr y) = Lift (ℓa' ⊔ ℓb') ⊥
  ⊎-OFE .within (suc n) (inr x) (inl y) = Lift (ℓa' ⊔ ℓb') ⊥
```

The proofs of all the axioms will have to make the same case
distinctions to get at a concrete type for the approximations. Let's see
it for reflexivity:

- We first distinguish on the number of steps. If we've not taken any
  yet, then our relation is trivial, and we can (have to!) give back its
  trivial point.

- Having taken a number of steps, we distinguish on the summand. Having
  exposed the underlying relation, we can lift its proof of reflexivity to
  the sum.

```agda
  ⊎-OFE .has-is-ofe .≈-refl zero            = lift tt
  ⊎-OFE .has-is-ofe .≈-refl (suc n) {inl _} = lift (O.≈-refl (suc n))
  ⊎-OFE .has-is-ofe .≈-refl (suc n) {inr _} = lift (P.≈-refl (suc n))
```

<details>
<summary>The other fields are essentially the same, so there's not a lot
to write about.</summary>

```agda
  ⊎-OFE .has-is-ofe .has-is-prop zero x y _ _ = refl
  ⊎-OFE .has-is-ofe .has-is-prop (suc n) (inl _) (inl _) = hlevel!
  ⊎-OFE .has-is-ofe .has-is-prop (suc n) (inr _) (inr _) = hlevel!

  ⊎-OFE .has-is-ofe .≈-sym zero p = lift tt
  ⊎-OFE .has-is-ofe .≈-sym (suc n) {inl _} {inl _} p = lift (O.≈-sym _ (p .Lift.lower))
  ⊎-OFE .has-is-ofe .≈-sym (suc n) {inr _} {inr _} p = lift (P.≈-sym _ (p .Lift.lower))

  ⊎-OFE .has-is-ofe .≈-trans zero p q = lift tt
  ⊎-OFE .has-is-ofe .≈-trans (suc n) {inl _} {inl _} {inl _} p q = lift (O.≈-trans _ (p .Lift.lower) (q .Lift.lower))
  ⊎-OFE .has-is-ofe .≈-trans (suc n) {inr _} {inr _} {inr _} p q = lift (P.≈-trans _ (p .Lift.lower) (q .Lift.lower))

  ⊎-OFE .has-is-ofe .bounded a b  = lift tt
  ⊎-OFE .has-is-ofe .step zero _ _ p = lift tt
  ⊎-OFE .has-is-ofe .step (suc n) (inl x) (inl y) p = lift (O.step _ x y (p .Lift.lower))
  ⊎-OFE .has-is-ofe .step (suc n) (inr x) (inr y) p = lift (P.step _ x y (p .Lift.lower))
```

This minor quibble might be of note to the reader curious enough to
expand this note: To prove that our approximations converge, we _also_
need a case distinction. At the zeroth entry, we appeal to boundedness
of the summand OFEs to get a witness of $x \within{0} y$, since
$\rm{inr}(x) \within{0} \rm{inr}(y)$ is uninformative.

```agda
  ⊎-OFE .has-is-ofe .limit (inl x) (inl y) f = ap inl (O.limit x y f') where
    f' : ∀ n → O.within n x y
    f' zero    = O.bounded x y
    f' (suc n) = f (suc n) .Lift.lower
  ⊎-OFE .has-is-ofe .limit (inr x) (inr y) f = ap inr (P.limit x y f') where
    f' : ∀ n → P.within n x y
    f' zero    = P.bounded x y
    f' (suc n) = f (suc n) .Lift.lower
  ⊎-OFE .has-is-ofe .limit (inl x) (inr y) f = absurd (f 1 .Lift.lower)
  ⊎-OFE .has-is-ofe .limit (inr x) (inl y) f = absurd (f 1 .Lift.lower)
```

</details>

<!--
```agda
open Coproduct
open is-coproduct
open Total-hom
```
-->

We now prove that this construction, which despite my best efforts may
still feel unmotivated, _is_ the categorical product in OFEs. We start
by defining the coproduct of morphisms, the operation taking $f : A \to
Q$ and $g : B \to Q$ to $[f,g] : A \uplus B \to Q$. Once again, it's a
case bash, and we have to use boundedness of the codomain when showing
that points with distance 1 stay with distance 1.

```agda
OFE-Coproduct : ∀ {ℓ ℓ'} A B → Coproduct (OFEs ℓ ℓ') A B
OFE-Coproduct A B = mk where
  module A = OFE-on (A .snd)
  module B = OFE-on (B .snd)

  it = from-ofe-on (⊎-OFE (A .snd) (B .snd))

  disj : ∀ {Q} → OFEs.Hom A Q → OFEs.Hom B Q → OFEs.Hom it Q
  disj f g .hom (inl x) = f # x
  disj f g .hom (inr x) = g # x
  disj {Q = Q} f g .preserves .pres-≈ {n = zero} _ = OFE-on.bounded (Q .snd) _ _
  disj f g .preserves .pres-≈ {inl x} {inl y} {suc n} (lift α) =
    f .preserves .pres-≈ α
  disj f g .preserves .pres-≈ {inr x} {inr y} {suc n} (lift α) =
    g .preserves .pres-≈ α
```

We can then define the coprojections: since we must now produce an
approximation _in_ the sum, if our points have distance 1, we can
produce a trivial datum.

```agda
  in0 : OFEs.Hom A it
  in0 .hom = inl
  in0 .preserves .pres-≈ {n = zero}  _ = lift tt
  in0 .preserves .pres-≈ {n = suc n} α = lift α

  in1 : OFEs.Hom B it
  in1 .hom = inr
  in1 .preserves .pres-≈ {n = zero}  _ = lift tt
  in1 .preserves .pres-≈ {n = suc n} α = lift α
```

It suffices to show that all the relevant diagrams in the definition of
a coproduct actually commute, and that the coproduct of morphisms is
unique: but it suffices to reason at the level of sets.

```agda
  mk : Coproduct (OFEs _ _) A B
  mk .coapex = it
  mk .in₀ = in0
  mk .in₁ = in1
  mk .has-is-coproduct .is-coproduct.[_,_] {Q = Q} f g = disj f g
  mk .has-is-coproduct .in₀∘factor = trivial!
  mk .has-is-coproduct .in₁∘factor = trivial!
  mk .has-is-coproduct .unique other p q = Homomorphism-path λ where
    (inl x) → p #ₚ x
    (inr x) → q #ₚ x
```
