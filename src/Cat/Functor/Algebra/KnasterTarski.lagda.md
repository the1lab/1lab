---
description: |
  The Knaster-Tarski theorem for categories.
---
<!--
```agda
open import Cat.Functor.Algebra.Limits
open import Cat.Diagram.Initial.Weak
open import Cat.Diagram.Limit.Base
open import Cat.Diagram.Initial
open import Cat.Displayed.Total
open import Cat.Functor.Algebra
open import Cat.Prelude

open import Order.Diagram.Fixpoint
open import Order.Diagram.Glb
open import Order.Base
open import Order.Cat

import Cat.Reasoning
```
-->
```agda
module Cat.Functor.Algebra.KnasterTarski where
```

# The Knaster-Tarski fixpoint theorem {defines="knaster-tarski"}

The **Knaster-Tarski theorem** gives a recipe for constructing [[initial]]
[[F-algebras]] in [[complete categories]].

The big idea is that if a category $\cC$ is complete, then we can construct
an initial algebra of a functor $F$ by taking a limit $\rm{Fix}$ over the forgetful
functor $\pi : \FAlg{F} \to \cC$ from the category of $F$-algebras:
the universal property of such a limit let us construct an algebra
$F(\rm{Fix}) \to \rm{Fix}$, and the projections out of $\rm{Fix}$ let
us establish that $\rm{Fix}$ is the initial algebra.

Unfortunately, this limit is a bit too ambitious. If we examine the universe
levels involved, we will quickly notice that this argument requires $\cC$
to admit limits indexed by the \emph{objects} of $\cC$, which in the presence
of excluded middle means that $\cC$ must be a preorder.

This problem of overly ambitious limits is similar to the one encountered
in the naïve [[adjoint functor theorem]], so we can use a similar technique
to repair our proof. In particular, we will impose a variant of the
**solution set condition** on the category of $F$-algebras that ensures
that the limit we end up computing is determined by a small amount of data,
which lets us relax our large-completeness requirement.

More precisely, we will require that the category of $F$-algebras has a
small [[weakly initial family]] of algebras. This means that we need:

- A family $\alpha_i : F(A_i) \to A_i$ of $F$ algebras indexed by a
  small set $I$, such that;
- For every $F$-algebra $\beta : F(B) \to B$, there (merely) exists an $i : I$
  along with a $F$-algebra morphism $A_i \to B$.

<!--
```agda
module _
  {o ℓ} {C : Precategory o ℓ}
  (F : Functor C C)
  where
  open Cat.Reasoning C
  open Functor F
  open Total-hom
```
-->

Once we have a solution set, the theorem pops open like a walnut submerged
in water:

* First, $\cC$ is small-complete, so the category of $F$-algebras must also
  be small-complete, as [[limits of $F$-algebras]] are computed by limits
  in $\cC$.
* In particular, the category of $F$-algebras has all small [[equalisers]],
  so we can upgrade our weakly initial family to an [[initial object]].

```agda
  solution-set→initial-algebra
    : ∀ {κ} {Idx : Type κ} ⦃ _ : ∀ {n} → H-Level Idx (2 + n) ⦄
    → (Aᵢ : Idx → FAlg.Ob F)
    → is-complete κ (ℓ ⊔ κ) C
    → is-weak-initial-fam (FAlg F) Aᵢ
    → Initial (FAlg F)
  solution-set→initial-algebra Aᵢ complete soln-set =
    is-complete-weak-initial→initial (FAlg F)
      Aᵢ
      (FAlg-is-complete complete F)
      soln-set
```

We can obtain the more familiar form of the Knaster-Tarski theorem by
applying [[Lambek's lemma]] to the resulting initial algebra.

```agda
  solution-set→fixpoint
    : ∀ {κ} {Idx : Type κ} ⦃ _ : ∀ {n} → H-Level Idx (2 + n) ⦄
    → (Aᵢ : Idx → FAlg.Ob F)
    → is-complete κ (ℓ ⊔ κ) C
    → is-weak-initial-fam (FAlg F) Aᵢ
    → Σ[ Fix ∈ Ob ] (F₀ Fix ≅ Fix)
  solution-set→fixpoint Aᵢ complete soln-set =
    bot .fst , invertible→iso (bot .snd) (lambek F (bot .snd) has⊥)
    where open Initial (solution-set→initial-algebra Aᵢ complete soln-set)
```

## Knaster-Tarski for sup-lattices

<!--
```agda
module _
  {o ℓ} (P : Poset o ℓ)
  (f : Monotone P P)
  where
  open Poset P
  open Total-hom
```
-->

The "traditional" Knaster-Tarski theorem states that every [[monotone endomap|monotone-map]]
on a [[poset]] $P$ with all [[greatest lower bounds]] has a [[least fixpoint]].
In the presence of [[propositional resizing]], this theorem follows as a corollary of
our previous theorem.

```agda
  complete→least-fixpoint
    : (∀ {I : Type o} → (k : I → Ob) → Glb P k)
    → Least-fixpoint P f
  complete→least-fixpoint glbs = least-fixpoint where
```

<!--
```agda
    open Cat.Reasoning (poset→category P) using (_≅_; to; from)
    open is-least-fixpoint
    open Least-fixpoint
```
-->

The key is that resizing lets us prove the solution set condition with
respect to the size of the underlying set of $P$, as we can resize away
the proofs that $f x \leq x$.

```agda
    Idx : Type o
    Idx = Σ[ x ∈ Ob ] (□ (f · x ≤ x))

    soln : Idx → Σ[ x ∈ Ob ] (f · x ≤ x)
    soln (x , lt) = x , (□-out! lt)

    is-soln-set : is-weak-initial-fam (FAlg (monotone→functor f)) soln
    is-soln-set (x , lt) = inc ((x , inc lt) , total-hom ≤-refl prop!)
```

Moreover, $P$ has all [[greatest lower bounds]], so it is `complete as a
category`{.Agda ident=glbs→complete}. This lets us invoke the general
Knaster-Tarski theorem to get an initial $f$-algebra.

```agda
    initial : Initial (FAlg (monotone→functor f))
    initial =
      solution-set→initial-algebra (monotone→functor f)
        soln
        (glbs→complete glbs)
        is-soln-set
```

Finally, we can inline the proof of [[Lambek's lemma]] to show that this
initial algebra gives the least fixpoint of $f$!

```agda
    open Initial initial

    least-fixpoint : Least-fixpoint P f
    least-fixpoint .fixpoint =
      bot .fst
    least-fixpoint .has-least-fixpoint .fixed =
      ≤-antisym
        (bot .snd)
        (¡ {x = f .hom (bot .fst) , f .pres-≤ (bot .snd)} .hom)
    least-fixpoint .has-least-fixpoint .least x fx=x =
      ¡ {x = x , ≤-refl' fx=x} .hom
```
