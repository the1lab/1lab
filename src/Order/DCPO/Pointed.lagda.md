<!--
```agda
open import Data.Maybe.Base

open import Cat.Displayed.Total
open import Cat.Prelude

open import Order.Base
open import Order.DCPO

import Order.DCPO.Reasoning as DCPO
import Data.Nat as Nat
```
-->

```agda
module Order.DCPO.Pointed where
```

<!--
```agda
open Total-hom
```
-->

# Pointed DCPOs

A [DCPO] is **pointed** if it has a least element $\bot$.

[DCPO]: Order.DCPO.html

```agda
is-pointed-dcpo : ∀ {o ℓ} → DCPO o ℓ → Type _
is-pointed-dcpo D = DCPO.Bottom D
```

A DCPO is pointed if and only if it has least upper bounds of all
semidirected families.

<!--
```agda
module _ {o ℓ} (D : DCPO o ℓ) where
  open DCPO D
```
-->

The forward direction is straightforward: bottom elements are equivalent
to least upper bounds of the empty family $\bot \to D$, and this family
is trivially semidirected.

```agda
  semidirected-lub→pointed
    : (∀ {Ix : Type o} (s : Ix → Ob) → is-semidirected-family poset s → Lub s)
    → is-pointed-dcpo D
  semidirected-lub→pointed lub =
    Lub→Bottom (lower-lub (lub (absurd ⊙ Lift.lower) (absurd ⊙ Lift.lower)))
```

Conversely, if $D$ has a bottom element $\bot$, then we can extend any semidirected
family $I \to D$ to a directed family $\rm{Maybe}(I) \to D$ by sending `nothing`
to the bottom element. This directed family has a least upper bound which is also
a least upper bound for our original family.

```agda
  pointed→semidirected-lub
    : is-pointed-dcpo D
    → (∀ {Ix : Type o} (s : Ix → Ob) → is-semidirected-family poset s → Lub s)
  pointed→semidirected-lub pointed {Ix = Ix} s semidir = s-lub where
    open Bottom pointed

    s' : Maybe Ix → Ob
    s' (just ix) = s ix
    s' nothing = bot

    dir : is-directed-family poset s'
    dir .is-directed-family.elt = inc nothing
    dir .is-directed-family.semidirected (just i) (just j) = do
      (k , i≤k , j≤k) ← semidir i j
      pure (just k , i≤k , j≤k)
    dir .is-directed-family.semidirected (just x) nothing =
      pure (just x , ≤-refl , ¡)
    dir .is-directed-family.semidirected nothing (just y) =
      pure (just y , ¡ , ≤-refl)
    dir .is-directed-family.semidirected nothing nothing =
     pure (nothing , ≤-refl , ≤-refl)

    s-lub : Lub s
    s-lub .Lub.lub = ⋃ s' dir
    s-lub .Lub.has-lub .is-lub.fam≤lub ix = ⋃.fam≤lub s' dir (just ix)
    s-lub .Lub.has-lub .is-lub.least ub′ le = ⋃.least s' dir ub′ λ where
      (just ix) → le ix
      nothing → ¡
```

## Fixpoints

Let $D$ be a pointed DCPO. Every Scott continuous function $f : D \to D$ has a
[least fixed point].

[least fixed point]: Order.Diagram.Fixpoint.html

```agda
module _ {o ℓ} {D : DCPO o ℓ} where
  open DCPO D

  pointed→least-fixpoint
    : is-pointed-dcpo D
    → (f : DCPOs.Hom D D)
    → Least-fixpoint f
  pointed→least-fixpoint pointed f = f-fix where
    open Bottom pointed
```

We begin by constructing a directed family $\NN \to D$ that maps $n$ to
$f^n(\bot)$.

```
    fⁿ : Nat → Ob → Ob
    fⁿ zero x = x 
    fⁿ (suc n) x = f .hom (fⁿ n x)

    fⁿ-mono : ∀ {i j} → i Nat.≤ j → fⁿ i bot ≤ fⁿ j bot
    fⁿ-mono Nat.0≤x = ¡
    fⁿ-mono (Nat.s≤s p) = scott→monotone (f .preserves) _ _ (fⁿ-mono p)

    fⁿ⊥ : Lift o Nat → Ob
    fⁿ⊥ (lift n) = fⁿ n bot

    fⁿ⊥-dir : is-directed-family poset fⁿ⊥
    fⁿ⊥-dir .is-directed-family.elt = inc (lift zero)
    fⁿ⊥-dir .is-directed-family.semidirected (lift i) (lift j) =
      inc (lift (Nat.max i j) , fⁿ-mono (Nat.max-≤l i j) , fⁿ-mono (Nat.max-≤r i j))
```

The least upper bound of this sequence shall be our least fixpoint. We
begin by proving a slightly stronger variation of the universal property;
namely for any $y$ such that $f y \le y$, $\bigcup (f^{n}(\bot)) \le y$.
This follows from som quick induction.

```agda
    fⁿ⊥≤fix : ∀ (y : Ob) → f .hom y ≤ y → ∀ n → fⁿ⊥ n ≤ y
    fⁿ⊥≤fix y p (lift zero) = ¡
    fⁿ⊥≤fix y p (lift (suc n)) =
      f .hom (fⁿ n bot) ≤⟨ scott→monotone (f .preserves) _ _ (fⁿ⊥≤fix y p (lift n)) ⟩
      f .hom y          ≤⟨ p ⟩
      y                 ≤∎

    least-fix : ∀ (y : Ob) → f .hom y ≤ y → ⋃ fⁿ⊥ fⁿ⊥-dir ≤ y
    least-fix y p = ⋃.least _ _ _ (fⁿ⊥≤fix y p)
```

Now, let's show that $\bigcup (f^{n}(\bot))$ is actuall a fixpoint.
First, the forward direction: $\bigcup (f^{n}(\bot)) \le f (\bigcup (f^{n}(\bot)))$.
This follows directly from Scott-continuity of $f$.

```agda
    roll : f .hom (⋃ fⁿ⊥ fⁿ⊥-dir) ≤ ⋃ fⁿ⊥ fⁿ⊥-dir
    roll =
      f .hom (⋃ fⁿ⊥ _)    =⟨ scott-⋃ (f .preserves) _ _ ⟩
      ⋃ (f .hom ⊙ fⁿ⊥) _  ≤⟨ ⋃.least _ _ _ (λ (lift n) → ⋃.fam≤lub _ _ (lift (suc n))) ⟩
      ⋃ fⁿ⊥ _             ≤∎
```

To show the converse, we use universal property we proved earlier to
re-arrange the goal to $f (f (\bigcup (f^{n}(\bot)))) \le f (\bigcup (f^{n}(\bot)))$.
We can then apply monotonicity of $f$, and then use the forward direction
to finish off the proof.

```agda
    unroll : ⋃ fⁿ⊥ fⁿ⊥-dir ≤ f .hom (⋃ fⁿ⊥ fⁿ⊥-dir)
    unroll = least-fix (f .hom (⋃ fⁿ⊥ fⁿ⊥-dir)) $
      scott→monotone (f .preserves) _ _ roll
```

All that remains is to package up the data.

```agda
    f-fix : Least-fixpoint f
    f-fix .fixpoint = ⋃ fⁿ⊥ fⁿ⊥-dir
    f-fix .has-least-fixpoint .DCPO.fixed = ≤-antisym roll unroll
    f-fix .has-least-fixpoint .DCPO.least y y-fix =
      least-fix y (path→≤ y-fix)
```
