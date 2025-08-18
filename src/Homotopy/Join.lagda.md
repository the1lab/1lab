<!--
```agda
open import 1Lab.Prelude

open import Data.Bool

open import Homotopy.Space.Suspension
open import Homotopy.Pushout
```
-->

```agda
module Homotopy.Join where
```

# The join of types {defines="join-of-types"}

<!--
```agda
private variable
  ℓ ℓ' : Level
  A B C X Y Z : Type ℓ
```
-->

The **join** of two types $A$ and $B$, written $A \join B$ is the pushout
under the diagram $$A \ot (A \times B) \to B$$.

```agda
_∗_ : Type ℓ → Type ℓ' → Type (ℓ ⊔ ℓ')
A ∗ B = Pushout (A × B) fst snd

infixr 30 _∗_

pattern join x y i = glue (x , y) i
```

<!--
```agda
open Homotopy.Pushout using (inl ; inr) public
```
-->

<details>
<summary>
We show that the join operation is associative by a direct cubical
computation due to Loïc Pujet. A more conceptual proof is given in
[@HoTT, lemma 8.5.9].

```agda
join-associative : (X ∗ Y) ∗ Z ≃ X ∗ (Y ∗ Z)
```
</summary>

```agda
join-associative .fst (inl (inl x)) = inl x
join-associative .fst (inl (inr y)) = inr (inl y)
join-associative .fst (inl (join x y i)) = join x (inl y) i
join-associative .fst (inr z) = inr (inr z)
join-associative .fst (join (inl x) z i) = join x (inr z) i
join-associative .fst (join (inr y) z i) = inr (join y z i)
join-associative .fst (join (join x y i) z j) =
  hcomp (∂ i ∨ ∂ j) λ where
    k (k = i0) → join x (join y z j) i
    k (i = i0) → join x (inr z) (j ∧ k)
    k (i = i1) → inr (join y z j)
    k (j = i0) → join x (inl y) i
    k (j = i1) → join x (inr z) (i ∨ k)

join-associative {X = X} {Y = Y} {Z = Z} .snd = is-iso→is-equiv λ where
  .is-iso.from (inl x) → inl (inl x)
  .is-iso.from (inr (inl y)) → inl (inr y)
  .is-iso.from (inr (inr z)) → inr z
  .is-iso.from (inr (join y z i)) → join (inr y) z i
  .is-iso.from (join x (inl y) i) → inl (join x y i)
  .is-iso.from (join x (inr z) i) → join (inl x) z i
  .is-iso.from (join x (join y z j) i) →
    hcomp (∂ i ∨ ∂ j) λ where
      k (k = i0) → join (join x y i) z j
      k (i = i0) → join (inl x) z (j ∧ ~ k)
      k (i = i1) → join (inr y) z j
      k (j = i0) → inl (join x y i)
      k (j = i1) → join (inl x) z (i ∨ ~ k)

  .is-iso.rinv (inl x) → refl
  .is-iso.rinv (inr (inl y)) → refl
  .is-iso.rinv (inr (inr z)) → refl
  .is-iso.rinv (inr (join y z i)) → refl
  .is-iso.rinv (join x (inl y) i) → refl
  .is-iso.rinv (join x (inr z) i) → refl
  .is-iso.rinv (join x (join y z j) i) l →
    comp (λ _ → X ∗ (Y ∗ Z)) (∂ i ∨ ∂ j ∨ l) λ where
      k (k = i0) → hcomp (∂ i ∨ ∂ j ∨ l) λ where
        k (k = i0) → join x (join y z j) i
        k (i = i0) → join x (inr z) (j ∧ (k ∧ ~ l))
        k (i = i1) → inr (join y z j)
        k (j = i0) → join x (inl y) i
        k (j = i1) → join x (inr z) (i ∨ (k ∧ ~ l))
        k (l = i1) → join x (join y z j) i
      k (i = i0) → join x (inr z) (j ∧ (~ k ∧ ~ l))
      k (i = i1) → inr (join y z j)
      k (j = i0) → join x (inl y) i
      k (j = i1) → join x (inr z) (i ∨ (~ k ∧ ~ l))
      k (l = i1) → join x (join y z j) i

  .is-iso.linv (inl (inl x)) → refl
  .is-iso.linv (inl (inr y)) → refl
  .is-iso.linv (inl (join x y i)) → refl
  .is-iso.linv (inr z) → refl
  .is-iso.linv (join (inl x) z i) → refl
  .is-iso.linv (join (inr y) z i) → refl
  .is-iso.linv (join (join x y i) z j) l →
    comp (λ _ → (X ∗ Y) ∗ Z) (∂ i ∨ ∂ j ∨ l) λ where
      k (k = i0) → hcomp (∂ i ∨ ∂ j ∨ l) λ where
        k (k = i0) → join (join x y i) z j
        k (i = i0) → join (inl x) z (j ∧ (~ k ∨ l))
        k (i = i1) → join (inr y) z j
        k (j = i0) → inl (join x y i)
        k (j = i1) → join (inl x) z (i ∨ (~ k ∨ l))
        k (l = i1) → join (join x y i) z j
      k (i = i0) → join (inl x) z (j ∧ (k ∨ l))
      k (i = i1) → join (inr y) z j
      k (j = i0) → inl (join x y i)
      k (j = i1) → join (inl x) z (i ∨ (k ∨ l))
      k (l = i1) → join (join x y i) z j
```
</details>

The join operation is also commutative; luckily, this is much more
straightforward.

```agda
join-swap : X ∗ Y → Y ∗ X
join-swap (inl x) = inr x
join-swap (inr x) = inl x
join-swap (join a b i) = join b a (~ i)

join-commutative : X ∗ Y ≃ Y ∗ X
join-commutative .fst = join-swap
join-commutative .snd = is-iso→is-equiv record where
  from = join-swap
  rinv = Pushout-elim (λ _ → refl) (λ _ → refl) λ c i j → glue c i
  linv = Pushout-elim (λ _ → refl) (λ _ → refl) λ c i j → glue c i
```

Finally, if either of the joined types is contractible, so is the join.
```agda
join-is-contr-l : is-contr X → is-contr (X ∗ Y)
join-is-contr-l h .centre = inl (centre h)
join-is-contr-l h .paths (inl x) = ap inl (paths h x)
join-is-contr-l h .paths (inr y) = join (centre h) y
join-is-contr-l h .paths (join x y i) j = hcomp (∂ i ∨ ∂ j) λ where
  k (k = i0) → join x y (i ∧ j)
  k (i = i0) → inl (paths h x (~ k ∨ j))
  k (i = i1) → join (paths h x (~ k)) y j
  k (j = i0) → inl (paths h x (~ k))
  k (j = i1) → join x y i

join-is-contr-r : is-contr Y → is-contr (X ∗ Y)
join-is-contr-r h .centre = inr (centre h)
join-is-contr-r h .paths (inl x) = sym (join x (centre h))
join-is-contr-r h .paths (inr y) = ap inr (paths h y)
join-is-contr-r h .paths (join x y i) j = hcomp (∂ i ∨ ∂ j) λ where
  k (k = i0) → join x y (i ∨ ~ j)
  k (i = i0) → join x (paths h y (~ k)) (~ j)
  k (i = i1) → inr (paths h y (~ k ∨ j))
  k (j = i0) → inr (paths h y (~ k))
  k (j = i1) → join x y i
```

<!--
```agda
join-map : (A → B) → (X → Y) → A ∗ X → B ∗ Y
join-map f g (inl x) = inl (f x)
join-map f g (inr x) = inr (g x)
join-map f g (join a b i) = join (f a) (g b) i

join-ap : (A ≃ B) → (X ≃ Y) → A ∗ X ≃ B ∗ Y
join-ap f g .fst = join-map (f .fst) (g .fst)
join-ap f g .snd = is-iso→is-equiv record where
  from = join-map (Equiv.from f) (Equiv.from g)
  rinv = Pushout-elim (λ b → ap inl (Equiv.ε f b)) (λ y → ap inr (Equiv.ε g y))
      λ (b , y) i j → join (Equiv.ε f b j) (Equiv.ε g y j) i
  linv = Pushout-elim (λ a → ap inl (Equiv.η f a)) (λ x → ap inr (Equiv.η g x))
      λ (a , x) i j → join (Equiv.η f a j) (Equiv.η g x j) i
```
-->

## Suspensions as joins

The [[suspension]] of $A$ is equivalently the join of $A$ with the
[[booleans]]: the two booleans correspond to the poles, and the
meridian passing through $a$ corresponds to the composite path
$\mathrm{true} \is a \is \mathrm{false}$. Notice that the map $2 \join A
\to \Susp A$ sends every $a : A$ to the south pole. This is arbitrary,
and we could just as well have chosen the north pole; all the information
lives in the meridians.

```agda
2∗≡Susp : Bool ∗ A ≃ Susp A
2∗≡Susp .fst (inl true)  = north
2∗≡Susp .fst (inl false) = south
2∗≡Susp .fst (inr x) = south
2∗≡Susp .fst (join true  a i) = merid a i
2∗≡Susp .fst (join false _ i) = south

2∗≡Susp .snd = is-iso→is-equiv record where
  from = Susp-elim _ (inl true) (inl false) λ a → join true a ∙ sym (join false a)
  rinv = Susp-elim _ refl refl λ a →
    transpose (ap-∙ (2∗≡Susp .fst) (join true a) (sym (join false a)) ∙ ∙-idr _)
  linv = Pushout-elim
    (λ { true → refl
        ; false → refl })
    (λ a → join false a)
    λ { (true , a) → transpose (flip₁ (∙-filler _ _))
      ; (false , a) i j → join false a (i ∧ j) }
```

## Joins of propositions {defines="disjunction logical-or"}

When applied to propositions, the join construction
acts as logical disjunction. If `X` and `Y` are propositions,
then `X ∗ Y` is also a proposition, which holds iff
either `X` or `Y` does.

```agda
join-elim-prop : {P : X ∗ Y → Type ℓ} (pprop : ∀ x → is-prop (P x))
  → (f : ∀ x → P (inl x)) (g : ∀ y → P (inr y))
  → ∀ x → P x
join-elim-prop h f g =
  Pushout-elim f g λ c → is-prop→pathp (λ i → h (glue c i)) _ _

join-is-prop : is-prop X → is-prop Y → is-prop (X ∗ Y)
join-is-prop {X = X} {Y = Y} hx hy = λ x y → go x x y where
  go : X ∗ Y → is-prop (X ∗ Y)
  go = join-elim-prop
    (λ _ → is-prop-is-prop)
    (λ x → is-contr→is-prop (join-is-contr-l (is-prop∙→is-contr hx x)))
    (λ y → is-contr→is-prop (join-is-contr-r (is-prop∙→is-contr hy y)))
```
