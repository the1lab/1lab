```agda
open import 1Lab.HLevel.Sets
open import 1Lab.Type.Dec
open import 1Lab.HLevel
open import 1Lab.Path
open import 1Lab.Type

module Relation.Order where
```

# Order relations

This module characterises different types of binary relations, and, in
particular, ordering relations.

<!--
```
private variable
  ℓ ℓ' : Level
  A : Type ℓ
  R : A → A → Type ℓ'
```
-->

A relation is _reflexive_ if we have `R x x`, for any `x`:

```agda
isReflexive : (R : A → A → Type ℓ) → Type _
isReflexive R = {x : _} → R x x
```

A relation is _transitive_ if `R x y` and `R y z` implies `R x z`.

```agda
isTransitive : (R : A → A → Type ℓ) → Type _
isTransitive R = {x y z : _} → R x y → R y z → R x z
```

A **preorder** is a reflexive, transitive relation. Furthermore, we
impose that a preorder take value in propositions.

```agda
record isPreorder {A : Type ℓ} (R : A → A → Type ℓ') : Type (ℓ ⊔ ℓ') where
  field
    reflexive     : isReflexive R
    transitive    : isTransitive R
    propositional : {x y : A} → isProp (R x y)
```

## Partial Orders

A **partial order** is a preorder which, in addition, is antisymmetric:

```agda
isAntiSymmetric : (R : A → A → Type ℓ) → Type _
isAntiSymmetric R = {x y : _} → R x y → R y x → x ≡ y

record isPartialOrder {A : Type ℓ} (R : A → A → Type ℓ') : Type (ℓ ⊔ ℓ') where
  field
    preorder : isPreorder R
    antisym : isAntiSymmetric R

  open isPreorder preorder public
```

Any type with a choice of partial order is a set. This is because of
`Rijke's theorem`{.Agda ident=Rijke-isSet}: Any type with a reflexive
relation implying equality is a set.

```agda
hasPartialOrder→isSet : {A : Type ℓ} {R : A → A → Type ℓ'}
                      → isPartialOrder R
                      → isSet A
hasPartialOrder→isSet {A = A} {_≤_} ispo =
  Rijke-isSet {R = R'} reflexive' (λ { (x , y) → antisym x y }) isProp'
  where
    open isPartialOrder ispo
```

For the relation, we take $R(x, y) = (x \le y) \land (y \le x)$. By
antisymmetry, this implies $x = y$. Since propositions are closed under
products, this is a proposition.

```agda
    R' : A → A → Type _
    R' x y = (x ≤ y) × (y ≤ x)

    reflexive' : {x : A} → R' x x
    reflexive' = reflexive , reflexive

    isProp' : {x y : A} → isProp (R' x y)
    isProp' (a , b) (a' , b') i = propositional a a' i , propositional b b' i
```

With this theorem, we can prove that being a partial order is a
proposition. We do this by the characterisation of propositions as those
types which are `contractible when inhabited`{.Agda
ident=inhContr→isProp}, since then we're free to assume A is a set.

```agda
isProp-isPartialOrder : {A : Type ℓ} {R : A → A → Type ℓ'}
                      → isProp (isPartialOrder R)
isProp-isPartialOrder {A = A} {R} = inhContr→isProp contract
  where
    open isPartialOrder
    open isPreorder

    contract : isPartialOrder R → isContr (isPartialOrder R)
    contract order = contr order deform where
      A-set : isSet A
      A-set = hasPartialOrder→isSet order
```

For the centre of contraction, we're free to use the given witness.
Since the paths end up being a big product of propositions, most of the
construction follows directly from the fact that `preorders are
propositional`{.Agda ident=propositional}.

```agda
      deform : (x : isPartialOrder R) → order ≡ x
      deform x i .preorder .reflexive =
        x .propositional (order .preorder .reflexive)
                         (x .preorder .reflexive)
                         i
      deform x i .preorder .transitive p q =
        x .propositional (order .preorder .transitive p q)
                         (x .preorder .transitive p q)
                         i
```

To connect the propositionality witnesses, we use the fact that `isProp
is a proposition`{.Agda ident=isProp-isProp}.

```agda
      deform x i .preorder .propositional =
        isProp-isProp (order .preorder .propositional)
                      (x .preorder .propositional)
                      i
```

The construction is finished by relating the antisymmetry witnesses.
Since `A` admits a partial order, and thus is a set, all of its path
spaces are propositions:

```agda
      deform x i .antisym p q = A-set _ _ (order .antisym p q) (x .antisym p q) i
```

## Trichotomous orders

We say a relation is **trichotomous** for all `x,y` if exactly _one_ of
`R x y`, `x ≡ y`, or `R y x` holds.  We define this in two parts: First
we define what trichotomy means for 2 elements via `Tri`, then
`Trichotomous` in terms of `Tri`.

```agda
data Tri {A : Type ℓ} (R : A → A → Type ℓ') (x y : A) : Type (ℓ ⊔ ℓ') where
  lt : R x y       → (x ≡ y → ⊥) → (R y x → ⊥) → Tri R x y
  eq : (R x y → ⊥) → x ≡ y       → (R y x → ⊥) → Tri R x y
  gt : (R x y → ⊥) → (x ≡ y → ⊥) → R y x       → Tri R x y

isTrichotomous : {A : Type ℓ} → (R : A → A → Type ℓ') → Type (ℓ ⊔ ℓ')
isTrichotomous R = ∀ x y → Tri R x y
```

Trichotomy is a very powerful property, and we can derive a lot of useful
results from it!

To start, trichotomy immediately implies discreteness:

```agda
trichotomous-discrete : ∀ {A : Type ℓ} {R : A → A → Type ℓ'}
                      → isTrichotomous R → Discrete A
trichotomous-discrete compare x y with compare x y
... | lt _ ¬x≡y _ = no ¬x≡y
... | eq _  x≡y _ = yes x≡y
... | gt _ ¬x≡y _ = no ¬x≡y
```

These results aren't particularly deep, but are useful nonetheless.
If `x` and `y` are trichotomous with respect to one another, then
we can flip everything around without consequence.

```agda
tri-sym : ∀ {x y} → Tri R x y → Tri R y x
tri-sym (lt  x≺y ¬x≡y ¬y≺x) = gt ¬y≺x (¬x≡y ∘ sym)  x≺y
tri-sym (eq ¬x≺y  x≡y ¬y≺x) = eq ¬y≺x (sym x≡y)    ¬x≺y
tri-sym (gt ¬x≺y ¬x≡y  y≺x) = lt  y≺x (¬x≡y ∘ sym) ¬x≺y
```
