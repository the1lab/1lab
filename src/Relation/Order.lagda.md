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
is-reflexive : (R : A → A → Type ℓ) → Type _
is-reflexive R = {x : _} → R x x
```

A relation is _transitive_ if `R x y` and `R y z` implies `R x z`.

```agda
is-transitive : (R : A → A → Type ℓ) → Type _
is-transitive R = {x y z : _} → R x y → R y z → R x z
```

A **preorder** is a reflexive, transitive relation. Furthermore, we
impose that a preorder take value in propositions.

```agda
record is-preorder {A : Type ℓ} (R : A → A → Type ℓ') : Type (ℓ ⊔ ℓ') where
  field
    reflexive     : is-reflexive R
    transitive    : is-transitive R
    propositional : {x y : A} → is-prop (R x y)
```

## Partial Orders

A **partial order** is a preorder which, in addition, is antisymmetric:

```agda
is-anti-symmetric : (R : A → A → Type ℓ) → Type _
is-anti-symmetric R = {x y : _} → R x y → R y x → x ≡ y

record is-partial-order {A : Type ℓ} (R : A → A → Type ℓ') : Type (ℓ ⊔ ℓ') where
  field
    preorder : is-preorder R
    antisym : is-anti-symmetric R

  open is-preorder preorder public
```

Any type with a choice of partial order is a set. This is because of
`Rijke's theorem`{.Agda ident=Rijke-is-set}: Any type with a reflexive
relation implying equality is a set.

```agda
has-partial-order→is-set : {A : Type ℓ} {R : A → A → Type ℓ'}
                      → is-partial-order R
                      → is-set A
has-partial-order→is-set {A = A} {_≤_} ispo =
  Rijke-is-set {R = R'} reflexive' (λ { (x , y) → antisym x y }) is-prop'
  where
    open is-partial-order ispo
```

For the relation, we take $R(x, y) = (x \le y) \land (y \le x)$. By
antisymmetry, this implies $x = y$. Since propositions are closed under
products, this is a proposition.

```agda
    R' : A → A → Type _
    R' x y = (x ≤ y) × (y ≤ x)

    reflexive' : {x : A} → R' x x
    reflexive' = reflexive , reflexive

    is-prop' : {x y : A} → is-prop (R' x y)
    is-prop' (a , b) (a' , b') i = propositional a a' i , propositional b b' i
```

With this theorem, we can prove that being a partial order is a
proposition. We do this by the characterisation of propositions as those
types which are `contractible when inhabited`{.Agda
ident=contractible-if-inhabited}, since then we're free to assume A is a set.

```agda
is-partial-order-is-prop : {A : Type ℓ} {R : A → A → Type ℓ'}
                      → is-prop (is-partial-order R)
is-partial-order-is-prop {A = A} {R} = contractible-if-inhabited contract
  where
    open is-partial-order
    open is-preorder

    contract : is-partial-order R → is-contr (is-partial-order R)
    contract order = contr order deform where
      A-set : is-set A
      A-set = has-partial-order→is-set order
```

For the centre of contraction, we're free to use the given witness.
Since the paths end up being a big product of propositions, most of the
construction follows directly from the fact that `preorders are
propositional`{.Agda ident=propositional}.

```agda
      deform : (x : is-partial-order R) → order ≡ x
      deform x i .preorder .reflexive =
        x .propositional (order .preorder .reflexive)
                         (x .preorder .reflexive)
                         i
      deform x i .preorder .transitive p q =
        x .propositional (order .preorder .transitive p q)
                         (x .preorder .transitive p q)
                         i
```

To connect the propositionality witnesses, we use the fact that `is-prop
is a proposition`{.Agda ident=is-prop-is-prop}.

```agda
      deform x i .preorder .propositional =
        is-prop-is-prop (order .preorder .propositional)
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

is-trichotomous : {A : Type ℓ} → (R : A → A → Type ℓ') → Type (ℓ ⊔ ℓ')
is-trichotomous R = ∀ x y → Tri R x y
```

Trichotomy is a very powerful property, and we can derive a lot of useful
results from it!

To start, trichotomy immediately implies discreteness:

```agda
trichotomous-discrete : ∀ {A : Type ℓ} {R : A → A → Type ℓ'}
                      → is-trichotomous R → Discrete A
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
