<!--
```agda
open import 1Lab.Prelude
open import Data.Sum
```
-->

```agda
module Data.Rel.Base where
```

# Relations

A **relation** between types $A$ and $B$ consists of a family of types
indexed by $A$ and $B$.

```agda
Rel : ∀ {a b} → Type a → Type b → (ℓ : Level) → Type _
Rel A B ℓ = A → B → Type ℓ
```

<!--
```agda
private variable
  ℓ ℓ' : Level
  A B C : Type ℓ
  R S : Rel A B ℓ
```
-->

We say that a relation is **propositional** if $R(x,y)$ is a proposition
for every $x$ and $y$.

```agda
is-prop-rel : Rel A B ℓ → Type _
is-prop-rel R = ∀ {x y} → is-prop (R x y)
```

## Operations on Propositional Relations

We can take the union of two propositional relations by taking the
pointwise truncated
coproduct.

```agda
_∪r_ : Rel A B ℓ → Rel A B ℓ' → Rel A B _
R ∪r S = λ x y → ∥ R x y ⊎ S x y ∥
```

Likewise, intersection can be defined by taking the pointwise product
of the two relations.

```agda
_∩r_ : Rel A B ℓ → Rel A B ℓ' → Rel A B _
R ∩r S = λ x y → R x y × S x y
```

We can compose two propositional relations by requiring the (mere)
existence of a common endpoint.

```agda
_∘r_ : Rel B C ℓ → Rel A B ℓ' → Rel A C _
R ∘r S = λ x y → ∃[ z ∈ _ ] (S x z × R z y)
```

Every relation between $A$ and $B$ can be flipped to get a relation
between $B$ and $A$.

```agda
flipr : Rel A B ℓ → Rel B A ℓ
flipr R = λ x y → R y x
```

## Relationships between Relations

We say that a relation $R$ is contained in another relation $S$
if $R(x,y)$ implies $S(x,y)$ for every $x$ and $y$.

```agda
_⊆r_ : Rel A B ℓ → Rel A B ℓ' → Type _
R ⊆r S = ∀ {x y} → R x y → S x y
```

Equality of propositional relations can be characterised in terms
of containment.

```agda
prop-rel-ext
  : is-prop-rel R → is-prop-rel S
  → R ⊆r S → S ⊆r R → R ≡ S
prop-rel-ext R-prop S-prop R⊆S S⊆R =
  funext λ x → funext λ y → ua (prop-ext R-prop S-prop R⊆S S⊆R)
```

## Properties of Relations

A relation is **reflexive** if every element is related to itself.

```agda
is-reflexive : Rel A A ℓ → Type _
is-reflexive R = ∀ x → R x x
```

A relation is **symmetric** if every $R(x,y)$ implies that $R(y,x)$.

```agda
is-symmetric : Rel A A ℓ → Type _
is-symmetric R = ∀ {x y} → R x y → R y x
```

A relation is **transitive** if $R(x,y)$ and $R(y,z)$ implies that
$R(x,z)$.

```agda
is-transitive : Rel A A ℓ → Type _
is-transitive R = ∀ {x y z} → R x y → R y z → R x z
```
