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

## Operations on Relations

We can take the union of two relations by taking the pointwise truncated
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

We can compose two relations by requiring the (mere) existence of a
common endpoint.

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
