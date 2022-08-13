```agda
open import 1Lab.Reflection.Record

open import Cat.Univalent.Instances.Opposite
open import Cat.Displayed.Instances.Family
open import Cat.Displayed.Univalence
open import Cat.Instances.Discrete
open import Cat.Instances.Functor
open import Cat.Displayed.Fibre
open import Cat.Displayed.Total
open import Cat.Displayed.Base
open import Cat.Instances.Sets
open import Cat.Prelude


import Cat.Reasoning

module Cat.Instances.Poly where
```

# Polynomial functors and lenses

The category of _polynomial functors_ is the free coproduct completion
of $\sets$. Equivalently, it is the [total space] of the [family
fibration] of $\sets\op$. More concretely, an object of $\ht{Poly}$ is
given by a set $I$ and a family of sets $I \to \sets$. The idea is that
this data corresponds to the polynomial (set-valued, with set
coefficients) given by

$$
p(y) = \sum_{i : I} y^{A_i}
$$

[total space]: Cat.Displayed.Total.html
[family fibration]: Cat.Displayed.Instances.Family.html

```agda
Poly : ∀ ℓ → Precategory (lsuc ℓ) ℓ
Poly ℓ = ∫ {ℓ = ℓ} (Family (Sets ℓ ^op))

module Poly {ℓ} = Cat.Reasoning (Poly ℓ)
```

Our standard toolkit for showing [univalence of total spaces] applies here:

[univalence of total spaces]: Cat.Displayed.Univalence.html

```agda
Poly-is-category : ∀ {ℓ} → is-category (Poly ℓ)
Poly-is-category =
  is-category-total _ Sets-is-category $
    is-category-fibrewise′ _
      (λ x → Families-are-categories _ x (opposite-is-category Sets-is-category))
      Sets-is-category
```

It is entirely mechanical to calculate that morphisms in $\ht{Poly}$ are
given by pairs of a reindexing together with a contravariant action on
the families. It is _so_ mechanical that we can do it automatically:

```agda
poly-maps : ∀ {ℓ} {A B} → Iso
  (Poly.Hom {ℓ} A B)
  (Σ[ f ∈ (∣ A .fst ∣ → ∣ B .fst ∣) ] ∀ x → ∣ B .snd (f x) ∣ → ∣ A .snd x ∣)
unquoteDef poly-maps = define-record-iso poly-maps (quote Total-hom)
```
