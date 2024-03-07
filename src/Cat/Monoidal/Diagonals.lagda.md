<!--
```agda
open import Cat.Instances.Product
open import Cat.Monoidal.Base
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Monoidal.Diagonals {o ℓ}
  {C : Precategory o ℓ} (Cᵐ : Monoidal-category C)
  where
```

# Monoidal categories with diagonals {defines="monoidal-category-with-diagonals"}

<!--
```agda
open Cat.Reasoning C
open Monoidal Cᵐ

_ = λ≡ρ
```
-->

A [[monoidal category]] can be equipped with a system of *diagonal
morphisms* $\delta_A : A \to A \otimes A$. Of course, such a system
should be natural in $A$; another sensible thing to require is that the
diagonal $1 \to 1 \otimes 1$ agree with the left (`hence`{.Agda ident=λ≡ρ}
also right) unitor.

We call the resulting structure a **monoidal category with diagonals**.

```agda
record Diagonals : Type (o ⊔ ℓ) where
  field
    diagonals : Id => -⊗- F∘ Cat⟨ Id , Id ⟩

  module δ = _=>_ diagonals

  δ : ∀ {A} → Hom A (A ⊗ A)
  δ = δ.η _

  field
    diagonal-λ→ : δ {Unit} ≡ λ→ {Unit}
```

The prototypical examples of monoidal categories with diagonals are
[[cartesian monoidal categories]].
