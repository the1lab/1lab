<!--
```agda
open import Cat.Functor.Hom.Representable
open import Cat.Functor.Naturality
open import Cat.Functor.Base
open import Cat.Functor.Hom
open import Cat.Prelude
```
-->

```agda
module Cat.Functor.Hom.Duality where
```

# Duality of Hom functors

We prove the obvious dualities between $\hom$ functors of opposite categories, and
between representable and corepresentable functors.

<!--
```agda
private variable
  o ℓ : Level
  C : Precategory o ℓ

open Representation
open Corepresentation
```
-->

```agda
Hom-from-op : ∀ c → Hom-from (C ^op) c ≡ Hom-into C c
Hom-from-op c = Functor-path (λ _ → refl) (λ _ → refl)

Hom-into-op : ∀ c → Hom-into (C ^op) c ≡ opFˡ (Functor.op (Hom-from C c))
Hom-into-op c = Functor-path (λ _ → refl) (λ _ → refl)
```
