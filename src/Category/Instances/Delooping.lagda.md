```agda
open import 1Lab.Prelude

open import Algebra.Monoid
open import Algebra.Group

open import Category.Base

module Category.Instances.Delooping where
```

<!--
```agda
private variable
  ℓ : Level
```
-->

Given a monoid $M$, we build a pointed precategory $B(M)$, where the
endomorphism monoid of the point recovers $M$.

```
B : ∀ {ℓ} {M : Type ℓ} → MonoidOn M → Precategory lzero ℓ
B {M = M} mm = r where
  module mm = MonoidOn mm
  open Precategory

  r : Precategory _ _
  r .Ob = ⊤
  r .Hom _ _ = M
  r .Hom-set _ _ = mm.hasIsSet
  r .Precategory.id = mm.identity
  r .Precategory._∘_ = mm._⋆_
  r .idr _ = mm.idʳ
  r .idl _ = mm.idˡ
  r .assoc _ _ _ = mm.associative
```

In addition to providing a concise description of sets with $M$-actions
(functors $B(M) \to \set$), the delooping category of a monoid lets us
reuse the category solver to solve monoid associativity/identity
problems:

<!--
```agda
open import Category.Solver
open import 1Lab.Reflection

findMonoidNames : Term → TC CategoryNames
findMonoidNames = findGenericNames (quote MonoidOn._⋆_) (quote MonoidOn.identity)

macro
  solveMonoidOn : Term → Term → TC ⊤
  solveMonoidOn = solveGeneric findMonoidNames (λ x → def (quote B) (x v∷ []))

  solveMonoid : ∀ {ℓ} (A : Monoid ℓ) → Term → TC ⊤
  solveMonoid (_ , mm) goal = do
    tmm ← quoteTC mm
    solveGeneric findMonoidNames (λ x → def (quote B) (x v∷ [])) tmm goal
```
-->

```agda
module _ (M : Monoid ℓ) where private
  module M = MonoidOn (M .snd)
  variable
    a b c d : M .fst

  test : ((a M.⋆ b) M.⋆ (c M.⋆ d))
       ≡ ((a M.⋆ (M.identity M.⋆ (b M.⋆ M.identity))) M.⋆ (c M.⋆ d))
  test = solveMonoid M
```