```agda
open import Algebra.Monoid

open import Cat.Prelude

module Cat.Instances.Delooping where
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
B : ∀ {ℓ} {M : Type ℓ} → Monoid-on M → Precategory lzero ℓ
B {M = M} mm = r where
  module mm = Monoid-on mm
  open Precategory

  r : Precategory _ _
  r .Ob = ⊤
  r .Hom _ _ = M
  r .Hom-set _ _ = mm.has-is-set
  r .Precategory.id = mm.identity
  r .Precategory._∘_ = mm._⋆_
  r .idr _ = mm.idr
  r .idl _ = mm.idl
  r .assoc _ _ _ = mm.associative
```

In addition to providing a concise description of sets with $M$-actions
(functors $B(M) \to \set$), the delooping category of a monoid lets us
reuse the category solver to solve monoid associativity/identity
problems:

<!--
```agda
open import Cat.Solver
open import 1Lab.Reflection

find-monoid-names : Term → TC CategoryNames
find-monoid-names =
  find-generic-names (quote Monoid-on._⋆_) (quote Monoid-on.identity)

macro
  solve-monoid-on : Term → Term → TC ⊤
  solve-monoid-on = solve-generic find-monoid-names (λ x → def (quote B) (x v∷ []))

  solve-monoid : ∀ {ℓ} (A : Monoid ℓ) → Term → TC ⊤
  solve-monoid (_ , mm) goal = do
    tmm ← quoteTC mm
    solve-generic find-monoid-names (λ x → def (quote B) (x v∷ [])) tmm goal
```
-->

```agda
module _ (M : Monoid ℓ) where private
  module M = Monoid-on (M .snd)
  variable
    a b c d : M .fst

  test : ((a M.⋆ b) M.⋆ (c M.⋆ d))
       ≡ ((a M.⋆ (M.identity M.⋆ (b M.⋆ M.identity))) M.⋆ (c M.⋆ d))
  test = solve-monoid M
```
