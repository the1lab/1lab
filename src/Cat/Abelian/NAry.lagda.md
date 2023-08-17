<!--
```agda
open import Algebra.Group.NAry
open import Algebra.Group.Ab
open import Algebra.Group

open import Cat.Abelian.Base
open import Cat.Prelude

open import Data.Fin.Base
```
-->

```agda
module Cat.Abelian.NAry {o ℓ} {C : Precategory o ℓ} (A : Ab-category C) where
```

# n-Ary operations on Hom-groups

We instantiate the theory of n-ary sums in a group to the special case
of the $\hom$ [[abelian groups]] of an $\Ab$-enriched category. In
particular, we show that the linearity of function composition extends
to distribution over arbitrary sums.

```agda
private module A = Ab-category A

∑ₕ : ∀ {x y} n → (Fin n → A.Hom x y) → A.Hom x y
∑ₕ n f = ∑ {n = n} (Abelian→Group-on (A.Abelian-group-on-hom _ _)) f

∑-∘-left : ∀ {j} {A B C} (f : Fin j → A.Hom A B) {g : A.Hom B C}
          → g A.∘ ∑ₕ j f
          ≡ ∑ₕ j (λ i → g A.∘ f i)
∑-∘-left {zero} f  = A.∘-zero-r
∑-∘-left {suc j} f {g = g} =
  g A.∘ (f 0 A.+ ∑ₕ j (λ i → f (fsuc i)))         ≡˘⟨ A.∘-linear-r _ _ _ ⟩
  g A.∘ f 0 A.+ ⌜ g A.∘ ∑ₕ j (λ i → f (fsuc i)) ⌝ ≡⟨ ap! (∑-∘-left {j} _) ⟩
  g A.∘ f 0 A.+ ∑ₕ j (λ i → g A.∘ f (fsuc i))     ∎

∑-∘-right : ∀ {j} {A B C} (f : Fin j → A.Hom B C) {g : A.Hom A B}
        → ∑ₕ j f A.∘ g
        ≡ ∑ₕ j (λ i → f i A.∘ g)
∑-∘-right {zero} f      = A.∘-zero-l
∑-∘-right {suc j} f {g} =
  (f 0 A.+ ∑ₕ j (λ i → f (fsuc i))) A.∘ g          ≡˘⟨ A.∘-linear-l _ _ _ ⟩
  f 0 A.∘ g A.+ ⌜ ∑ₕ j (λ i → f (fsuc i)) A.∘ g ⌝  ≡⟨ ap! (∑-∘-right {j} _) ⟩
  (f 0 A.∘ g A.+ ∑ₕ j (λ i → f (fsuc i) A.∘ g))    ∎
```
