```agda
open import 1Lab.Path
open import 1Lab.Type

open import Data.Product.NAry
open import Data.Fin.Base

module Data.Vec.Base where
```

# Vectors

The type `Vec`{.Agda} is a representation of n-ary tuples with
coordinates drawn from A. Therefore, it is equivalent to the type
$\id{Fin}(n) \to A$, i.e., the functions from the \r{standard finite
set} with $n$ elements to the type $A$. The halves of this equivalence
are called `lookup`{.Agda} and `tabulate`{.Agda}.

```agda
data Vec {ℓ} (A : Type ℓ) : Nat → Type ℓ where
  []  : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

infixr 20 _∷_

private variable
  ℓ : Level
  A B : Type ℓ
  n k : Nat

lookup : Vec A n → Fin n → A
lookup (x ∷ xs) fzero = x
lookup (x ∷ xs) (fsuc i) = lookup xs i

tabulate : (Fin n → A) → Vec A n
tabulate {zero} f  = []
tabulate {suc n} f = f fzero ∷ tabulate (λ x → f (fsuc x))

map : (A → B) → Vec A n → Vec B n
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

instance
  From-prod-Vec : From-product A (Vec A)
  From-prod-Vec .From-product.from-prod = go where
    go : ∀ n → Vecₓ A n → Vec A n
    go zero xs                = []
    go (suc zero) xs          = xs ∷ []
    go (suc (suc n)) (x , xs) = x ∷ go (suc n) xs

_ : Path (Vec Nat 3) [ 1 , 2 , 3 ] (1 ∷ 2 ∷ 3 ∷ [])
_ = refl
```
