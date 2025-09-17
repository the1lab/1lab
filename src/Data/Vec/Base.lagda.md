<!--
```agda
open import 1Lab.Path
open import 1Lab.Type

open import Data.Product.NAry
open import Data.Fin.Base
open import Data.Nat.Base
```
-->

```agda
module Data.Vec.Base where
```

# Vectors

The type `Vec`{.Agda} is a representation of n-ary tuples with
coordinates drawn from A. Therefore, it is equivalent to the type
$\rm{Fin}(n) \to A$, i.e., the functions from the [[standard finite
set]] with $n$ elements to the type $A$. The halves of this equivalence
are called `lookup`{.Agda} and `tabulate`{.Agda}.

```agda
data Vec {ℓ} (A : Type ℓ) : Nat → Type ℓ where
  []  : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

Vec-elim
  : ∀ {ℓ ℓ'} {A : Type ℓ} (P : ∀ {n} → Vec A n → Type ℓ')
  → P []
  → (∀ {n} x (xs : Vec A n) → P xs → P (x ∷ xs))
  → ∀ {n} (xs : Vec A n) → P xs
Vec-elim P p[] p∷ [] = p[]
Vec-elim P p[] p∷ (x ∷ xs) = p∷ x xs (Vec-elim P p[] p∷ xs)

infixr 20 _∷_

private variable
  ℓ : Level
  A B C : Type ℓ
  n k : Nat

head : Vec A (suc n) → A
head (x ∷ xs) = x

tail : Vec A (suc n) → Vec A n
tail (x ∷ xs) = xs

lookup : Vec A n → Fin n → A
lookup xs n with fin-view n
... | zero  = head xs
... | suc i = lookup (tail xs) i
```

<!--
```agda
Vec-cast : {x y : Nat} → x ≡ y → Vec A x → Vec A y
Vec-cast {A = A} {x = x} {y = y} p xs =
  Vec-elim (λ {n} _ → (y : Nat) → n ≡ y → Vec A y)
    (λ { zero _ → []
       ; (suc x) p → absurd (zero≠suc p)
       })
    (λ { {n} head tail cast-tail zero 1+n=len → absurd (suc≠zero 1+n=len)
       ; {n} head tail cast-tail (suc len) 1+n=len →
          head ∷ cast-tail len (suc-inj 1+n=len)
       })
    xs y p
```
-->

```agda
tabulate : (Fin n → A) → Vec A n
tabulate {zero} f  = []
tabulate {suc n} f = f fzero ∷ tabulate (λ x → f (fsuc x))

map : (A → B) → Vec A n → Vec B n
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

_++_ : ∀ {n k} → Vec A n → Vec A k → Vec A (n + k)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

zip-with : (A → B → C) → Vec A n → Vec B n → Vec C n
zip-with f [] [] = []
zip-with f (x ∷ xs) (y ∷ ys) = f x y ∷ zip-with f xs ys

replicate : (n : Nat) → A → Vec A n
replicate zero a = []
replicate (suc n) a = a ∷ replicate n a

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
