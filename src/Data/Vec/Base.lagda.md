<!--
```agda
open import 1Lab.Path
open import 1Lab.Type

open import Data.Product.NAry
open import Data.List.Base hiding (lookup ; tabulate)
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

lookup : Vec A n → Fin n → A
lookup (x ∷ xs) fzero = x
lookup (x ∷ xs) (fsuc i) = lookup xs i
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

-- Will always compute:
lookup-safe : Vec A n → Fin n → A
lookup-safe {A = A} xs n =
  Fin-elim (λ {n} _ → Vec A n → A)
    (λ {k} xs → Vec-elim (λ {k'} _ → suc k ≡ k' → A)
      (λ p → absurd (suc≠zero p))
      (λ x _ _ _ → x) xs refl)
    (λ {i} j cont vec →
      Vec-elim (λ {k'} xs → suc i ≡ k' → A)
        (λ p → absurd (suc≠zero p))
        (λ {n} head tail _ si=sn → cont (Vec-cast (suc-inj (sym si=sn)) tail)) vec refl)
    n xs
```
-->

```agda
tabulate : (Fin n → A) → Vec A n
tabulate {zero} f  = []
tabulate {suc n} f = f fzero ∷ tabulate (λ x → f (fsuc x))

map : (A → B) → Vec A n → Vec B n
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

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
