<!--
```agda
open import 1Lab.Path
open import 1Lab.Type

open import Data.Product.NAry
open import Data.Maybe.Base
open import Data.List.Base hiding (head ; tail ; lookup) renaming (tabulate to tabulateℓ ; _++_ to _++ℓ_)
open import Data.Fin.Base
open import Data.Nat.Base as Nat
open import Data.Id.Base

open import Meta.Idiom

import Data.Irr
```
-->

```agda
module Data.Vec.Base where
```
<!--
```agda
-- we need reexport make-irr for []v to work
open Data.Irr using (make-irr) public
open Data.Irr
```
-->

# Vectors

The type `Vec`{.Agda} is a representation of n-ary tuples with
coordinates drawn from A. Therefore, it is equivalent to the type
$\rm{Fin}(n) \to A$, i.e., the functions from the [[standard finite
set]] with $n$ elements to the type $A$. The halves of this equivalence
are called `lookup`{.Agda} and `tabulate`{.Agda}.

```agda
private variable
  ℓ : Level
  A B C : Type ℓ
  n k : Nat

data Length {ℓ} {A : Type ℓ} : List A → Nat → Type ℓ where
  zero : Length [] zero
  suc  : ∀ {x xs n} → Length xs n → Length (x ∷ xs) (suc n)

instance
  Length-zero : Length {A = A} [] zero
  Length-zero = zero

  Length-suc : ∀ {x n} {xs : List A} → ⦃ _ : Length xs n ⦄
    → Length (x ∷ xs) (suc n)
  Length-suc ⦃ l ⦄ = suc l

  Length-length : ∀ {xs : List A} → Length xs (length xs)
  Length-length {xs = []} = zero
  Length-length {xs = x ∷ xs} = suc Length-length
  {-# INCOHERENT Length-length #-}


length-uncons : ∀ {xs n x} → Length {A = A} (x ∷ xs) (suc n) → Length xs n
length-uncons (suc l) = l

has-lengthᵢ : ∀ {xs : List A} {n : Nat} → Irr (Length xs n) → length xs ≡ᵢ n
has-lengthᵢ {xs = []} {n = zero} len = reflᵢ
has-lengthᵢ {xs = x ∷ xs} {n = suc n} len = apᵢ suc $ has-lengthᵢ $ length-uncons <$> len

has-length : ∀ {xs : List A} {n : Nat} → Irr (Length xs n) → length xs ≡ n
has-length l = Id≃path.to $ has-lengthᵢ l

record Vec {ℓ} (A : Type ℓ) (n : Nat) : Type ℓ where
  constructor vec
  field
    lower   : List A
    ⦃ len ⦄ : Irr (Length lower n)

pattern []v = vec []

infixr 20 _∷v_
_∷v_ : ∀ {n} → A → Vec A n → Vec A (suc n)
_∷v_ v (vec vs ⦃ p ⦄) = vec (v ∷ vs) ⦃ suc <$> p ⦄

data Vec-view {ℓ} {A : Type ℓ} : {n : Nat} → Vec A n → Type ℓ where
  []     : Vec-view {n = 0} []v
  _∷_  : ∀ {n} (a : A) → (vs : Vec A n) → Vec-view {n = suc n} (a ∷v vs)

vec-view : ∀ {n} (v : Vec A n) → Vec-view v
vec-view {n = zero} (vec []) = []
vec-view {n = suc k} (vec (x ∷ l) ⦃ p ⦄) = x ∷ vec l ⦃ length-uncons <$> p ⦄

list→vec : (xs : List A) → Vec A (length xs)
list→vec xs = vec xs

head : Vec A (suc n) → A
head (vec (x ∷ xs)) = x

tail : Vec A (suc n) → Vec A n
tail v with (x ∷ xs) ← vec-view v = xs

lookup : Vec A n → Fin n → A
lookup (vec xs ⦃ forget len ⦄) (fin n ⦃ n<xs ⦄) =
  from-just! _ $ !?-just xs n $ ≤-trans n<xs $ subst (Nat._≤ length xs) (has-length $ forget len) auto

instance
  From-prod-Vec : From-product A (Vec A)
  From-prod-Vec .From-product.from-prod = go where
    go : ∀ n → Vecₓ A n → Vec A n
    go zero xs                = []v
    go (suc zero) xs          = xs ∷v []v
    go (suc (suc n)) (x , xs) = x ∷v go (suc n) xs

_++_ : ∀ {n k} → Vec A n → Vec A k → Vec A (n + k)
xs ++ ys with vec-view xs
...| [] = ys
...| (x ∷ xs) = x ∷v (xs ++ ys)

Vec-elim
  : ∀ {ℓ ℓ'} {A : Type ℓ} (P : ∀ {n} → Vec A n → Type ℓ')
  → P []v
  → (∀ {n} x (xs : Vec A n) → P xs → P (x ∷v xs))
  → ∀ {n} (xs : Vec A n) → P xs
Vec-elim P p[] p∷ v with vec-view v
... | [] = p[]
... | (x ∷ xs) = p∷ x xs $ Vec-elim P p[] p∷ xs
```

<!--
```agda
Vec-cast : {x y : Nat} → x ≡ y → Vec A x → Vec A y
Vec-cast {A = A} {x = x} {y = y} p (vec l ⦃ len ⦄) =
  vec l ⦃ subst (λ n → Length l n) p <$> len ⦄

len-tab : ∀ {n} → (v : Fin n → A) → Length (tabulateℓ v) n
len-tab {n = zero} v = zero
len-tab {n = suc n} v = suc (len-tab {n = n} (v ∘ fsuc))
```
-->

```agda
tabulate : (Fin n → A) → Vec A n
tabulate v  = vec (tabulateℓ v) ⦃ forget (len-tab v) ⦄

len-map : ∀ {ℓ ℓ' n} {A : Type ℓ} {B : Type ℓ'} (f : A → B) (xs : List A) → Length xs n → Length (f <$> xs) n
len-map {n = zero} f [] x = zero
len-map {n = suc n} f (x ∷ xs) (suc l) = suc (len-map f xs l)

instance
  Map-Vec : ∀ {n} → Map (eff (λ A → Vec A n ) )
  Map-Vec = record { map = λ { f (vec l ⦃ len ⦄) → vec (f <$> l) ⦃ len-map f l <$> len ⦄ } }

zip-with : (A → B → C) → Vec A n → Vec B n → Vec C n
zip-with f u v with vec-view u | vec-view v
... |  []       | []       = []v
... |  (x ∷ xs) | (y ∷ ys) = f x y ∷v zip-with f xs ys

replicate : (n : Nat) → A → Vec A n
replicate zero a = []v
replicate (suc n) a = a ∷v replicate n a

_ : Path (Vec Nat 3) [ 1 , 2 , 3 ] (1 ∷v 2 ∷v 3 ∷v []v)
_ = refl
```
