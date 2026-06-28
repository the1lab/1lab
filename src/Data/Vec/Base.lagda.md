<!--
```agda
open import 1Lab.Path
open import 1Lab.Type

open import Data.Product.NAry
open import Data.Maybe.Base
open import Data.List.Base as List using (List; []; _∷_; length)
open import Data.Dec.Base
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
open import Data.List.Length public
-- we need reexport make-irr for []v to work
open Data.Irr using (make-irr) public
open Data.Irr

private variable
  ℓ : Level
  A B C : Type ℓ
  n k : Nat
```
-->

# Vectors

The type `Vec`{.Agda} is a representation of n-ary tuples with
coordinates drawn from A.

```agda
record Vec {ℓ} (A : Type ℓ) (n : Nat) : Type ℓ where
  constructor vec
  field
    lower   : List A
    ⦃ len ⦄ : Irr (Length lower n)

pattern []v = vec []

infixr 20 _∷v_
_∷v_ : ∀ {n} → A → Vec A n → Vec A (suc n)
_∷v_ v (vec vs ⦃ p ⦄) = vec (v ∷ vs) ⦃ suc <$> p ⦄

data Vec-view {ℓ} {A : Type ℓ} : {n : Nat} → Vec A n → Typeω where
  []     : Vec-view []v
  _∷_  : ∀ {n} a → (vs : Vec A n) → Vec-view {n = suc n} (a ∷v vs)

vec-view : ∀ {n} (v : Vec A n) → Vec-view v
vec-view {n = zero} []v = []
vec-view {n = zero} (vec (x ∷ xs) ⦃ l ⦄) with () ← recover l
vec-view {n = suc n} (vec (x ∷ xs)) = x ∷ vec xs
  ⦃ len-uncons <$> auto ⦄
vec-view {n = suc n} (vec [] ⦃ l ⦄) with () ← recover l

list→vec : (xs : List A) → Vec A (length xs)
list→vec xs = vec xs

head : Vec A (suc n) → A
head (vec (x ∷ xs)) = x
head (vec [] ⦃ l ⦄) with () ← recover l

tail : Vec A (suc n) → Vec A n
tail v with (x ∷ xs) ← vec-view v = xs
```

The type `Vec A n` [is equivalent to] the type $\rm{Fin}(n) \to A$, i.e.,
the functions from the [[standard finite set]] with $n$ elements to the
type $A$. The halves of this equivalence are called `lookup`{.Agda} and
`tabulate`{.Agda}.

[is equivalent to]: Data.Vec.Properties.html

```agda
lookup : Vec A n → Fin n → A
lookup (vec xs) (fin n) = from-just! _ $ List.!?-just xs n p where abstract
  p : n Nat.< length xs
  p = ≤-trans auto $ subst (Nat._≤ length xs) (has-length auto) auto
```

## List syntax {defines="list-syntax-for-vectors"}

A similar type to `Vec`{.Agda} can be defined by _recursion_ as an
iteraded `non-dependent product`{.Agda}. The resulting type `Vecₓ`{.Agda}
has the advantage of supporting usual tuple syntax, but is fiddlier to
eliminate. This is solved by implementing the `From-product`{.Agda}
typeclass for `Vec`{.Agda}, which enables list syntax for the latter.

```agda
instance
  From-prod-Vec : From-product A (Vec A)
  From-prod-Vec .From-product.from-prod = go where
    go : ∀ n → Vecₓ A n → Vec A n
    go zero xs                = []v
    go (suc zero) xs          = xs ∷v []v
    go (suc (suc n)) (x , xs) = x ∷v go (suc n) xs

_++_ : ∀ {n k} → Vec A n → Vec A k → Vec A (n + k)
vec xs ++ vec ys = vec (xs List.++ ys) ⦃ liftA2 len-++ auto auto ⦄

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
```
-->

```agda
tabulate : (Fin n → A) → Vec A n
tabulate v  = vec (List.tabulate v) ⦃ forget (len-tabulate v) ⦄

instance
  Map-Vec : ∀ {n} → Map (eff (λ A → Vec A n ) )
  Map-Vec .Map.map f (vec l) = vec (f <$> l) ⦃ len-map <$> auto ⦄

zip :  Vec A n → Vec B n → Vec (A × B) n
zip (vec u) (vec v) = vec (List.zip u v) ⦃ liftA2 len-zip auto auto ⦄

zip-with : (A → B → C) → Vec A n → Vec B n → Vec C n
zip-with f (vec u) (vec v) = vec (List.zip-with f u v)
  ⦃ liftA2 len-zip-with auto auto ⦄

replicate : (n : Nat) → A → Vec A n
replicate zero a = []v
replicate (suc n) a = a ∷v replicate n a

_ : Path (Vec Nat 3) [ 1 , 2 , 3 ] (1 ∷v 2 ∷v 3 ∷v []v)
_ = refl
```
