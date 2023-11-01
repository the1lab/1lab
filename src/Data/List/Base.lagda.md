<!--
```agda
open import 1Lab.Path
open import 1Lab.Type

open import Data.Product.NAry
open import Data.Bool
```
-->

```agda
module Data.List.Base where
```

# The type of lists

This module contains the definition of the type of lists, and some basic
operations on lists. Properties of these operations are in the module
[`Data.List`], not here.

[`Data.List`]: Data.List.html

<!--
```agda
private variable
  ℓ : Level
  A B : Type ℓ

infixr 20 _∷_
```
-->

```agda
data List {ℓ} (A : Type ℓ) : Type ℓ where
  [] : List A
  _∷_ : A → List A → List A

{-# BUILTIN LIST List #-}
```

One of the first things we set up is list literal syntax (the
`From-product`{.Agda} class) for lists. The list corresponding to an
n-ary product is the list of its elements.

```agda
instance
  From-prod-List : From-product A (λ _ → List A)
  From-prod-List .From-product.from-prod = go where
    go : ∀ n → Vecₓ A n → List A
    go zero xs                = []
    go (suc zero) xs          = xs ∷ []
    go (suc (suc n)) (x , xs) = x ∷ go (suc n) xs

-- Test:
_ : [ 1 , 2 , 3 ] ≡ 1 ∷ 2 ∷ 3 ∷ []
_ = refl
```

## “Fields”

```agda
head : A → List A → A
head def []     = def
head _   (x ∷ _) = x

tail : List A → List A
tail []       = []
tail (_ ∷ xs) = xs
```

## Elimination

As with any inductive type, the type of lists-of-As has a
canonically-defined eliminator, but it also has some fairly popular
_recursors_, called "folds":

```agda
List-elim
  : ∀ {ℓ ℓ'} {A : Type ℓ} (P : List A → Type ℓ')
  → P []
  → (∀ x xs → P xs → P (x ∷ xs))
  → ∀ x → P x
List-elim P p[] p∷ []       = p[]
List-elim P p[] p∷ (x ∷ xs) = p∷ x xs (List-elim P p[] p∷ xs)

foldr : (A → B → B) → B → List A → B
foldr f x = List-elim _ x (λ x _ → f x)

foldl : (B → A → B) → B → List A → B
foldl f x []       = x
foldl f x (a ∷ as) = foldl f (f x a) as
```

## Functorial action

It's also possible to lift a function `A → B` to a function `List A →
List B`.

```agda
map : (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs
```

## Monoidal structure

We can define concatenation of lists by recursion:

```agda
_++_ : ∀ {ℓ} {A : Type ℓ} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

infixr 5 _++_

mapUp : (Nat → A → B) → Nat → List A → List B
mapUp f _ [] = []
mapUp f n (x ∷ xs) = f n x ∷ mapUp f (suc n) xs

length : List A → Nat
length [] = zero
length (x ∷ x₁) = suc (length x₁)

concat : List (List A) → List A
concat [] = []
concat (x ∷ xs) = x ++ concat xs

reverse : List A → List A
reverse = go [] where
  go : List A → List A → List A
  go acc [] = acc
  go acc (x ∷ xs) = go (x ∷ acc) xs

_∷r_ : List A → A → List A
xs ∷r x = xs ++ (x ∷ [])

all=? : (A → A → Bool) → List A → List A → Bool
all=? eq=? [] [] = true
all=? eq=? [] (x ∷ ys) = false
all=? eq=? (x ∷ xs) [] = false
all=? eq=? (x ∷ xs) (y ∷ ys) = and (eq=? x y) (all=? eq=? xs ys)

enumerate : ∀ {ℓ} {A : Type ℓ} → List A → List (Nat × A)
enumerate = go 0 where
  go : Nat → List _ → List (Nat × _)
  go x [] = []
  go x (a ∷ b) = (x , a) ∷ go (suc x) b

take : ∀ {ℓ} {A : Type ℓ} → Nat → List A → List A
take 0 xs = []
take (suc n) [] = []
take (suc n) (x ∷ xs) = x ∷ take n xs
```
