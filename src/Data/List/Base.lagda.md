<!--
```agda
open import 1Lab.Path
open import 1Lab.Type

open import Data.Product.NAry
open import Data.Dec.Base
open import Data.Bool

open import Meta.Foldable
open import Meta.Append
open import Meta.Idiom
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
```

<!--
```agda
instance
  Foldable-List : Foldable (eff List)
  Foldable-List .foldr f x = List-elim _ x (λ x _ → f x)

traverse
  : ∀ {M : Effect} ⦃ _ : Idiom M ⦄ (let module M = Effect M) {ℓ ℓ'}
      {a : Type ℓ} {b : Type ℓ'}
  → (a → M.₀ b) → List a → M.₀ (List b)
traverse f []       = pure []
traverse f (x ∷ xs) = ⦇ f x ∷ traverse f xs ⦈

sequence
  : ∀ {M : Effect} ⦃ _ : Idiom M ⦄ (let module M = Effect M) {ℓ}
      {a : Type ℓ}
  → List (M.₀ a) → M.₀ (List a)
sequence = traverse id

for
  : ∀ {M : Effect} ⦃ _ : Idiom M ⦄ (let module M = Effect M) {ℓ ℓ'}
      {a : Type ℓ} {b : Type ℓ'}
  → List a → (a → M.₀ b) → M.₀ (List b)
for f xs = traverse xs f

foldl : (B → A → B) → B → List A → B
foldl f x []       = x
foldl f x (a ∷ as) = foldl f (f x a) as
```
-->

## Functorial action

It's also possible to lift a function `A → B` to a function `List A →
List B`.

```agda
instance
  Map-List : Map (eff List)
  Map-List = record { map = go } where
    go : (A → B) → List A → List B
    go f []       = []
    go f (x ∷ xs) = f x ∷ go f xs
```

## Monoidal structure

We can define concatenation of lists by recursion:

```agda
_++_ : ∀ {ℓ} {A : Type ℓ} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

infixr 5 _++_

instance
  Append-List : ∀ {ℓ} {A : Type ℓ} → Append (List A)
  Append-List = record { mempty = [] ; _<>_ = _++_ }
```

<!--
```agda
map-up : (Nat → A → B) → Nat → List A → List B
map-up f _ []       = []
map-up f n (x ∷ xs) = f n x ∷ map-up f (suc n) xs

length : List A → Nat
length []       = zero
length (x ∷ xs) = suc (length xs)

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
take 0       xs       = []
take (suc n) []       = []
take (suc n) (x ∷ xs) = x ∷ take n xs

drop : ∀ {ℓ} {A : Type ℓ} → Nat → List A → List A
drop zero    xs       = xs
drop (suc n) []       = []
drop (suc n) (x ∷ xs) = drop n xs
```
-->

## Predicates

We can define a function that determines if a boolean-valued
predicate holds on every element of a list.

```agda
all-of : ∀ {ℓ} {A : Type ℓ} → (A → Bool) → List A → Bool
all-of f [] = true
all-of f (x ∷ xs) = and (f x) (all-of f xs)
```

Dually, we can also define a function that determines if a boolean-valued
predicate holds on some element of a list.

```agda
any-of : ∀ {ℓ} {A : Type ℓ} → (A → Bool) → List A → Bool
any-of f [] = false
any-of f (x ∷ xs) = or (f x) (any-of f xs)
```

<!--
```agda
∷-head-inj : ∀ {x y : A} {xs ys} → (x ∷ xs) ≡ (y ∷ ys) → x ≡ y
∷-head-inj {x = x} p = ap (head x) p

∷-tail-inj : ∀ {x y : A} {xs ys} → (x ∷ xs) ≡ (y ∷ ys) → xs ≡ ys
∷-tail-inj p = ap tail p

∷≠[] : ∀ {x : A} {xs} → ¬ (x ∷ xs) ≡ []
∷≠[] {A = A} p = subst distinguish p tt where
  distinguish : List A → Type
  distinguish []     = ⊥
  distinguish (_ ∷ _) = ⊤

instance
  Discrete-List : ∀ ⦃ d : Discrete A ⦄ → Discrete (List A)
  Discrete-List {x = []}     {y = []}     = yes refl
  Discrete-List {x = []}     {y = x ∷ y}  = no λ p → ∷≠[] (sym p)
  Discrete-List {x = x ∷ xs} {y = []}     = no ∷≠[]
  Discrete-List {x = x ∷ xs} {y = y ∷ ys} = case x ≡? y of λ where
    (yes x=y) → case Discrete-List {x = xs} {ys} of λ where
      (yes xs=ys) → yes (ap₂ _∷_ x=y xs=ys)
      (no  xs≠ys) → no λ p → xs≠ys (∷-tail-inj p)
    (no x≠y)      → no λ p → x≠y (∷-head-inj p)

traverse-up
  : ∀ {M : Effect} ⦃ _ : Idiom M ⦄ (let module M = Effect M) {ℓ ℓ'}
    {a : Type ℓ} {b : Type ℓ'}
  → (Nat → a → M.₀ b) → Nat → List a → M.₀ (List b)
traverse-up f n xs = sequence (map-up f n xs)
```
-->
