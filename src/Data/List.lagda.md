```agda
open import 1Lab.HLevel.Retracts
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type
open import Data.Bool

module Data.List where

open import Agda.Builtin.List public
```

# Lists

A _list_ is a finite, ordered sequence of elements of some type. Lists
are an inductive type, as an Agda builtin. Here, we echo the
definition for clarity:

<!--
```
private variable
  ℓ : Level
  A B : Type ℓ
```
-->

```agda
module _ where private
  data List' {ℓ} (A : Type ℓ) : Type ℓ where
    [] : List' A
    _∷_ : A → List' A → List' A
```

## Path Space

We begin by characteristing the behaviour of paths of lists. For
instance, `∷`{.Agda} is injective in both its arguments:

```agda
head : A → List A → A
head def []     = def
head _   (x ∷ _) = x

tail : List A → List A
tail []      = []
tail (_ ∷ xs) = xs

∷-head-inj : ∀ {x y : A} {xs ys} → (x ∷ xs) ≡ (y ∷ ys) → x ≡ y
∷-head-inj {x = x} p = ap (head x) p

∷-tail-inj : ∀ {x y : A} {xs ys} → (x ∷ xs) ≡ (y ∷ ys) → xs ≡ ys
∷-tail-inj p = ap tail p
```

Similarly, it is possible to distinguish `_ ∷ _` from `[]`{.Agda}, so
they are not identical:

```agda
∷≠[] : ∀ {x : A} {xs} → (x ∷ xs) ≡ [] → ⊥
∷≠[] {A = A} p = subst distinguish p tt where
  distinguish : List A → Type
  distinguish []     = ⊥
  distinguish (_ ∷ _) = ⊤
```

Using these lemmas, we can characterise the path space of `List A` in
terms of the path space of `A`. For this, we define by induction a type
family `Code`{.Agda}, which represents paths in `List A` by
iterated products of paths in `A`.

```agda
module ListPath {A : Type ℓ} where
  Code : List A → List A → Type (level-of A)
  Code [] []             = Lift (level-of A) ⊤
  Code [] (x ∷ x₁)       = Lift (level-of A) ⊥
  Code (h ∷ t) []        = Lift (level-of A) ⊥
  Code (h ∷ t) (h' ∷ t') = (h ≡ h') × Code t t'
```

We have a map `encode`{.Agda} which turns a path into a `Code`{.Agda},
and a function `decode`{.Agda} which does the opposite.

```agda
  encode : {xs ys : List A} → xs ≡ ys → Code xs ys
  encode {xs = []} {ys = []} path = lift tt
  encode {xs = []} {ys = x ∷ ys} path = lift (∷≠[] (sym path))
  encode {xs = x ∷ xs} {ys = []} path = lift (∷≠[] path)
  encode {xs = x ∷ xs} {ys = x₁ ∷ ys} path =
    ∷-head-inj path , encode {xs = xs} {ys = ys} (ap tail path)

  decode : {xs ys : List A} → Code xs ys → xs ≡ ys
  decode {[]} {[]} code = refl
  decode {x ∷ xs} {x₁ ∷ ys} (p , q) i = p i ∷ decode q i
```

These maps are inverses by construction:

```agda
  encode-decode : {xs ys : List A} (p : Code xs ys) → encode (decode p) ≡ p
  encode-decode {[]} {[]} (lift tt) = refl
  encode-decode {x ∷ xs} {x₁ ∷ ys} (p , q) i = p , encode-decode q i

  decode-encode : {xs ys : List A} (p : xs ≡ ys) → decode (encode p) ≡ p
  decode-encode = J (λ y p → decode (encode p) ≡ p) de-refl where
    de-refl : {xs : List A} → decode (encode (λ i → xs)) ≡ (λ i → xs)
    de-refl {[]}         = refl
    de-refl {x ∷ xs} i j = x ∷ de-refl {xs = xs} i j

  Code≃Path : {xs ys : List A} → Code xs ys ≃ (xs ≡ ys)
  Code≃Path = Iso→Equiv (decode , iso encode decode-encode encode-decode)
```

Thus we have a characterisation of `Path (List A)` in terms of `Path A`.
We use this to prove that lists preserve h-levels for $n \ge 2$, i.e. if
`A` is a set (or more) then `List A` is a type of the same h-level.

```agda
  List-is-hlevel : (n : Nat) → is-hlevel A (2 + n) → is-hlevel (List A) (2 + n)
  List-is-hlevel n ahl x y = is-hlevel≃ (suc n) Code≃Path Code-is-hlevel where
    Code-is-hlevel : {x y : List A} → is-hlevel (Code x y) (suc n)
    Code-is-hlevel {[]} {[]}         = is-prop→is-hlevel-suc λ x y → refl
    Code-is-hlevel {[]} {x ∷ y}      = is-prop→is-hlevel-suc λ x → absurd (Lift.lower x)
    Code-is-hlevel {x ∷ x₁} {[]}     = is-prop→is-hlevel-suc λ x → absurd (Lift.lower x)
    Code-is-hlevel {x ∷ x₁} {x₂ ∷ y} = ×-is-hlevel (suc n) (ahl _ _) Code-is-hlevel

  instance
    H-Level-List : ∀ {n} {k} → ⦃ H-Level A (2 + n) ⦄ → H-Level (List A) (2 + n + k)
    H-Level-List {n = n} ⦃ x ⦄ =
      basic-instance (2 + n) (List-is-hlevel n (H-Level.has-hlevel x))

  is-set→List-is-set : is-set A → is-set (List A)
  is-set→List-is-set = List-is-hlevel zero
```

We can define concatenation of lists by recursion:

```agda
infixr 5 _++_
_++_ : ∀ {ℓ} {A : Type ℓ} → List A → List A → List A
[]      ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)
```

Then we can prove that this operation is associative and has `[]` as
both left and right units:

```agda
++-assoc : ∀ {ℓ} {A : Type ℓ} (xs ys zs : List A)
         → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs i = x ∷ ++-assoc xs ys zs i

++-idl : ∀ {ℓ} {A : Type ℓ} (xs : List A) → [] ++ xs ≡ xs
++-idl xs i = xs

++-idr : ∀ {ℓ} {A : Type ℓ} (xs : List A) → xs ++ [] ≡ xs
++-idr [] i = []
++-idr (x ∷ xs) i = x ∷ ++-idr xs i
```

## Lemmas

Continuing with the useful lemmas, if the heads and tails of two lists
are identified, then the lists themselves are identified:

```agda
ap-∷ : ∀ {x y : A} {xs ys : List A}
     → x ≡ y → xs ≡ ys
     → Path (List A) (x ∷ xs) (y ∷ ys)
ap-∷ x≡y xs≡ys i = x≡y i ∷ xs≡ys i
```

<!--
⚠️ TODO: Explain these ⚠️

```agda
map : (A → B) → List A → List B
map f [] = []
map f (x₁ ∷ x₂) = f x₁ ∷ map f x₂

mapUp : (Nat → A → B) → Nat → List A → List B
mapUp f _ [] = []
mapUp f n (x ∷ xs) = f n x ∷ mapUp f (suc n) xs

length : List A → Nat
length [] = zero
length (x ∷ x₁) = suc (length x₁)

foldr : (A → B → B) → B → List A → B
foldr f z [] = z
foldr f z (x ∷ xs) = f x (foldr f z xs)

foldl : (B → A → B) → B → List A → B
foldl f z [] = z
foldl f z (x ∷ xs) = foldl f (f z x) xs

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
```
-->
