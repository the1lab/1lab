```agda
open import 1Lab.HLevel.Sets
open import 1Lab.HLevel
open import 1Lab.Path
open import 1Lab.Type

module 1Lab.Data.List where
```

# Lists

A _list_ is a finite, ordered sequence of elements of some type. Lists
are an inductive type:

```agda
data List {ℓ} (A : Type ℓ) : Type ℓ where
  nil : List A
  _∷_ : A → List A → List A
```

The first thing we prove is that, if `A` is a set, then so is `List
A`{.Agda ident=List}.

```agda
isSet→List-isSet : {ℓ : _} {A : Type ℓ} → isSet A
                 → isSet (List A)
isSet→List-isSet {A = A} set = Rijke-isSet {R = R} R-refl R-impliesId R-isProp where
  R : List A → List A → Type (level-of A)
  R nil nil = Lift _ ⊤
  R nil (h ∷ t) = Lift _ ⊥
  R (h ∷ t) nil = Lift _ ⊥
  R (h ∷ t) (h' ∷ t') = (h ≡ h') × R t t'

  R-refl : {x : List A} → R x x
  R-refl {nil} = lift tt
  R-refl {x ∷ t} = refl , R-refl {x = t}

  R-impliesId : {x y : List A} → R x y → x ≡ y
  R-impliesId {nil} {nil} _                = refl
  R-impliesId {_ ∷ _} {_ ∷ _} (p , rest) i = p i ∷ R-impliesId rest i

  R-isProp : {x y : List A} (p q : R x y) → p ≡ q
  R-isProp {nil} {nil} p q = refl
  R-isProp {x ∷ x₁} {x₂ ∷ y} p q i = 
    set _ _ (p .fst) (q .fst) i , R-isProp (p .snd) (q .snd) i 
```

We can define concatenation of lists by recursion:

```agda
_++_ : {ℓ : _} {A : Type ℓ} → List A → List A → List A
nil      ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)
```

Then we can prove that this operation is associative and has `nil` as
both left and right units:

```agda
++-assoc : {ℓ : _} {A : Type ℓ} (xs ys zs : List A)
         → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc nil ys zs = refl
++-assoc (x ∷ xs) ys zs i = x ∷ ++-assoc xs ys zs i

++-idˡ : {ℓ : _} {A : Type ℓ} (xs : List A) → nil ++ xs ≡ xs
++-idˡ xs i = xs

++-idʳ : {ℓ : _} {A : Type ℓ} (xs : List A) → xs ++ nil ≡ xs
++-idʳ nil i = nil
++-idʳ (x ∷ xs) i = x ∷ ++-idʳ xs i
```
