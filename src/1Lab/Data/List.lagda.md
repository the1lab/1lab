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

<!--
```
private variable
  ℓ : Level
  A : Type ℓ
```
-->

```agda
data List {ℓ} (A : Type ℓ) : Type ℓ where
  nil : List A
  _∷_ : A → List A → List A
```

The first thing we prove is that, if `A` is a set, then so is `List
A`{.Agda ident=List}.

```agda
isSet→List-isSet : ∀ {ℓ} {A : Type ℓ} → isSet A
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
infixr 5 _++_
_++_ : ∀ {ℓ} {A : Type ℓ} → List A → List A → List A
nil      ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)
```

Then we can prove that this operation is associative and has `nil` as
both left and right units:

```agda
++-assoc : ∀ {ℓ} {A : Type ℓ} (xs ys zs : List A)
         → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc nil ys zs = refl
++-assoc (x ∷ xs) ys zs i = x ∷ ++-assoc xs ys zs i

++-idˡ : ∀ {ℓ} {A : Type ℓ} (xs : List A) → nil ++ xs ≡ xs
++-idˡ xs i = xs

++-idʳ : ∀ {ℓ} {A : Type ℓ} (xs : List A) → xs ++ nil ≡ xs
++-idʳ nil i = nil
++-idʳ (x ∷ xs) i = x ∷ ++-idʳ xs i
```

## Lemmas

Now, for a bunch of useful little lemmas! First, `∷` is injective
in both arguments:

```agda
head : A → List A → A
head def nil     = def
head _   (x ∷ _) = x

tail : List A → List A
tail nil      = nil
tail (_ ∷ xs) = xs

∷-head-inj : ∀ {x y : A} {xs ys} → (x ∷ xs) ≡ (y ∷ ys) → x ≡ y
∷-head-inj {x = x} p = ap (head x) p

∷-tail-inj : ∀ {x y : A} {xs ys} → (x ∷ xs) ≡ (y ∷ ys) → xs ≡ ys
∷-tail-inj p = ap tail p
```

Continuing with the useful lemmas, if the head and tail of two lists are equal,
then the two lists are equal:

```agda
ap-∷ : ∀ {x y : A} {xs ys} → x ≡ y → xs ≡ ys → x ∷ xs ≡ y ∷ ys
ap-∷ {x = x} {y = y} {xs = xs} {ys = ys} x≡y xs≡ys =
  subst (λ z → x ∷ xs ≡ z ∷ ys) x≡y (ap (x ∷_) xs≡ys)
```

It is impossible for an empty list to be equal to a non-empty one:

```agda
∷≠nil : ∀ {x : A} {xs} → (x ∷ xs) ≡ nil → ⊥
∷≠nil {A = A} p = subst distinguish p tt
  where
    distinguish : List A → Type
    distinguish nil     = ⊥
    distinguish (_ ∷ _) = ⊤
```
