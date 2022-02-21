```agda
open import 1Lab.Path
open import 1Lab.Type

open import Data.List

open import Relation.Order

module Relation.Order.Lexicographic where
```

# Lexicographic Orderings

A **Lexicographic Ordering** can be thought of as a generalization of
how we sort words.  For instance, if we were to look up "math" in the
dictionary, it would come before "mathematician", but after "cube". By
generalizing the order in question, we can get a notion of ordering for
any arbitrary list, instead of being restricted to lists of characters.

We define our ordering as an inductive type:

```agda
data Lex {ℓ ℓ'} {A : Type ℓ}
         (_≺_ : A → A → Type ℓ') : List A → List A → Type (ℓ ⊔ ℓ') where
  done     : ∀ {y ys}                      → Lex _≺_ []      (y ∷ ys)
  here     : ∀ {x xs y ys} → x ≺ y         → Lex _≺_ (x ∷ xs) (y ∷ ys)
  next     : ∀ {x xs ys}   → Lex _≺_ xs ys → Lex _≺_ (x ∷ xs) (x ∷ ys)
```


<!--
```agda
private
  variable
    ℓ ℓ'  : Level
    A     : Type ℓ
    _≺_   : A → A → Type ℓ'
    x y   : A
    xs ys : List A
```
-->

## Lemmas

In order to prove further results, we are going to need a handful of little lemmas.
First, let's show that if the head `xs` is greater than the head of `ys`, then
then `xs` cannot be smaller than `ys`:

```agda
lex-antisym-head : (x ≺ y → ⊥) → (x ≡ y → ⊥) → Lex _≺_ (x ∷ xs) (y ∷ ys) → ⊥
lex-antisym-head ¬x≺y ¬x≡y (here x≺y) = ¬x≺y x≺y
lex-antisym-head ¬x≺y ¬x≡y (next _)   = ¬x≡y refl
```

We can show something similar for the tails of lists as well!

```agda
lex-antisym-tail : (x ≺ y → ⊥) → (Lex _≺_ xs ys → ⊥) → Lex _≺_ (x ∷ xs) (y ∷ ys) → ⊥
lex-antisym-tail ¬x≺y ¬xs≺ys (here x≺y)   = ¬x≺y x≺y
lex-antisym-tail ¬x≺y ¬xs≺ys (next xs≺ys) = ¬xs≺ys xs≺ys
```

When we defined `next`, we specified it's type as `Lex _≺_ (x ∷ xs) (x ∷ ys)`.
We could have given it the type `Lex _≺_ (x ∷ xs) (y ∷ ys)` and required a proof
that `x ≡ y`, but that would mean a lot more `substs` when we go to use it.

However, it does mean that we need to prove the following lemma:

```agda
ap-∷-next : x ≡ y → Lex _≺_ xs ys → Lex _≺_ (x ∷ xs) (y ∷ ys)
ap-∷-next {x = x} {xs = xs} {ys = ys} x≡y xs≺ys =
  subst (λ z → Lex _ (x ∷ xs) (z ∷ ys)) x≡y (next xs≺ys)
```

## Trichotomy

Note that we have provided a _non-strict_ version! This means the
relation is irreflexive rather than reflexive. There's a good reason for
doing so: it makes the relation trichotomous.

This proof is a bit of a monster, so don't feel bad if it's
overwhelming! The core idea is that we can walk down both lists,
comparing each element as we go. Most of the code here is to convince
Agda that various situations are impossible.

```agda
lex-trichotomous : is-trichotomous _≺_ → is-trichotomous (Lex _≺_)
lex-trichotomous tri []      []      = eq (λ ()) refl (λ ())
lex-trichotomous tri []      (x ∷ ys) = lt done (∷≠[] ∘ sym) (λ ())
lex-trichotomous tri (x ∷ xs) []      = gt (λ ()) ∷≠[] done
lex-trichotomous tri (x ∷ xs) (y ∷ ys) with tri x y | lex-trichotomous tri xs ys
... | lt  x≺y ¬x≡y ¬y≺x | _ =
  lt (here x≺y) (¬x≡y ∘ ∷-head-inj) (lex-antisym-head ¬y≺x (¬x≡y ∘ sym))
... | gt ¬x≺y ¬x≡y  y≺x | _ =
  gt (lex-antisym-head ¬x≺y ¬x≡y) (¬x≡y ∘ ∷-head-inj) (here y≺x)
... | eq _     x≡y ¬y≺x | lt xs≺ys ¬xs≡ys ¬ys≺xs =
  lt (ap-∷-next x≡y xs≺ys) (¬xs≡ys ∘ ∷-tail-inj) (lex-antisym-tail ¬y≺x ¬ys≺xs)
... | eq ¬x≺y x≡y ¬y≺x  | eq ¬xs≺ys xs≡ys ¬ys≺xs =
  eq (lex-antisym-tail ¬x≺y ¬xs≺ys) (ap-∷ x≡y xs≡ys) (lex-antisym-tail ¬y≺x ¬ys≺xs)
... | eq ¬x≺y x≡y ¬y≺x  | gt ¬xs≺ys ¬xs≡ys ys≺xs =
  gt (lex-antisym-tail ¬x≺y ¬xs≺ys) (¬xs≡ys ∘ ∷-tail-inj) (ap-∷-next (sym x≡y) ys≺xs)
```
