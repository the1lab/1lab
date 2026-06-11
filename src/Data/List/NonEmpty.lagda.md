---
description: |
  Nonempty lists.
---

<!--
```agda
open import 1Lab.Reflection.HLevel
open import 1Lab.HLevel.Closure
open import 1Lab.Truncation
open import 1Lab.Inductive
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

open import Data.List.Properties
open import Data.List.Base
open import Data.Dec.Base
open import Data.Sum.Base
```
-->

```agda
module Data.List.NonEmpty where
```

# Nonempty lists

<!--
```agda
private variable
  ℓ : Level
  A : Type ℓ
  xs : List A
```
-->

:::{.definition #nonempty-list}
A list $xs : \List{A}$ is **nonempty** if it can be written as $u \cons us$
for some $u : A$, $us : \List{A}$.
:::

We can encode this neatly in Mikan by using an indexed inductive type,
which makes it more amenable to proof automation.

```agda
data is-nonempty {ℓ} {A : Type ℓ} : (xs : List A) → Type ℓ where
  instance nonempty : ∀ {x xs} → is-nonempty (x ∷ xs)
```

Being nonempty is a proposition.

```agda
is-nonempty-is-prop
  : ∀ {xs : List A}
  → is-prop (is-nonempty xs)
is-nonempty-is-prop {xs = x ∷ xs} nonempty nonempty = refl
```

<!--
```agda
is-nonempty-is-contr
  : ∀ {x : A} {xs : List A}
  → is-contr (is-nonempty (x ∷ xs))
is-nonempty-is-contr = is-prop∙→is-contr is-nonempty-is-prop nonempty

instance
  H-Level-is-nonempty : ∀ {xs : List A} {n : Nat} → H-Level (is-nonempty xs) (suc n)
  H-Level-is-nonempty = prop-instance is-nonempty-is-prop
```
-->

A list is non-empty if and only if it is not equal to the empty list.

```agda
is-nonempty→not-empty
  : is-nonempty xs
  → xs ≠ []
is-nonempty→not-empty nonempty = ∷≠[]

not-empty→is-nonempty
  : xs ≠ []
  → is-nonempty xs
not-empty→is-nonempty {xs = []} xs≠[] = absurd (xs≠[] refl)
not-empty→is-nonempty {xs = x ∷ xs} xs≠[] = nonempty

is-nonempty≃not-empty : is-nonempty xs ≃ (xs ≠ [])
is-nonempty≃not-empty = prop-ext! is-nonempty→not-empty not-empty→is-nonempty
```

A list $xs$ is nonempty if and only if there is some $u : A$ and
$us : \List{A}$ such that $xs = u \cons us$.

```agda
is-nonempty≃∷
  : ∀ {xs : List A}
  → is-nonempty xs ≃ (Σ[ u ∈ A ] Σ[ us ∈ List A ] xs ≡ u ∷ us)
is-nonempty≃∷ {xs = []} =
  is-empty→≃
    (λ ())
    (λ (u , us , []=u∷us) → absurd ([]≠∷ []=u∷us))
is-nonempty≃∷ {xs = x ∷ xs} =
  is-contr→≃
    is-nonempty-is-contr
    (∷-singleton-is-contr x xs)
```

## Properties

We can decide if a list is nonempty by just checking if it is empty.

```agda
instance
  Dec-nonempty : ∀ {xs : List A} → Dec (is-nonempty xs)
  Dec-nonempty {xs = []} = no (λ ())
  Dec-nonempty {xs = x ∷ xs} = yes nonempty
```

## Closure properties

A list $xs \concat ys$ is nonempty if and only if
one of $xs$ or $ys$ is nonempty.

```agda
++-nonemptyl
  : ∀ (xs ys : List A)
  → is-nonempty xs
  → is-nonempty (xs ++ ys)
++-nonemptyl (x ∷ xs) ys ne = nonempty

++-nonemptyr
  : ∀ (xs ys : List A)
  → is-nonempty ys
  → is-nonempty (xs ++ ys)
++-nonemptyr [] ys ne = ne
++-nonemptyr (x ∷ xs) ys ne = nonempty

++-nonempty-split
  : ∀ (xs ys : List A)
  → is-nonempty (xs ++ ys)
  → is-nonempty xs ⊎ is-nonempty ys
++-nonempty-split [] ys ne = inr ne
++-nonempty-split (x ∷ xs) ys ne = inl nonempty

++-nonempty≃
  : ∀ (xs ys : List A)
  → is-nonempty (xs ++ ys) ≃ ∥ (is-nonempty xs ⊎ is-nonempty ys) ∥
++-nonempty≃ xs ys =
  prop-ext!
    (λ ne → inc (++-nonempty-split xs ys ne))
    (rec! [ ++-nonemptyl xs ys , ++-nonemptyr xs ys ])
```
