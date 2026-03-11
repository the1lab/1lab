<!--
```agda
open import 1Lab.Prelude

open import Data.Fin.Base

import Data.Vec.Base as Vec

open Vec
```
-->

```agda
module Data.Vec.Properties where
```

<!--
```agda
private variable
  ℓ : Level
  A B C : Type ℓ
  n k : Nat
  xs ys zs : Vec A n
```
-->

# Properties of vectors

In this module we show properties of vectors, including 
`the equivalence`{.Agda ident="Vec≃Fun"} between vectors of length $n$
and functions from `Fin n`{.Agda ident="Fin"}.

```agda
tabulate-lookup : (xs : Vec A n) → tabulate (lookup xs) ≡ xs
tabulate-lookup []       = refl
tabulate-lookup (x ∷ xs) = ap (x ∷_) (tabulate-lookup xs)

lookup-tabulate : (xs : Fin n → A) (i : Fin n) → lookup (tabulate xs) i ≡ xs i
lookup-tabulate xs i with fin-view i
... | zero  = refl
... | suc i = lookup-tabulate (xs ∘ fsuc) i

lookup-is-equiv : is-equiv (lookup {A = A} {n})
lookup-is-equiv = is-iso→is-equiv $
  iso tabulate (λ x → funext (lookup-tabulate x)) tabulate-lookup

Vec≃Fun : Vec A n ≃ (Fin n → A)
Vec≃Fun = lookup , lookup-is-equiv

module Lookup {ℓ} {A : Type ℓ} {n : Nat} = Equiv (Vec≃Fun {A = A} {n = n})
```

It follows from `Vec≃Fun`{.Agda} that `Vec`{.Agda} preserves [[h-Level]].

```agda
Vec-is-hlevel
  : ∀ {A : Type ℓ} {n} m
  → is-hlevel A m
  → is-hlevel (Vec A n) m
Vec-is-hlevel m Ahl = Equiv→is-hlevel m Vec≃Fun (fun-is-hlevel m Ahl)
```

<!--
```agda
instance
  H-Level-Vec : 
    ∀ {m} {A : Type ℓ} {n} → ⦃ H-Level A n ⦄
    → H-Level (Vec A m) n
  H-Level-Vec {n = n} .H-Level.has-hlevel = Vec-is-hlevel n (hlevel n)
```
-->

We define the following for building paths between vectors:

```agda
Vec-path
  : ∀ {A : Type ℓ} {n} {v w : Vec A (suc n)}
  → (head v ≡ head w) → (tail v ≡ tail w)
  → v ≡ w

Vec-path {v = _ ∷ _} {w = _ ∷ _} p q i = p i ∷ q i

[]-unique : ∀ {A : Type ℓ} → is-contr (Vec A 0)
[]-unique {A = A} = contr [] λ where [] → refl
```

## Functoriality {defines="functioriality-of-Vec"}

Here we show the functoriality of `Vec.map`{.Agda}.

```agda
map-lookup : ∀ (f : A → B) (xs : Vec A n) i → lookup (Vec.map f xs) i ≡ f (lookup xs i)
map-lookup _ _ i with fin-view i
map-lookup f (x ∷ xs) _ | zero  = refl
map-lookup f (x ∷ xs) _ | suc i = map-lookup f xs i

map-id : (xs : Vec A n) → Vec.map (λ x → x) xs ≡ xs
map-id xs = Lookup.injective₂ (funext λ i → map-lookup _ xs i) refl

map-comp
  : (xs : Vec A n) (f : A → B) (g : B → C)
  → Vec.map (λ x → g (f x)) xs ≡ Vec.map g (Vec.map f xs)
map-comp xs f g = Lookup.injective $ funext λ i →
  lookup (Vec.map (λ x → g (f x)) xs) i ≡⟨ map-lookup (λ x → g (f x)) xs i ⟩
  g (f (lookup xs i))                   ≡˘⟨ ap g (map-lookup f xs i) ⟩
  g (lookup (Vec.map f xs) i)           ≡˘⟨ map-lookup g (Vec.map f xs) i ⟩
  lookup (Vec.map g (Vec.map f xs)) i   ∎
```