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

```agda
tabulate-lookup : (xs : Vec A n) → tabulate (lookup xs) ≡ xs
tabulate-lookup []       = refl
tabulate-lookup (x ∷ xs) = ap (x ∷_) (tabulate-lookup xs)

lookup-tabulate : (xs : Fin n → A) (i : Fin n) → lookup (tabulate xs) i ≡ xs i
lookup-tabulate xs fzero = refl
lookup-tabulate xs (fsuc i) = lookup-tabulate (λ x → xs (fsuc x)) i

lookup-is-equiv : is-equiv (lookup {A = A} {n})
lookup-is-equiv = is-iso→is-equiv $
  iso tabulate (λ x → funext (lookup-tabulate x)) tabulate-lookup

module Lookup {ℓ} {A : Type ℓ} {n : Nat} = Equiv (lookup {A = A} {n} , lookup-is-equiv)

map-lookup : ∀ (f : A → B) (xs : Vec A n) i → lookup (Vec.map f xs) i ≡ f (lookup xs i)
map-lookup f (x ∷ xs) fzero    = refl
map-lookup f (x ∷ xs) (fsuc i) = map-lookup f xs i

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
