```agda
open import 1Lab.Prim.Extension
open import 1Lab.Prim.Interval
open import 1Lab.Prim.Type

module 1Lab.Prim.Kan where
```

# Primitive: Kan operations

Using the machinery from the other `Prim` modules, we can define the Kan
operations: [transport] and [composition].

[transport]: 1Lab.Path.html#Transport
[composition]: 1Lab.Path.html#Composition

```agda
private module X where primitive
  primTransp : ∀ {ℓ} (A : (i : I) → Type (ℓ i)) (φ : I) (a : A i0) → A i1
  primHComp  : ∀ {ℓ} {A : Type ℓ} {φ : I} (u : ∀ i → Partial φ A) (a : A) → A
  primComp : ∀ {ℓ} (A : (i : I) → Type (ℓ i)) {φ : I} (u : ∀ i → Partial φ (A i)) (a : A i0) → A i1

open X public renaming (primTransp to transp ; primHComp to hcomp ; primComp to comp)
```

We also define the type of dependent paths, and of non-dependent paths.

```agda
postulate
  PathP : ∀ {ℓ} (A : I → Type ℓ) → A i0 → A i1 → Type ℓ

{-# BUILTIN PATHP PathP #-}

infix 4 _≡_

Path : ∀ {ℓ} (A : Type ℓ) → A → A → Type ℓ
Path A = PathP (λ i → A)

_≡_ : ∀ {ℓ} {A : Type ℓ} → A → A → Type ℓ
_≡_ {A = A} = PathP (λ i → A)

{-# BUILTIN PATH _≡_ #-}
```
