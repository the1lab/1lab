```agda
open import 1Lab.Prim.Extension
open import 1Lab.Prim.Interval
open import 1Lab.Prim.Type

module 1Lab.Prim.Kan where
```

# Primitive: Kan operations

Using the machinery from the other `Prim` modules, we can define the Kan
operations: [transport] and [composition].

[transport]: 1Lab.Path.html#transport
[composition]: 1Lab.Path.html#composition

```agda
private module X where primitive
  primTransp : ∀ {ℓ} (A : (i : I) → Type (ℓ i)) (φ : I) (a : A i0) → A i1
  primHComp  : ∀ {ℓ} {A : Type ℓ} {φ : I} (u : ∀ i → Partial φ A) (a : A) → A
  primComp : ∀ {ℓ} (A : (i : I) → Type (ℓ i)) {φ : I} (u : ∀ i → Partial φ (A i)) (a : A i0) → A i1

open X public renaming (primTransp to transp)

hcomp
  : ∀ {ℓ} {A : Type ℓ} (φ : I)
  → (u : (i : I) → Partial (φ ∨ ~ i) A)
  → A
hcomp φ u = X.primHComp (λ { j (φ = i1) → u j 1=1 }) (u i0 1=1)

∂ : I → I
∂ i = i ∨ ~ i

comp
  : ∀ {ℓ : I → Level} (A : (i : I) → Type (ℓ i)) (φ : I)
  → (u : (i : I) → Partial (φ ∨ ~ i) (A i))
  → A i1
comp A φ u = X.primComp A (λ { j (φ = i1) → u j 1=1 }) (u i0 1=1)
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
