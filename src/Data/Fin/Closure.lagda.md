<!--
```agda
open import 1Lab.Prelude

open import Data.Fin.Base
open import Data.Sum
```
-->

```agda
module Data.Fin.Closure where
```

<!--
```agda
private variable
  ℓ : Level
  A B C : Type ℓ
  k l m n : Nat
```
-->

# Closure of finite sets

In this module, we prove that the finite sets are closed under "typal
arithmetic": The initial and terminal objects are finite (they have 1
and 0 elements respectively), products of finite sets are finite,
coproducts of finite sets are finite, and functions between finite sets
are finite. Moreover, these operations all correspond to arithmetic
operations on the natural number indices: $[n] \uplus [m] = [n + m]$,
etc.

## Zero, one, successors

The finite set $[0]$ is an initial object, and the finite set $[1]$ is a
[[terminal object]]:

```agda
Finite-zero-is-initial : Fin 0 ≃ ⊥
Finite-zero-is-initial .fst ()
Finite-zero-is-initial .snd .is-eqv ()

Finite-one-is-contr : is-contr (Fin 1)
Finite-one-is-contr .centre = fzero
Finite-one-is-contr .paths fzero = refl
```

The successor operation on indices corresponds to taking coproducts with
the unit set.

```agda
Finite-successor : Fin (suc n) ≃ (⊤ ⊎ Fin n)
Finite-successor {n} = Iso→Equiv (f , iso g rinv linv) where
  f : Fin (suc n) → ⊤ ⊎ Fin n
  f fzero = inl tt
  f (fsuc x) = inr x

  g : ⊤ ⊎ Fin n → Fin (suc n)
  g (inr x) = fsuc x
  g (inl _) = fzero

  rinv : is-right-inverse g f
  rinv (inr _) = refl
  rinv (inl _) = refl

  linv : is-left-inverse g f
  linv fzero = refl
  linv (fsuc x) = refl
```

We can also phrase this equivalence in a particularly strong way, which
applies to dependent types over finite successor types:

```agda
Fin-suc-Π
  : ∀ {ℓ} {n} {A : Fin (suc n) → Type ℓ}
  → (∀ x → A x) ≃ (A fzero × (∀ x → A (fsuc x)))
Fin-suc-Π = Iso→Equiv λ where
  .fst f → f fzero , (λ x → f (fsuc x))

  .snd .is-iso.inv (z , f) fzero    → z
  .snd .is-iso.inv (z , f) (fsuc x) → f x

  .snd .is-iso.rinv x → refl

  .snd .is-iso.linv k i fzero    → k fzero
  .snd .is-iso.linv k i (fsuc n) → k (fsuc n)

Fin-suc-Σ
  : ∀ {ℓ} {n} {A : Fin (suc n) → Type ℓ}
  → Σ (Fin (suc n)) A ≃ (A fzero ⊎ Σ (Fin n) (A ∘ fsuc))
Fin-suc-Σ = Iso→Equiv λ where
  .fst (fzero , a) → inl a
  .fst (fsuc x , a) → inr (x , a)

  .snd .is-iso.inv (inl a) → fzero , a
  .snd .is-iso.inv (inr (x , a)) → fsuc x , a

  .snd .is-iso.rinv (inl _) → refl
  .snd .is-iso.rinv (inr _) → refl

  .snd .is-iso.linv (fzero , a) → refl
  .snd .is-iso.linv (fsuc x , a) → refl
```

## Addition

For binary coproducts, we prove the correspondence with addition in
steps, to make the proof clearer:

```agda
Finite-coproduct : (Fin n ⊎ Fin m) ≃ Fin (n + m)
Finite-coproduct {zero} {m}  =
  (Fin 0 ⊎ Fin m) ≃⟨ ⊎-apl Finite-zero-is-initial ⟩
  (⊥ ⊎ Fin m)     ≃⟨ ⊎-zerol ⟩
  Fin m           ≃∎
Finite-coproduct {suc n} {m} =
  (Fin (suc n) ⊎ Fin m) ≃⟨ ⊎-apl Finite-successor ⟩
  ((⊤ ⊎ Fin n) ⊎ Fin m) ≃⟨ ⊎-assoc ⟩
  (⊤ ⊎ (Fin n ⊎ Fin m)) ≃⟨ ⊎-apr (Finite-coproduct {n} {m}) ⟩
  (⊤ ⊎ Fin (n + m))     ≃⟨ Finite-successor e⁻¹ ⟩
  Fin (suc (n + m))     ≃∎
```

### Sums

We also have a correspondence between "coproducts" and "addition" in the
iterated case: If you have a family of finite types (represented by a
map to their cardinalities), the dependent _sum_ of that family is
equivalent to the iterated binary `sum`{.Agda} of the cardinalities:

```agda
sum : ∀ n → (Fin n → Nat) → Nat
sum zero f = zero
sum (suc n) f = f fzero + sum n (f ∘ fsuc)

Finite-sum : (B : Fin n → Nat) → Σ (Fin _) (Fin ∘ B) ≃ Fin (sum n B)
Finite-sum {zero} B .fst ()
Finite-sum {zero} B .snd .is-eqv ()
Finite-sum {suc n} B =
  Σ (Fin (suc n)) (Fin ∘ B)              ≃⟨ Fin-suc-Σ ⟩
  Fin (B 0) ⊎ Σ (Fin n) (Fin ∘ B ∘ fsuc) ≃⟨ ⊎-apr (Finite-sum (B ∘ fsuc)) ⟩
  Fin (B 0) ⊎ Fin (sum n (B ∘ fsuc))     ≃⟨ Finite-coproduct ⟩
  Fin (sum (suc n) B)                    ≃∎
```

## Multiplication

Recall (from middle school) that the product $n \times m$ is the same
thing as summing together $n$ copies of the number $m$. Correspondingly,
we can use the theorem above for general sums to establish the case of
binary products:

```agda
Finite-multiply : (Fin n × Fin m) ≃ Fin (n * m)
Finite-multiply {n} {m} =
  (Fin n × Fin m)       ≃⟨ Finite-sum (λ _ → m) ⟩
  Fin (sum n (λ _ → m)) ≃⟨ cast (sum≡* n m) , cast-is-equiv _ ⟩
  Fin (n * m)           ≃∎
  where
    sum≡* : ∀ n m → sum n (λ _ → m) ≡ n * m
    sum≡* zero m = refl
    sum≡* (suc n) m = ap (m +_) (sum≡* n m)
```

## Products

Similarly to the case for sums, the cardinality of a dependent *product* of
finite sets is the `product`{.Agda} of the cardinalities:

```agda
product : ∀ n → (Fin n → Nat) → Nat
product zero f = 1
product (suc n) f = f fzero * product n (f ∘ fsuc)

Finite-product : (B : Fin n → Nat) → (∀ x → Fin (B x)) ≃ Fin (product n B)
Finite-product {zero} B .fst _ = fzero
Finite-product {zero} B .snd = is-iso→is-equiv λ where
  .is-iso.inv _ ()
  .is-iso.rinv fzero → refl
  .is-iso.linv _ → funext λ ()
Finite-product {suc n} B =
  (∀ x → Fin (B x))                          ≃⟨ Fin-suc-Π ⟩
  Fin (B fzero) × (∀ x → Fin (B (fsuc x)))   ≃⟨ Σ-ap-snd (λ _ → Finite-product (B ∘ fsuc)) ⟩
  Fin (B fzero) × Fin (product n (B ∘ fsuc)) ≃⟨ Finite-multiply ⟩
  Fin (B fzero * product n (B ∘ fsuc))       ≃∎
```
