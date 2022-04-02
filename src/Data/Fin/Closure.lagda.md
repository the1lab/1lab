```agda
open import 1Lab.Prelude

open import Agda.Builtin.Maybe

open import Data.Fin.Base
open import Data.Sum

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
terminal object:

```agda
Finite-zero-is-initial : Fin 0 ≃ ⊥
Finite-zero-is-initial .fst ()
Finite-zero-is-initial .snd .is-eqv ()

Finite-one-is-contr : is-contr (Fin 1)
Finite-one-is-contr .centre = fzero
Finite-one-is-contr .paths fzero = refl
```

The successor operation on indices corresponds to taking coproducts with
the unit set:

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
```

In this case, the isomorphism is constructed directly:

```agda
Finite-sum : (B : Fin n → Nat) → Σ (Fin ∘ B) ≃ Fin (sum n B)
Finite-sum {zero} B .fst ()
Finite-sum {zero} B .snd .is-eqv ()
Finite-sum {suc n} B =
  Finite-coproduct .fst ∘ f ,
  ∙-is-equiv (is-iso→is-equiv f-iso) (Finite-coproduct .snd)
    where
      rec = Finite-sum (B ∘ fsuc)

      f : Σ (Fin ∘ B) → Fin (B fzero) ⊎ Fin (sum n (B ∘ fsuc))
      f (fzero , x) = inl x
      f (fsuc x , y) = inr (rec .fst (x , y))

      f-iso : is-iso f
      f-iso .is-iso.inv (inl x) = fzero , x
      f-iso .is-iso.inv (inr x) with equiv→inverse (rec .snd) x
      ... | x , y = fsuc x , y

      f-iso .is-iso.rinv (inl x) = refl
      f-iso .is-iso.rinv (inr x) = ap inr (equiv→section (rec .snd) _)

      f-iso .is-iso.linv (fzero , x) = refl
      f-iso .is-iso.linv (fsuc x , y) =
        Σ-pathp
          (ap (fsuc ∘ fst) (equiv→retraction (rec .snd) _))
          (ap snd (equiv→retraction (rec .snd) _))
```

## Multiplication

Recall (from middle school) that the product $n \times m$ is the same
thing as summing together $n$ copies of the number $m$. Correspondingly,
we can use the theorem above for general sums to establish the case of
binary products:

```agda
Finite-product : (Fin n × Fin m) ≃ Fin (n * m)
Finite-product {n} {m} =
  (Fin n × Fin m)       ≃⟨ Finite-sum (λ _ → m) ⟩
  Fin (sum n (λ _ → m)) ≃⟨ cast (sum≡* n m) , cast-is-equiv _ ⟩
  Fin (n * m)           ≃∎
  where
    sum≡* : ∀ n m → sum n (λ _ → m) ≡ n * m
    sum≡* zero m = refl
    sum≡* (suc n) m = ap (m +_) (sum≡* n m)
```
