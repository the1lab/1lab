```agda
open import 1Lab.Equiv.Fibrewise
open import 1Lab.HLevel.Retracts
open import 1Lab.Type.Dec
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

module 1Lab.HLevel.Sets where
```

<!--
```
private variable
  ℓ : Level
  A : Type ℓ
  x y : A
  p q : x ≡ y
```
-->

# Sets

A set, in HoTT, is a type that validates UIP (uniqueness of equality
proofs): Any two proofs of the same equality are equal. There are many
ways to prove that a type is a set. An equivalence that is well-known in
type theory is that UIP is equivalent to **Axiom K**:

```agda
hasK : Type ℓ → Typeω
hasK A = ∀ {ℓ} {x : A} (P : x ≡ x → Type ℓ) → P refl → (p : x ≡ x) → P p
```

A type is a Set if, and only if, it satisfies K:

```agda
K→isSet : hasK A → isSet A
K→isSet K x y =
  J (λ y p → (q : x ≡ y) → p ≡ q) (λ q → K (λ q → refl ≡ q) refl q)

isSet→K : isSet A → hasK A
isSet→K Aset {x = x} P prefl p = transport (λ i → P (Aset _ _ refl p i)) prefl
```

## Rijke's Theorem

Another useful way of showing that a type is a set is **Rijke's
theorem.**[^1] Suppose we have the following setup: `R` is a relation on
the elements of `A`; `R x y` is always a proposition; `R` is reflexive,
and `R x y` implies `x ≡ y`. Then we have that `(x ≡ y) ≃ R x y`, and by
closure of h-levels under equivalences, `A` is a set.

```agda
Rijke-equivalence : {R : A → A → Type ℓ}
                  → (refl : {x : A} → R x x)
                  → (toid : {x y : A} → R x y → x ≡ y)
                  → (isProp : {x y : A} → isProp (R x y))
                  → {x y : A} → isEquiv (toid {x} {y})
Rijke-equivalence {A = A} {R = R} refl toid isprop = total→equiv equiv where
  equiv : {x : A} → isEquiv (total {P = R x} {Q = x ≡_} (λ y → toid {x} {y}))
  equiv {x} = isContr→isEquiv
    (contr (x , refl) λ { (x , q) → Σ-Path (toid q) (isprop _ _) })
    (contr (x , λ i → x) λ { (x , q) i → q i , λ j → q (i ∧ j) })
```

By the characterisation of [fibrewise equivalences], it suffices to show
that `total toid` induces an equivalence of total spaces. By J, the
total space of `x ≡_` is contractible; By `toid`, and the fact that `R`
is propositional, we can contract the total space of `R x` to `(x ,
refl)`.

[fibrewise equivalences]: agda://1Lab.Equiv.Fibrewise

```agda
Rijke-isSet : {R : A → A → Type ℓ}
            → (refl : {x : A} → R x x)
            → (toid : {x y : A} → R x y → x ≡ y)
            → (isProp : {x y : A} → isProp (R x y))
            → isSet A
Rijke-isSet refl toid isprop x y =
  isHLevel-equiv 1
    toid (Rijke-equivalence refl toid isprop) isprop
```

## Hedberg's Theorem

As a consequence of Rijke's theorem, we get that any type for which we
can conclude equality from a double-negated equality is a set:

```agda
¬¬-separated→isSet : ({x y : A} → ((x ≡ y → ⊥) → ⊥) → x ≡ y)
                   → isSet A
¬¬-separated→isSet stable = Rijke-isSet (λ x → x refl) stable prop where
  prop : {x y : A} → isProp ((x ≡ y → ⊥) → ⊥)
  prop p q i x = absurd {A = p x ≡ q x} (p x) i
```

From this we get **Hedberg's theorem**: Any type with decidable equality
is a set.

```agda
Discrete→isSet : Discrete A → isSet A
Discrete→isSet {A = A} dec = ¬¬-separated→isSet sep where
  sep : {x y : A} → ((x ≡ y → ⊥) → ⊥) → x ≡ y
  sep {x = x} {y = y} ¬¬p with dec x y
  ... | yes p = p
  ... | no ¬p = absurd (¬¬p ¬p)
```

[^1]: Named after a Twitter mutual of mine :)
