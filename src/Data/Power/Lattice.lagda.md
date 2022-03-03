```agda
open import 1Lab.Prelude

open import Algebra.Semilattice
open import Algebra.Semigroup
open import Algebra.Lattice
open import Algebra.Magma

open import Cat.Thin
open import Cat.Thin

open import Data.Power
open import Data.Sum

module Data.Power.Lattice where
```

# Lattice of Subobjects

The `power set`{.Agda ident=ℙ} of a type $X$ can be organised into a
_lattice_, where the meets of two subsets are given by their
intersection $x \cap y$ and the joins are given by their union $x \cup
y$. Furthermore, we prove that the ordering induced by this lattice is
the same as the subset inclusion ordering.

First, we take a detour to define the structure of `ℙ` as a
`Poset`{.Agda} ordered by `subset inclusion`{.Agda ident=_⊆_}. This
packages up the reflexivity and transitivity of the subset relation.
Antisymmetry for this relation is exactly the `principle of
extensionality for subsets`{.Agda ident=ℙ-ext}.

```agda
ℙ⊆ : ∀ {ℓ} → Type ℓ → Poset _ _
ℙ⊆ A =
  make-poset {A = ℙ A} {R = _⊆_}
    (λ _ x → x)
    (λ x⊆y y⊆z a a∈x → y⊆z a (x⊆y a a∈x))
    ℙ-ext
    λ {x} {y} → Π-is-hlevel 1 λ x → fun-is-hlevel 1 (y x .snd)
```

Back on track, we equip intersection of subsets with the structure of a
semilattice:

```agda
∩-semilattice : ∀ {ℓ} {X : Type ℓ} → is-semilattice (_∩_ {X = X})
∩-semilattice = r where
  open is-semilattice
  open is-semigroup

  r : is-semilattice _
  r .has-is-semigroup .has-is-magma .has-is-set = ℙ-is-set
  r .has-is-semigroup .associative =
    ℙ-ext (λ { x (a , b , c) → (a , b) , c })
          (λ { x ((a , b) , c) → a , b , c })

  r .commutative =
    ℙ-ext (λ { x (a , b) → b , a }) (λ { x (a , b) → b , a })

  r .idempotent =
    ℙ-ext (λ { x (y , _) → y }) (λ { x y → y , y })
```

We then equip union of subsets with the structure of a semilattice. This
direction of the proof is a lot more annoying because of the truncation
in `_∪_`{.Agda}, but it is essentially shuffling sums around:

```agda
∪-semilattice : ∀ {ℓ} {X : Type ℓ} → is-semilattice (_∪_ {X = X})
∪-semilattice = r where
  open is-semilattice
  open is-semigroup
```

To show that subset union is associative, we must "shuffle" coproducts
`(x ∈ X) ⊎ (x ∈ Y ⊎ x ∈ Z)` to `(x ∈ X ⊎ x ∈ Y) ⊎ (x ∈ Z)`, which would
be simple enough to do with pattern matching. The complication arises
because in reality we're shuffling `P ⊎ ∥ Q ⊎ R ∥` into `∥ P ⊎ Q ∥ ⊎ R`
and vice-versa, so we must use `∥-∥-elim`{.Agda} to get at the
underlying coproduct, even though all of `P`, `Q`, and `R` are
propositions.

```agda
  r : is-semilattice _
  r .has-is-semigroup .has-is-magma .has-is-set = ℙ-is-set
  r .has-is-semigroup .associative =
    ℙ-ext (λ _ → ∥-∥-elim (λ _ → squash)
                 λ { (inl x) → inc (inl (inc (inl x)))
                   ; (inr x) → ∥-∥-elim (λ _ → squash)
                               (λ { (inl y) → inc (inl (inc (inr y)))
                                  ; (inr y) → inc (inr y) }) x
                   })
          (λ _ → ∥-∥-elim (λ _ → squash)
                 λ { (inl x) → ∥-∥-elim (λ _ → squash)
                               (λ { (inl y) → inc (inl y)
                                  ; (inr y) → inc (inr (inc (inl y))) }) x
                   ; (inr x) → inc (inr (inc (inr x)))
                   })
```

For commutativity, since we are changing `∥ (x ∈ X) ⊎ (x ∈ Y) ∥` to `∥
(x ∈ Y) ⊎ (x ∈ X) ∥`, ‵∥-∥-map`{.Agda} suffices - there is no need to
reassociate _truncations_.

```agda
  r .commutative =
    ℙ-ext (λ _ → ∥-∥-map λ { (inl x) → inr x
                           ; (inr x) → inl x })
          (λ _ → ∥-∥-map λ { (inl x) → inr x
                           ; (inr x) → inl x })
```

For idempotence, we must show that `x ∈ X ≃ ∥ (x ∈ X) ⊎ (x ∈ X) ∥`.
Since `x ∈ X` is a proposition, we can eliminate from a truncation to
it, at which point either branch will do just fine. In the other
direction, we inject it into the left summand for definiteness.

```agda
  r .idempotent {x = X} =
    ℙ-ext (λ _ → ∥-∥-elim (λ _ → X _ .snd)
                 (λ { (inl x) → x
                    ; (inr x) → x }))
          λ _ x → inc (inl x)
```

We must now show that intersections absorb unions, and that unions
absorb intersections.

```agda
∩-absorbs-∪ : ∀ {ℓ} {A : Type ℓ} {X Y : ℙ A} → X ∩ (X ∪ Y) ≡ X
∩-absorbs-∪ = ℙ-ext (λ { _ (a , _) → a }) λ _ x → x , inc (inl x)

∪-absorbs-∩ : ∀ {ℓ} {A : Type ℓ} {X Y : ℙ A} → X ∪ (X ∩ Y) ≡ X
∪-absorbs-∩ {X = X} {Y = Y} =
  ℙ-ext (λ _ → ∥-∥-elim (λ x → X _ .snd)
               (λ { (inl x∈X) → x∈X
                  ; (inr (x∈X , x∈Y)) → x∈X }))
        λ _ x∈X → inc (inl x∈X) 
```

This means that $\mathbb{P}(X), \cap, \cup$ assemble into a lattice,
which we call `Power`{.Agda}:

```agda
open Lattice-on
open is-lattice

Power : ∀ {ℓ} (X : Type ℓ) → Lattice-on (ℙ X)
Power X ._L∧_ = _∩_
Power X ._L∨_ = _∪_
Power X .has-is-lattice .has-meets = ∩-semilattice
Power X .has-is-lattice .has-joins = ∪-semilattice
Power X .has-is-lattice .∧-absorbs-∨ {y = y} = ∩-absorbs-∪ {Y = y}
Power X .has-is-lattice .∨-absorbs-∧ {y = y} = ∪-absorbs-∩ {Y = y}
```

It remains to show that the covariant ordering induced by the
`Power`{.Agda} lattice is the same as `ℙ⊆`{.Agda}. For this we show that
$(x ⊆ y) \leftrightarrow (x ≡ (x ∩ y))$.

```agda
subset-∩ : ∀ {ℓ} {A : Type ℓ} {X Y : ℙ A} → (X ⊆ Y) ≃ (X ≡ (X ∩ Y))
subset-∩ {X = X} {Y = Y} =
  prop-ext
    (Π-is-hlevel 1 λ x → fun-is-hlevel 1 (Y x .snd))
    (ℙ-is-set _ _)
    to from
  where
```

In the "if" direction, suppose that $X \subseteq Y$. We show that $X ∩
Y$ intersect to $X$ by extensionality of power sets: If $x \in X$ and $X
\subseteq Y$ then $x \in Y$, so $x \in (X \cap Y)$. Conversely, if $x
\in (X \cap Y)$, then $x \in X$, so we are done.

```agda
    to : X ⊆ Y → X ≡ (X ∩ Y)
    to x⊆y = ℙ-ext (λ x x∈X → x∈X , x⊆y x x∈X)
                   (λ x x∈X∩Y → x∈X∩Y .fst)
```

In the "only if" direction, suppose that $X = (X \cap Y)$. If $x \in X$,
then $x \in (X \cap Y)$ (by the assumed equality), so $x \in Y$, hence
$X \subseteq Y$, so we are done.

```agda
    from : (X ≡ (X ∩ Y)) → X ⊆ Y
    from path x x∈X = transport (ap fst (happly path x)) x∈X .snd
```
