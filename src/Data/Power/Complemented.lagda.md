<!--
```agda
{-# OPTIONS -vtactic.hlevel:10 #-}
open import 1Lab.Prelude

open import Data.Power
open import Data.Bool
open import Data.Dec
open import Data.Sum
```
-->

```agda
module Data.Power.Complemented where
```

# Complemented subobjects

A subobject $p : \bb{P}(A)$ of a type $A$ is called **complemented** if
there is a subobject $A \setminus p$ such that $A \sube p \cup (A
\setminus p)$^[where $A$ is regarded as the top element of its own
subobject lattice], and $(p \cap (A \setminus p)) \sube \emptyset$.
Because of $\bb{P}(A)$'s lattice structure, these containments suffice
to establish equality.

<!--
```agda
private variable
  ℓ : Level
  A : Type ℓ
  p q r : ℙ A
```
-->

```agda
is-complemented : ∀ {ℓ} {A : Type ℓ} (p : ℙ A) → Type _
is-complemented {A = A} p = Σ[ p⁻¹ ∈ ℙ A ]
  ((p ∩ p⁻¹ ⊆ minimal) × (maximal ⊆ p ∪ p⁻¹))
```

More conventionally, in constructive mathematics, we may say a subobject
is _decidable_ if its associated predicate is pointwise a decidable
type. It turns out that these conditions are equivalent: a subobject is
decidable if, and only if, it is complemented. It's immediate that
decidable subobjects are complemented: given a decision procedure $p$,
the fibres $p^*(\rm{yes}(x))$ and $p^*(\rm{no}(x))$ are disjoint and
their union is all of $A$.

```agda
is-decidable : ∀ {ℓ} {A : Type ℓ} (p : ℙ A) → Type _
is-decidable p = ∀ a → Dec (a ∈ p)

is-decidable→is-complemented : (p : ℙ A) → is-decidable p → is-complemented p
is-decidable→is-complemented {A = A} p dec = inv , intersection , union where
  inv : ℙ A
  inv x = el (¬ (x ∈ p)) hlevel!

  intersection : (p ∩ inv) ⊆ minimal
  intersection x (x∈p , x∉p) = x∉p x∈p

  union : maximal ⊆ (p ∪ inv)
  union x wit with dec x
  ... | yes x∈p = inc (inl x∈p)
  ... | no x∉p = inc (inr x∉p)
```

For the converse, since _decidability_ of a proposition is itself a
proposition, it suffices to assume we have an inhabitant of $(x \in p)
\coprod (x \in p^{-1})$. Assuming that $x \in p^{-1}$, we must show that
$x \notin p$: But by the definition of complemented subobject, the
intersection $(p \cap p^{-1})$ is empty.

```agda
is-complemented→is-decidable : (p : ℙ A) → is-complemented p → is-decidable p
is-complemented→is-decidable p (p⁻¹ , intersection , union) elt =
  ∥-∥-rec!  (λ { (inl x∈p)   → yes x∈p
             ; (inr x∈p⁻¹) → no λ x∈p → intersection elt (x∈p , x∈p⁻¹)
             })
    (union elt tt)
```

# Decidable subobject classifiers

In the same way that we have a (large) type $\rm{Prop}_\kappa$ of all
propositions of size $\kappa$, the decidable (complemented) subobjects
also have a classifying object: Any two-element type with decidable
equality! This can be seen as a local instance of excluded middle: the
complemented subobjects are precisely those satisfying $P \lor \neg P$,
and so they are classified by the "classical subobject classifier" $2 :=
\{ 0, 1 \}$.

```agda
decidable-subobject-classifier
  : (A → Bool) ≃ (Σ[ p ∈ ℙ A ] (is-decidable p))
decidable-subobject-classifier = eqv where
```

In much the same way that the subobject represented by a map $A \to
\rm{Prop}$ is the fibre over $\top$, the subobject represented by a map
$A \to 2$ is the fibre over $\mathtt{true}$. This is a decidable
subobject because $2$ has decidable equality.

```agda
  to : (A → Bool) → (Σ[ p ∈ ℙ A ] (is-decidable p))
  to map .fst x = el (map x ≡ true) hlevel!
  to map .snd p = Bool-elim (λ p → Dec (p ≡ true))
    (yes refl) (no (λ p → true≠false (sym p))) (map p)
```

Conversely, to each decidable subobject $p : \bb{P}(A)$ and element $x :
A$ we associate a boolean $b$ such that $(b \equiv \mathtt{true})$ if
and only if $x \in p$. Projecting the boolean and forgetting the
equivalence gives us a map $A \to 2$ associated with $p$, as desired;
The characterisation of $b$ serves to smoothen the proof that this
process is inverse to taking fibres over $\mathtt{true}$.

```agda
  from : (pr : Σ[ p ∈ ℙ A ] (is-decidable p)) (x : A)
       → (Σ[ b ∈ Bool ] ((b ≡ true) ≃ (x ∈ pr .fst)))
  from (p , dec) elt = Dec-elim (λ _ → Σ Bool (λ b → (b ≡ true) ≃ (elt ∈ p)))
    (λ y → true , prop-ext! (λ _ → y) (λ _ → refl))
    (λ x∉p → false , prop-ext!
      (λ p → absurd (true≠false (sym p)))
      (λ x → absurd (x∉p x)))
    (dec elt)

  eqv = Iso→Equiv λ where
    .fst → to
    .snd .is-iso.inv p x → from p x .fst
    .snd .is-iso.rinv pred → Σ-prop-path! $ ℙ-ext
      (λ x w → from pred x .snd .fst w)
      (λ x p → Equiv.from (from pred x .snd) p)
    .snd .is-iso.linv pred → funext λ x →
      Bool-elim (λ p → from (to λ _ → p) x .fst ≡ p) refl refl (pred x)
```
