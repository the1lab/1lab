```agda
open import 1Lab.HLevel.Retracts
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

module 1Lab.HIT.Truncation where
```

# Propositional Truncation

Let $A$ be a type. The **propositional truncation** of $A$ is a type
which represents the [proposition] "A is inhabited". In MLTT,
propositional truncations can not be constructed without postulates,
even in the presence of impredicative prop. However, Cubical Agda
provides a tool to define them: _higher inductive types_.

[proposition]: agda://1Lab.HLevel#isProp

```agda
data ∥_∥ {ℓ : _} (A : Type ℓ) : Type ℓ where
  inc    : A → ∥ A ∥
  squash : (x y : ∥ A ∥) → x ≡ y
```

The two constructors that generate `∥_∥`{.Agda} state precisely that the
truncation is inhabited when `A` is (`inc`{.Agda}), and that it is a
proposition (`squash`{.Agda}).

```agda
isProp-∥-∥ : {ℓ : _} {A : Type ℓ} → isProp ∥ A ∥
isProp-∥-∥ = squash
```

The eliminator for `∥_∥`{.Agda} says that you can eliminate onto $P$
whenever it is a family of propositions, by providing a case for
`inc`{.Agda}.

```agda
∥-∥-elim : {ℓ ℓ' : _} {A : Type ℓ}
           {P : ∥ A ∥ → Type ℓ'}
         → ((x : _) → isProp (P x))
         → ((x : A) → P (inc x))
         → (x : ∥ A ∥) → P x
∥-∥-elim pprop incc (inc x) = incc x
∥-∥-elim pprop incc (squash x y i) =
  isProp→PathP (λ j → pprop (squash x y j)) (∥-∥-elim pprop incc x)
                                            (∥-∥-elim pprop incc y)
                                            i
```

The propositional truncation can be called the **free proposition** on a
type, because it satisfies the universal property that a left adjoint
would have. Specifically, let `B` be a proposition. We have:

```agda
∥-∥-univ : {ℓ : _} {A : Type ℓ} {B : Type ℓ}
         → isProp B → (∥ A ∥ → B) ≃ (A → B)
∥-∥-univ {A = A} {B = B} bprop = Iso→Equiv (inc' , iso rec (λ _ → refl) beta) where
  inc' : (x : ∥ A ∥ → B) → A → B
  inc' f x = f (inc x)

  rec : (f : A → B) → ∥ A ∥ → B
  rec f (inc x) = f x
  rec f (squash x y i) = bprop (rec f x) (rec f y) i

  beta : _
  beta f = funext (∥-∥-elim (λ _ → isProp→isSet bprop _ _) (λ _ → refl))
```

Using propositional truncation, we can define the **existential
quantifier** as a truncated `Σ`{.Agda}.

```agda
∃ : {a b : _} (A : Type a) (B : A → Type b) → Type _
∃ A B = ∥ Σ B ∥

syntax ∃ A (λ x → B) = ∃[ x ∈ A ] B
```

Note that if $P$ is a proposition, then its truncation does nothing:

```agda
isProp→equiv∥-∥ : {ℓ : _} {P : Type ℓ} → isProp P → P ≃ ∥ P ∥
isProp→equiv∥-∥ pprop = propExt pprop squash inc (∥-∥-elim (λ x → pprop) λ x → x)
```

In fact, we can take this as a definition of `isProp`{.Agda}:

```agda
isProp≃equiv∥-∥ : {ℓ : _} {P : Type ℓ}
               → isProp P ≃ (P ≃ ∥ P ∥)
isProp≃equiv∥-∥ {P = P} = propExt isProp-isProp eqv-prop isProp→equiv∥-∥ inv where
  inv : (P ≃ ∥ P ∥) → isProp P
  inv eqv = isHLevel-equiv 1 ((eqv e¯¹) .fst) ((eqv e¯¹) .snd) squash

  eqv-prop : isProp (P ≃ ∥ P ∥)
  eqv-prop x y = Σ-Path (λ i p → squash (x .fst p) (y .fst p) i)
                        (isProp-isEquiv _ _ _)
```
