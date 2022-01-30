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
data ∥_∥ {ℓ} (A : Type ℓ) : Type ℓ where
  inc    : A → ∥ A ∥
  squash : isProp ∥ A ∥
```

The two constructors that generate `∥_∥`{.Agda} state precisely that the
truncation is inhabited when `A` is (`inc`{.Agda}), and that it is a
proposition (`squash`{.Agda}).

```agda
isProp-∥-∥ : ∀ {ℓ} {A : Type ℓ} → isProp ∥ A ∥
isProp-∥-∥ = squash
```

The eliminator for `∥_∥`{.Agda} says that you can eliminate onto $P$
whenever it is a family of propositions, by providing a case for
`inc`{.Agda}.

```agda
∥-∥-elim : ∀ {ℓ ℓ'} {A : Type ℓ}
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

<!--
```agda
∥-∥-elim₂ : ∀ {ℓ ℓ₁ ℓ₂} {A : Type ℓ} {B : Type ℓ₁}
              {P : ∥ A ∥ → ∥ B ∥ → Type ℓ₂}
          → (∀ x y → isProp (P x y))
          → (∀ x y → P (inc x) (inc y))
          → ∀ x y → P x y
∥-∥-elim₂ {A = A} {B} {P} pprop work x y = go x y where
  go : ∀ x y → P x y
  go (inc x) (inc x₁) = work x x₁
  go (inc x) (squash y y₁ i) =
    isProp→PathP (λ i → pprop (inc x) (squash y y₁ i))
                 (go (inc x) y) (go (inc x) y₁) i
  go (squash x x₁ i) z =
    isProp→PathP (λ i → pprop (squash x x₁ i) z)
                  (go x z) (go x₁ z) i
```
-->

The propositional truncation can be called the **free proposition** on a
type, because it satisfies the universal property that a left adjoint
would have. Specifically, let `B` be a proposition. We have:

```agda
∥-∥-univ : ∀ {ℓ} {A : Type ℓ} {B : Type ℓ}
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

Furthermore, as required of a free construction, the propositional
truncation extends to a functor:

```agda
∥-∥-map : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
        → (A → B) → ∥ A ∥ → ∥ B ∥ 
∥-∥-map f (inc x)        = inc (f x)
∥-∥-map f (squash x y i) = squash (∥-∥-map f x) (∥-∥-map f y) i
```

<!--
```agda
∥-∥-map₂ : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
         → (A → B → C) → ∥ A ∥ → ∥ B ∥ → ∥ C ∥
∥-∥-map₂ f (inc x) (inc y)  = inc (f x y)
∥-∥-map₂ f (squash x y i) z = squash (∥-∥-map₂ f x z) (∥-∥-map₂ f y z) i
∥-∥-map₂ f x (squash y z i) = squash (∥-∥-map₂ f x y) (∥-∥-map₂ f x z) i

∥-∥-recSet : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
           → (f : A → B)
           → (∀ x y → f x ≡ f y)
           → isSet B
           → ∥ A ∥ → B
∥-∥-recSet {A = A} {B} f const b = go where
  go : ∥ A ∥ → B
  helper : ∀ x y → go x ≡ go y

  go (inc x) = f x
  go (squash x y i) = helper x y i

  helper (inc x) (inc y) = const x y
  helper (squash x y i) z =
    isSet→SquareP (λ _ _ → b) (helper x y) (helper x z) (helper y z) refl i
  helper x (squash y z i) =
    isSet→SquareP (λ _ _ → b) refl (helper x y) (helper x z) (helper y z) i
```
-->

Using the propositional truncation, we can define the **existential
quantifier** as a truncated `Σ`{.Agda}.

```agda
∃ : ∀ {a b} (A : Type a) (B : A → Type b) → Type _
∃ A B = ∥ Σ B ∥

syntax ∃ A (λ x → B) = ∃[ x ∈ A ] B
```

Note that if $P$ is already a proposition, then truncating it does
nothing:

```agda
isProp→equiv∥-∥ : ∀ {ℓ} {P : Type ℓ} → isProp P → P ≃ ∥ P ∥
isProp→equiv∥-∥ pprop = propExt pprop squash inc (∥-∥-elim (λ x → pprop) λ x → x)
```

In fact, an alternative definition of `isProp`{.Agda} is given by "being
equivalent to your own truncation":

```agda
isProp≃equiv∥-∥ : ∀ {ℓ} {P : Type ℓ}
               → isProp P ≃ (P ≃ ∥ P ∥)
isProp≃equiv∥-∥ {P = P} = propExt isProp-isProp eqv-prop isProp→equiv∥-∥ inv where
  inv : (P ≃ ∥ P ∥) → isProp P
  inv eqv = isHLevel-equiv 1 ((eqv e⁻¹) .fst) ((eqv e⁻¹) .snd) squash

  eqv-prop : isProp (P ≃ ∥ P ∥)
  eqv-prop x y = Σ-Path (λ i p → squash (x .fst p) (y .fst p) i)
                        (isProp-isEquiv _ _ _)
```
