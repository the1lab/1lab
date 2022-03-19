```agda
open import 1Lab.HLevel.Retracts
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

module Data.Set.Truncation where
```

# Set truncation

Exactly analogously to the construction of [propositional truncations],
we can construct the **set truncation** of a type, reflecting it onto
the subcategory of sets. Just like the propositional truncation is
constructed by attaching enough lines to a type to hide away all
information other than "is the type inhabited", the set truncation is
constructed by attaching enough square to kill off all homotopy groups.

[propositional truncations]: 1Lab.HIT.Truncation.html

```agda
data ∥_∥₀ {ℓ} (A : Type ℓ) : Type ℓ where
  inc    : A → ∥ A ∥₀
  squash : is-set ∥ A ∥₀
```

We begin by defining the induction principle. The (family of) type(s) we
map into must be a set, as required by the `squash`{.Agda} constructor.

```agda
∥-∥₀-elim : ∀ {ℓ ℓ'} {A : Type ℓ} {B : ∥ A ∥₀ → Type ℓ'}
          → (∀ x → is-set (B x))
          → (∀ x → B (inc x))
          → ∀ x → B x
∥-∥₀-elim Bset binc (inc x) = binc x
∥-∥₀-elim Bset binc (squash x y p q i j) =
  is-set→squarep (λ i j → Bset (squash x y p q i j))
    (λ _ → g x) (λ i → g (p i)) (λ i → g (q i)) (λ i → g y) i j
  where g = ∥-∥₀-elim Bset binc
```

The most interesting result is that, since the sets form a reflective
subcategory of types, it generates an idempotent monad. Indeed, as
required, the counit `inc`{.Agda} is an equivalence:

```agda
∥-∥₀-idempotent : ∀ {ℓ} {A : Type ℓ} → is-set A
                → is-equiv (inc {A = A})
∥-∥₀-idempotent {A = A} aset = is-iso→is-equiv (iso proj inc∘proj λ _ → refl)
  where
    proj : ∥ A ∥₀ → A
    proj (inc x) = x
    proj (squash x y p q i j) =
      aset (proj x) (proj y) (λ i → proj (p i)) (λ i → proj (q i)) i j

    inc∘proj : (x : ∥ A ∥₀) → inc (proj x) ≡ x
    inc∘proj = ∥-∥₀-elim (λ _ → is-prop→is-set (squash _ _)) λ _ → refl
```

The other definitions are entirely routine. We define functorial actions
of `∥_∥₀`{.Agda} directly, rather than using the eliminator, to avoid
using `is-set→squarep`{.Agda}.

```agda
∥-∥₀-map : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
        → (A → B) → ∥ A ∥₀ → ∥ B ∥₀
∥-∥₀-map f (inc x)        = inc (f x)
∥-∥₀-map f (squash x y p q i j) =
  squash (∥-∥₀-map f x) (∥-∥₀-map f y)
         (λ i → ∥-∥₀-map f (p i))
         (λ i → ∥-∥₀-map f (q i))
         i j

∥-∥₀-map₂ : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
          → (A → B → C) → ∥ A ∥₀ → ∥ B ∥₀ → ∥ C ∥₀
∥-∥₀-map₂ f (inc x) (inc y)        = inc (f x y)
∥-∥₀-map₂ f (squash x y p q i j) b =
  squash (∥-∥₀-map₂ f x b) (∥-∥₀-map₂ f y b)
         (λ i → ∥-∥₀-map₂ f (p i) b)
         (λ i → ∥-∥₀-map₂ f (q i) b)
         i j
∥-∥₀-map₂ f a (squash x y p q i j) =
  squash (∥-∥₀-map₂ f a x) (∥-∥₀-map₂ f a y)
         (λ i → ∥-∥₀-map₂ f a (p i))
         (λ i → ∥-∥₀-map₂ f a (q i))
         i j

∥-∥₀-elim₂ : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : ∥ A ∥₀ → ∥ B ∥₀ → Type ℓ''}
           → (∀ x y → is-set (C x y))
           → (∀ x y → C (inc x) (inc y))
           → ∀ x y → C x y
∥-∥₀-elim₂ Bset f = ∥-∥₀-elim (λ x → Π-is-hlevel 2 (Bset x))
  λ x → ∥-∥₀-elim (Bset (inc x)) (f x)

∥-∥₀-elim₃ : ∀ {ℓ ℓ' ℓ'' ℓ'''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
               {D : ∥ A ∥₀ → ∥ B ∥₀ → ∥ C ∥₀ → Type ℓ'''}
           → (∀ x y z → is-set (D x y z))
           → (∀ x y z → D (inc x) (inc y) (inc z))
           → ∀ x y z → D x y z
∥-∥₀-elim₃ Bset f = ∥-∥₀-elim₂ (λ x y → Π-is-hlevel 2 (Bset x y))
  λ x y → ∥-∥₀-elim (Bset (inc x) (inc y)) (f x y)
```
