<!--
```agda
open import 1Lab.Path.IdentitySystem
open import 1Lab.Reflection.HLevel
open import 1Lab.HLevel.Universe
open import 1Lab.HLevel.Closure
open import 1Lab.Type.Pointed
open import 1Lab.Truncation
open import 1Lab.Inductive
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type
```
-->

```agda
module Data.Set.Truncation where
```

# Set truncation {defines=set-truncation}

Exactly analogously to the construction of [[propositional truncations]],
we can construct the **set truncation** of a type, reflecting it onto
the subcategory of sets. Just like the propositional truncation is
constructed by attaching enough lines to a type to hide away all
information other than "is the type inhabited", the set truncation is
constructed by attaching enough square to kill off all homotopy groups.

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

∥-∥₀-rec
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → is-set B
  → (A → B) → ∥ A ∥₀ → B
∥-∥₀-rec bset f (inc x) = f x
∥-∥₀-rec bset f (squash x y p q i j) =
  bset (go x) (go y) (λ i → go (p i)) (λ i → go (q i)) i j
  where go = ∥-∥₀-rec bset f
```

<!--
```agda
instance
  Inductive-∥∥₀
    : ∀ {ℓ ℓ' ℓm} {A : Type ℓ} {P : ∥ A ∥₀ → Type ℓ'} ⦃ i : Inductive (∀ x → P (inc x)) ℓm ⦄
    → ⦃ _ : ∀ {x} → H-Level (P x) 2 ⦄
    → Inductive (∀ x → P x) ℓm
  Inductive-∥∥₀ ⦃ i ⦄ = record
    { methods = i .Inductive.methods
    ; from    = λ f → ∥-∥₀-elim (λ x → hlevel 2) (i .Inductive.from f)
    }
```
-->

The most interesting result is that, since the sets form a [[reflective
subcategory]] of types, the set-truncation is an idempotent monad.
Indeed, as required, the counit `inc`{.Agda} is an equivalence:

```agda
∥-∥₀-idempotent : ∀ {ℓ} {A : Type ℓ} → is-set A
                → is-equiv (inc {A = A})
∥-∥₀-idempotent {A = A} aset = is-iso→is-equiv (iso proj inc∘proj λ _ → refl)
  module ∥-∥₀-idempotent where
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
```

# Paths in the set truncation

```agda
∥-∥₀-path-equiv
  : ∀ {ℓ} {A : Type ℓ} {x y : A}
  → (∥_∥₀.inc x ≡ ∥_∥₀.inc y) ≃ ∥ x ≡ y ∥
∥-∥₀-path-equiv {A = A} =
  prop-ext (squash _ _) squash (encode _ _) (decode _ (inc _))
  where
    code : ∀ x (y : ∥ A ∥₀) → Prop _
    code x = ∥-∥₀-elim (λ y → hlevel 2) λ y → el ∥ x ≡ y ∥ squash

    encode : ∀ x y → inc x ≡ y → ∣ code x y ∣
    encode x y p = J (λ y p → ∣ code x y ∣) (inc refl) p

    decode : ∀ x y → ∣ code x y ∣ → inc x ≡ y
    decode x = ∥-∥₀-elim
      (λ _ → fun-is-hlevel 2 (is-prop→is-set (squash _ _)))
      λ _ → ∥-∥-rec (squash _ _) (ap inc)

module ∥-∥₀-path {ℓ} {A : Type ℓ} {x} {y}
  = Equiv (∥-∥₀-path-equiv {A = A} {x} {y})
```

<!--
```agda
instance
  H-Level-∥-∥₀ : ∀ {ℓ} {A : Type ℓ} {n : Nat} → H-Level ∥ A ∥₀ (2 + n)
  H-Level-∥-∥₀ {n = n} = basic-instance 2 squash

is-contr→∥-∥₀-is-contr : ∀ {ℓ} {A : Type ℓ} → is-contr A → is-contr ∥ A ∥₀
is-contr→∥-∥₀-is-contr h = Equiv→is-hlevel 0 ((_ , ∥-∥₀-idempotent (is-contr→is-set h)) e⁻¹) h

is-prop→∥-∥₀-is-prop : ∀ {ℓ} {A : Type ℓ} → is-prop A → is-prop ∥ A ∥₀
is-prop→∥-∥₀-is-prop h = Equiv→is-hlevel 1 ((_ , ∥-∥₀-idempotent (is-prop→is-set h)) e⁻¹) h

∥-∥₀-ap : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → A ≃ B → ∥ A ∥₀ ≃ ∥ B ∥₀
∥-∥₀-ap e .fst = ∥-∥₀-map (e .fst)
∥-∥₀-ap e .snd = is-iso→is-equiv λ where
  .is-iso.from → ∥-∥₀-map (Equiv.from e)
  .is-iso.rinv → elim! λ x → ap inc (Equiv.ε e x)
  .is-iso.linv → elim! λ x → ap inc (Equiv.η e x)

instance
  ∥-∥₀-homogeneous : ∀ {ℓ} {A : Type ℓ} → ⦃ _ : Homogeneous A ⦄ → Homogeneous ∥ A ∥₀
  ∥-∥₀-homogeneous {A = A} ⦃ h ⦄ {x} {y} =
    ∥-∥₀-elim {B = λ x → ∀ y → (∥ A ∥₀ , x) ≡ (∥ A ∥₀ , y)}
      (λ _ → Π-is-hlevel 2 λ _ → Type∙-path-is-hlevel 1)
      (λ x → ∥-∥₀-elim
        (λ _ → Type∙-path-is-hlevel 1)
        (λ y → let e , pt = path→equiv∙ h
               in ua∙ (∥-∥₀-ap e , ap ∥_∥₀.inc pt)))
      x y
```
-->
