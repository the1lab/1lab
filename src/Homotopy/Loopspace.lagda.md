<!--
```agda
open import 1Lab.Equiv.Pointed
open import 1Lab.Prelude

open import Homotopy.Conjugation
```
-->

```agda
module Homotopy.Loopspace where
```

<!--
```agda
private variable
  ℓ ℓ'  : Level
  A B C : Type∙ ℓ
```
-->

# Loop spaces {defines="loop-space"}

Given a `pointed type`{.Agda ident=Type∙} $(A, a)$ we refer to the type
$a = a$ as the **loop space of $A$**, and refer to it in short as
$\Omega A$. Since we always have $\refl : a = a$, $\Omega A$ is _itself_
a pointed type, this construction can be iterated, resulting in the
higher loop spaces $\Omega^n A$.

```agda
Ω¹ : Type∙ ℓ → Type∙ ℓ
Ω¹ (A , a₀) = Path A a₀ a₀ , refl

Ωⁿ : Nat → Type∙ ℓ → Type∙ ℓ
Ωⁿ zero    A = A
Ωⁿ (suc n) A = Ω¹ (Ωⁿ n A)
```

```agda
Ω¹-map : (A →∙ B) → Ω¹ A →∙ Ω¹ B
Ω¹-map (f , pt) .fst α = conj pt (ap f α)
Ω¹-map (f , pt) .snd = conj-of-refl pt

Ω¹-map-id : Ω¹-map {A = A} id∙ ≡ id∙
Ω¹-map-id = homogeneous-funext∙ (λ _ → conj-refl _)

Ω¹-map-∘ : (f : B →∙ C) (g : A →∙ B) → Ω¹-map f ∘∙ Ω¹-map g ≡ Ω¹-map (f ∘∙ g)
Ω¹-map-∘ (f , f*) (g , g*) = homogeneous-funext∙ λ α →
  ap (conj f*) (ap-conj f g* (ap g α)) ∙ conj-∙ _ _ _

Ω¹-ap : A ≃∙ B → Ω¹ A ≃∙ Ω¹ B
Ω¹-ap f .fst .fst = Ω¹-map (Equiv∙.to∙ f) .fst
Ω¹-ap f .fst .snd = ∘-is-equiv (conj-is-equiv (f .snd)) (ap-equiv (f .fst) .snd)
Ω¹-ap f .snd = Ω¹-map (Equiv∙.to∙ f) .snd

opaque
  unfolding conj conj-refl conj-of-refl

  Ω¹-map-zero : Ω¹-map (zero∙ {A = A} {B = B}) ≡ zero∙
  Ω¹-map-zero {B = B} = Σ-pathp (funext λ a → conj-refl _) conj-refl-square

Ω¹-map∙ : Maps∙ A B →∙ Maps∙ (Ω¹ A) (Ω¹ B)
Ω¹-map∙ .fst = Ω¹-map
Ω¹-map∙ .snd = Ω¹-map-zero

Ωⁿ-map
  : ∀ {ℓ ℓ'} {A : Type∙ ℓ} {B : Type∙ ℓ'} n (e : A →∙ B)
  → Ωⁿ n A →∙ Ωⁿ n B
Ωⁿ-map zero    f = f
Ωⁿ-map (suc n) f = Ω¹-map (Ωⁿ-map n f)

Ωⁿ-map-∘ : ∀ n → (f : B →∙ C) (g : A →∙ B) → Ωⁿ-map n f ∘∙ Ωⁿ-map n g ≡ Ωⁿ-map n (f ∘∙ g)
Ωⁿ-map-∘ zero    f g = refl
Ωⁿ-map-∘ (suc n) f g = Ω¹-map-∘ (Ωⁿ-map n f) (Ωⁿ-map n g) ∙ ap Ω¹-map (Ωⁿ-map-∘ n f g)

Ωⁿ-map-equiv : ∀ n (f : A →∙ B) → is-equiv (f .fst) → is-equiv (Ωⁿ-map n f .fst)
Ωⁿ-map-equiv zero    f e = e
Ωⁿ-map-equiv (suc n) f e = Ω¹-ap ((_ , Ωⁿ-map-equiv n f e) , _) .fst .snd

Ωⁿ-map-∙ : ∀ n (f : A →∙ B) p q → Ωⁿ-map (suc n) f · (p ∙ q) ≡ Ωⁿ-map (suc n) f · p ∙ Ωⁿ-map (suc n) f · q
Ωⁿ-map-∙ n f p q using f' , f'* ← Ωⁿ-map n f = ap (conj f'*) (ap-∙ f' _ _) ∙ conj-of-∙ f'* _ _

Ωⁿ-map-zero : ∀ n → Ωⁿ-map n (zero∙ {A = A} {B = B}) ≡ zero∙
Ωⁿ-map-zero zero    = refl
Ωⁿ-map-zero (suc n) = ap Ω¹-map (Ωⁿ-map-zero n) ∙ Ω¹-map-zero

Ωⁿ-map∙ : ∀ n → Maps∙ A B →∙ Maps∙ (Ωⁿ n A) (Ωⁿ n B)
Ωⁿ-map∙ n .fst = Ωⁿ-map n
Ωⁿ-map∙ n .snd = Ωⁿ-map-zero n

Ω-Maps∙ : Ω¹ (Maps∙ A B) ≃∙ Maps∙ A (Ω¹ B)
Ω-Maps∙ .fst = twist , eqv where
  twist : Ω¹ (Maps∙ _ _) .fst → Maps∙ _ (Ω¹ _) .fst
  twist p .fst x i = p i .fst x
  twist p .snd i j = p j .snd i

  eqv : is-equiv twist
  eqv = is-iso→is-equiv λ where
    .is-iso.from f i → (λ x → f .fst x i) , (λ j → f .snd j i)
    .is-iso.rinv x → refl
    .is-iso.linv x → refl
Ω-Maps∙ {B = B} .snd i = (λ x j → B .snd) , λ j k → B .snd

Ω-map-∙ : ∀ (f : A →∙ B) p q → Ω¹-map f · (p ∙ q) ≡ Ω¹-map f · p ∙ Ω¹-map f · q
Ω-map-∙ = Ωⁿ-map-∙ 0

Ωⁿ-ap
  : ∀ {ℓ ℓ'} {A : Type∙ ℓ} {B : Type∙ ℓ'} n (e : A ≃∙ B)
  → Ωⁿ n A ≃∙ Ωⁿ n B
Ωⁿ-ap {A = A} {B = B} n e∙@((e , eq) , p) = record
  { fst = e' .fst , Ωⁿ-map-equiv n (e , p) eq
  ; snd = e' .snd
  }
  where e' = Ωⁿ-map n (e , p)

Ωⁿ-map-id : ∀ n → Ωⁿ-map {A = A} n id∙ ≡ id∙
Ωⁿ-map-id zero    = refl
Ωⁿ-map-id (suc n) = ap Ω¹-map (Ωⁿ-map-id n) ∙ Ω¹-map-id

Ωⁿ-ap-id : ∀ n → Ωⁿ-ap {A = A} n id≃∙ ≡ id≃∙
Ωⁿ-ap-id n with p ← Ωⁿ-map-id n = Σ-pathp (Σ-prop-path! (ap fst p)) (ap snd p)

Ωⁿ-suc : ∀ (A : Type∙ ℓ) n → Ωⁿ (suc n) A ≃∙ Ωⁿ n (Ωⁿ 1 A)
Ωⁿ-suc A zero    = id≃ , refl
Ωⁿ-suc A (suc n) = Ωⁿ-ap 1 (Ωⁿ-suc A n)

abstract
  Ωⁿ-sucP : ∀ (A : Type∙ ℓ) n → Ωⁿ (suc n) A ≡ Ωⁿ n (Ωⁿ 1 A)
  Ωⁿ-sucP A zero    = refl
  Ωⁿ-sucP A (suc n) = ap Ω¹ (Ωⁿ-sucP A n)

  Ωⁿ-suc-coh : ∀ {A : Type∙ ℓ} n → ua∙ (Ωⁿ-suc A n) ≡ Ωⁿ-sucP A n
  Ωⁿ-suc-coh {A = A , a₀} zero    = ua∙-id-equiv
  Ωⁿ-suc-coh {A = A , a₀} (suc n) =
    ua∙ (Ωⁿ-ap 1 (Ωⁿ-suc (A , a₀) n))
      ≡⟨ Equiv∙J (λ B e → ua∙ (Ωⁿ-ap 1 e) ≡ ap Ω¹ (ua∙ e))
          (ap ua∙ (Ωⁿ-ap-id 1) ∙ ua∙-id-equiv ∙ sym (ap (ap Ω¹) ua∙-id-equiv))
          (Ωⁿ-suc (A , a₀) n) ⟩
    ap Ω¹ (ua∙ (Ωⁿ-suc (A , a₀) n))
      ≡⟨ ap (ap Ω¹) (Ωⁿ-suc-coh n) ⟩
    ap Ω¹ (Ωⁿ-sucP (A , a₀) n)
      ∎

  Ω-suc-naturalP
    : ∀ {A : Type∙ ℓ} {B : Type∙ ℓ'} n (f : A →∙ B)
    → PathP (λ i → ua∙ (Ωⁿ-suc A n) i →∙ ua∙ (Ωⁿ-suc B n) i)
      (Ωⁿ-map (suc n) f)
      (Ωⁿ-map n (Ω¹-map f))
  Ω-suc-naturalP {A = _ , a₀} {B = _ , b₀} zero f =
    transport
      (λ i → PathP
        (λ j → ua∙-id-equiv {A = a₀ ≡ a₀ , refl} (~ i) j
            →∙ ua∙-id-equiv {A = b₀ ≡ b₀ , refl} (~ i) j)
        (Ω¹-map f) (Ω¹-map f)) refl
  Ω-suc-naturalP {A = A} {B = B} (suc n) f =
    let
      coh : (A : Type∙ ℓ) → ap Ω¹ (ua∙ (Ωⁿ-suc A n)) ≡ ua∙ (Ωⁿ-suc A (suc n))
      coh A = sym (Ωⁿ-suc-coh (suc n) ∙ ap (ap Ω¹) (sym (Ωⁿ-suc-coh n)))
    in transport
      (λ i → PathP
        (λ j → coh A i j →∙ coh B i j)
        (Ω¹-map (Ω¹-map (Ωⁿ-map n f)))
        (Ω¹-map (Ωⁿ-map n (Ω¹-map f))))
      (apd (λ i → Ω¹-map) (Ω-suc-naturalP n f))

  Ω-suc-natural
    : ∀ {A : Type∙ ℓ} {B : Type∙ ℓ'} n (f : A →∙ B)
    → Equiv∙.to∙ (Ωⁿ-suc B n) ∘∙ Ωⁿ-map (suc n) f ∘∙ Equiv∙.from∙ (Ωⁿ-suc A n)
    ≡ Ωⁿ-map n (Ω¹-map f)
  Ω-suc-natural {A = A} {B = B} n f =
    let
      instance _ : Homogeneous (Ωⁿ n (Ωⁿ 1 B) .fst)
      _ = subst Homogeneous (ap fst (Ωⁿ-sucP B n)) auto
    in homogeneous-funext∙ λ x i → unglue (
      Ω-suc-naturalP {A = A} {B = B} n f i .fst
        (attach (∂ i) (λ { (i = i0) → _ ; (i = i1) → _ })
          (inS (Equiv.ε (Ωⁿ-suc A n .fst) x i))))
```
