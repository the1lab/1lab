```agda
open import Data.List

open import Theories.Signature

open import 1Lab.Prelude

module Theories.Data.Spine {ℓ ℓ′} (Sg : Sign ℓ) (Tm : ∣ Sign.Sort Sg ∣ → Type ℓ′) where

open Sign Sg
```

# Spines

When defining terms over a signature, we want to ensure that all operator
applications are fully applied. This holds even when defining λ-calculi;
we prefer to write `λ y → x + y` instead of `x +_` in the core syntax.
This makes various theory inclusions easier, as it stratifies the
syntax of the signature and any additional syntax built atop it.

```agda
data Spine (Args : List ∣ Sort ∣) (X : ∣ Sort ∣) : Type (ℓ ⊔ ℓ′) where
  op  : ∣ Op Args X ∣ → Spine Args X
  app : ∀ {A} → Spine (A ∷ Args) X → Tm A → Spine Args X
```


## Path Space

```agda
module SpinePath where

  CodeP : ∀ (P : I → List ∣ Sort ∣) {R} → Spine (P i0) R → Spine (P i1) R → Type (ℓ ⊔ ℓ′)
  CodeP P {R = R} (op o1) (op o2) = Lift ℓ′ (PathP (λ i → ∣ Op (P i) R ∣) o1 o2)
  CodeP P (op _) (app _ _) = Lift _ ⊥
  CodeP P (app _ _) (op _) = Lift _ ⊥
  CodeP P (app {A} f x) (app {B} g y) =
    Σ[ p ∈ A ≡ B ] (CodeP (λ i → p i ∷ P i) f g × PathP (λ i → Tm (p i)) x y)

  encode-refl : ∀ {Args : List ∣ Sort ∣} {R} → (f : Spine Args R) → CodeP (λ _ → Args) f f
  encode-refl (op x) = lift refl
  encode-refl (app f x) = refl , encode-refl f , refl

  encode : ∀ {P R} {f : Spine (P i0) R} {g : Spine (P i1) R}
         → PathP (λ i → Spine (P i) R) f g → CodeP P f g
  encode {P = P} {f = f} {g = g} p =
    coe0→1 (λ i → CodeP (λ j → P (i ∧ j)) f (p i)) (encode-refl f)

  decode : ∀ {P R} {f : Spine (P i0) R} {g : Spine (P i1) R}
         → CodeP P f g → PathP (λ i → Spine (P i) R) f g
  decode {f = op _} {g = op _} (lift p) i = op (p i)
  decode {f = app f x} {g = app g x₁} (p , q , r) i = app {A = p i} (decode q i) (r i)

  decode-encode-refl : ∀ {Args R} {f : Spine Args R} → decode (encode-refl f) ≡ refl
  decode-encode-refl {f = op x} = refl
  decode-encode-refl {f = app f x} i j = app (decode-encode-refl {f = f} i j) x

  decode-encode : ∀ {P : I → List ∣ Sort ∣} {R} {f : Spine (P i0) R} {g : Spine (P i1) R}
                → (p : PathP (λ i → Spine (P i) R) f g) → decode (encode p) ≡ p
  decode-encode {P = P} {R = R} {f = f} {g = g} p = transport ϕ decode-encode-refl
    where
      ϕ : (decode (encode-refl f) ≡ refl) ≡ (decode (encode p) ≡ p)
      ϕ i = decode (transp (λ j → CodeP (λ k → P (i ∧ j ∧ k)) f (p (i ∧ j))) (~ i) (encode-refl f)) ≡ λ j → p (i ∧ j)

  encode-decode : ∀ {P R} {f : Spine (P i0) R} {g : Spine (P i1) R}
                → (c : CodeP P f g) → encode (decode c) ≡ c
  encode-decode {f = op o1} {g = op o2} (lift p) =
    transport
      (λ i → encode (decode {f = op o1} {g = op (p i)} (lift (λ j → p (i ∧ j)))) ≡ lift (λ j → p (i ∧ j)))
      (transport-refl _)
  encode-decode {P = P} {R = R} {f = app {A} f x} {g = app {B} g y} (p , q , r) =
    transport
      (λ i →
        transp (λ j → Σ[ t ∈ A ≡ p (i ∧ j) ] (CodeP (λ k → t k ∷ P (i ∧ j ∧ k)) f (decode q (i ∧ j)) × PathP (λ k → Tm (t k)) x (r (i ∧ j)))) (~ i) (refl , encode-refl f , refl) ≡
        ((λ j → p (i ∧ j)) , coe1→i ϕ i q , λ j → r (i ∧ j)))
      (refl ,ₚ q-path ,ₚ refl)
      where
        ϕ : (i : I) → Type _
        ϕ i = CodeP (λ j → p (i ∧ j) ∷ P (i ∧ j)) f (decode q i)
      
        q-path : encode-refl f ≡ coe1→i ϕ i0 q
        q-path =
          encode-refl f                       ≡⟨⟩
          coe ϕ i0 i0 (encode-refl f)         ≡˘⟨ coei→j→k ϕ i0 i1 i0 (encode-refl f) ⟩
          coe1→0 ϕ (coe0→1 ϕ (encode-refl f)) ≡⟨ ap (coe1→0 ϕ) (encode-decode q) ⟩
          coe1→0 ϕ q                          ∎

  CodeP≃PathP : ∀ {P R} {f : Spine (P i0) R} {g : Spine (P i1) R}
              → PathP (λ i → Spine (P i) R) f g ≃ CodeP P f g
  CodeP≃PathP = Iso→Equiv (encode , iso decode encode-decode decode-encode)


Spine-is-hlevel : ∀ {Args : List ∣ Sort ∣} {R : ∣ Sort ∣} → (n : Nat)
                → (∀ (A : ∣ Sort ∣) → is-hlevel (Tm A) (2 + n))
                → is-hlevel (Spine Args R) (2 + n)
Spine-is-hlevel n tmhl p q = is-hlevel≃ (suc n) CodeP≃PathP (CodeP-is-hlevel p q) where
  open SpinePath

  CodeP-is-hlevel : ∀ {P R} (f : Spine (P i0) R) (g : Spine (P i1) R)
                  → is-hlevel (CodeP P f g) (suc n)
  CodeP-is-hlevel {P} {R} (op o1) (op o2) =
    Lift-is-hlevel (suc n) $
    is-prop→is-hlevel-suc $
    PathP-is-hlevel' 1 (is-tr (Op (P i1) R)) o1 o2
  CodeP-is-hlevel (op _) (app _ _) = hlevel!
  CodeP-is-hlevel (app _ _) (op _) = hlevel!
  CodeP-is-hlevel (app f x) (app g y) =
    Σ-is-hlevel (suc n) (is-prop→is-hlevel-suc (is-tr Sort _ _)) λ p →
    Σ-is-hlevel (suc n) (CodeP-is-hlevel f g) λ _ →
    PathP-is-hlevel' (suc n) (tmhl (p i1)) x y
```
