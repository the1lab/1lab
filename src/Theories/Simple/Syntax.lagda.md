```agda
open import Cat.Prelude

open import Data.List
open import Data.Sum

open import Theories.Signature

module Theories.Simple.Syntax {ℓ} (Sg : Sign ℓ) where

open Sign Sg
```

# Terms

As noted earlier, [signatures] form the raw materials we construct theories out of.

[signatures] Theories.Signature.html

```agda
data Term (Γ : List ∣ Sort ∣) (X : ∣ Sort ∣) : Type ℓ
data Fn (Ψ : List ∣ Sort ∣) (Γ : List ∣ Sort ∣) (X : ∣ Sort ∣) : Type ℓ

data Term Γ X where
  var : X ∈ Γ → Term Γ X
  fn  : Fn [] Γ X → Term Γ X

data Fn Ψ Γ X where
  op : ∣ Op Ψ X ∣ → Fn Ψ Γ X
  app : ∀ {A} → Fn (A ∷ Ψ) Γ X → Term Γ A → Fn Ψ Γ X 
```

## Substitutions

```agda
Subst : ∀ (Γ Δ : List ∣ Sort ∣) → Type ℓ
Subst Γ [] = Lift _ ⊤
Subst Γ (X ∷ Δ) = Term Γ X × Subst Γ Δ

lookup : ∀ {Γ Δ X} → Subst Γ Δ → X ∈ Δ → Term Γ X
lookup {Δ = A ∷ Δ} (tm , σ) (inl p) = subst (Term _) p tm
lookup {Δ = A ∷ Δ} (tm , σ) (inr v) = lookup σ v

tabulate : ∀ {Γ Δ} → (∀ {X} → X ∈ Δ → Term Γ X) → Subst Γ Δ
tabulate {Δ = []} k = lift tt
tabulate {Δ = X ∷ Δ} k = k (inl refl) , tabulate (k ⊙ inr)

sub : ∀ {Γ Δ X} → Subst Γ Δ → Term Δ X → Term Γ X
sub-fn : ∀ {Ψ Γ Δ X} → Subst Γ Δ → Fn Ψ Δ X → Fn Ψ Γ X

sub σ (var v) = lookup σ v
sub σ (fn f) = fn (sub-fn σ f)

sub-fn σ (op o) = op o
sub-fn σ (app f x) = app (sub-fn σ f) (sub σ x)
```

## Path Space

```agda
module TermPath where

  TermCodeP : ∀ {Γ} (P : I → ∣ Sort ∣) → Term Γ (P i0) → Term Γ (P i1) → Type ℓ
  FnCodeP : ∀ (P : I → List ∣ Sort ∣) {Γ} (Q : I → ∣ Sort ∣) → Fn (P i0) Γ (Q i0) → Fn (P i1) Γ (Q i1) → Type ℓ

  TermCodeP {Γ = Γ} P (var x) (var y) = PathP (λ i → P i ∈ Γ) x y
  TermCodeP _ (var _) (fn _) = Lift _ ⊥
  TermCodeP _ (fn _) (var _) = Lift _ ⊥
  TermCodeP {Γ = Γ} P (fn x) (fn y) = FnCodeP (λ _ → []) P x y

  FnCodeP P Q (op o1) (op o2) =
    PathP (λ i → ∣ Op (P i) (Q i) ∣) o1 o2
  FnCodeP P Q (op _) (app _ _) =
    Lift _ ⊥
  FnCodeP P Q (app _ _) (op _) =
    Lift _ ⊥
  FnCodeP P Q (app {A} f x) (app {B} g y) =
    Σ[ p ∈ A ≡ B ] (FnCodeP (λ i → p i ∷ P i) Q f g × TermCodeP (λ i → p i) x y)

  encode-term-refl : ∀ {Γ X} → (x : Term Γ X) → TermCodeP (λ _ → X) x x
  encode-fn-refl : ∀ {Ψ Γ X} → (f : Fn Ψ Γ X) → FnCodeP (λ _ → Ψ) (λ _ → X) f f

  encode-term-refl (var _) = refl
  encode-term-refl (fn f) = encode-fn-refl f

  encode-fn-refl (op x) = refl
  encode-fn-refl (app f x) = refl , encode-fn-refl f , encode-term-refl x

  encode-term-filler : ∀ {Γ} {P : I → ∣ Sort ∣}
                     → (x : Term Γ (P i0)) (y : Term Γ (P i1))
                     → (p : PathP (λ i → Term Γ (P i)) x y)
                     → (i : I) → TermCodeP (λ j → P (i ∧ j)) x (p i)
  encode-term-filler {P = P} x y p i =
    coe0→i (λ j → TermCodeP (λ k → P (j ∧ k)) x (p j)) i (encode-term-refl x)

  encode-term : ∀ {Γ P} (x : Term Γ (P i0)) (y : Term Γ (P i1))
              → PathP (λ i → Term Γ (P i)) x y → TermCodeP P x y
  encode-term {P = P} x y p = encode-term-filler x y p i1

  encode-fn-filler : ∀ {P : I → List ∣ Sort ∣} {Γ} {Q : I → ∣ Sort ∣}
                   → (f : Fn (P i0) Γ (Q i0)) (g : Fn (P i1) Γ (Q i1))
                   → (p : PathP (λ i → Fn (P i) Γ (Q i)) f g)
                   → (i : I) → FnCodeP (λ j → P (i ∧ j)) (λ j → Q (i ∧ j)) f (p i)
  encode-fn-filler {P = P} {Q = Q} f g p i =
    coe0→i (λ j → FnCodeP (λ k → P (j ∧ k)) (λ k → Q (j ∧ k)) f (p j)) i
      (encode-fn-refl f)

  encode-fn : ∀ {P Γ Q} (f : Fn (P i0) Γ (Q i0)) (g : Fn (P i1) Γ (Q i1))
            → PathP (λ i → Fn (P i) Γ (Q i)) f g → FnCodeP P Q f g
  encode-fn {P = P} {Q = Q} f g p = encode-fn-filler f g p i1

  decode-term : ∀ {Γ P} (x : Term Γ (P i0)) (y : Term Γ (P i1))
              → TermCodeP P x y → PathP (λ i → Term Γ (P i)) x y
  decode-fn : ∀ {P Γ Q} (f : Fn (P i0) Γ (Q i0)) (g : Fn (P i1) Γ (Q i1))
            → FnCodeP P Q f g → PathP (λ i → Fn (P i) Γ (Q i)) f g

  decode-term (var _) (var _) c i = var (c i)
  decode-term (fn f) (fn g) c i = fn (decode-fn f g c i)

  decode-fn (op _) (op _) c i = op (c i)
  decode-fn {Q = Q} (app f x) (app g y) (p , q , r) i =
    app {A = p i} (decode-fn f g q i) (decode-term {P = λ i → p i} x y r i)

  decode-encode-term-refl : ∀ {Γ X} (x : Term Γ X)
                          → decode-term x x (encode-term-refl x) ≡ refl
  decode-encode-fn-refl : ∀ {Ψ Γ X} (f : Fn Ψ Γ X)
                          → decode-fn f f (encode-fn-refl f) ≡ refl

  decode-encode-term-refl (var x) =
    refl
  decode-encode-term-refl (fn f) i j =
    fn (decode-encode-fn-refl f i j)

  decode-encode-fn-refl (op x) =
    refl
  decode-encode-fn-refl (app f x) i j =
    app (decode-encode-fn-refl f i j) (decode-encode-term-refl x i j)

  decode-encode-term : ∀ {Γ} {P : I → ∣ Sort ∣}
                     → (x : Term Γ (P i0)) (y : Term Γ (P i1))
                     → (p : PathP (λ i → Term Γ (P i)) x y)
                     → decode-term x y (encode-term x y p) ≡ p
  decode-encode-term {P = P} x y p =
    coe0→1 (λ i → decode-term x (p i) (encode-term-filler x y p i) ≡ λ j → p (i ∧ j))
      (decode-encode-term-refl x)

  decode-encode-fn : ∀ {P : I → List ∣ Sort ∣} {Γ} {Q : I → ∣ Sort ∣}
                     → (f : Fn (P i0) Γ (Q i0)) (g : Fn (P i1) Γ (Q i1))
                     → (p : PathP (λ i → Fn (P i) Γ (Q i)) f g)
                     → decode-fn f g (encode-fn f g p) ≡ p
  decode-encode-fn {P = P} {Q = Q} f g p =
    coe0→1 (λ i → decode-fn f (p i) (encode-fn-filler f g p i) ≡ λ j → p (i ∧ j))
      (decode-encode-fn-refl f)

  encode-decode-term : ∀ {Γ} {P : I → ∣ Sort ∣}
                     → (x : Term Γ (P i0)) (y : Term Γ (P i1))
                     → (c : TermCodeP P x y)
                     → encode-term x y (decode-term {P = P} x y c) ≡ c

  encode-decode-fn : ∀ {P : I → List ∣ Sort ∣} {Γ} {Q : I → ∣ Sort ∣}
                     → (f : Fn (P i0) Γ (Q i0)) (g : Fn (P i1) Γ (Q i1))
                     → (c : FnCodeP P Q f g)
                     → encode-fn f g (decode-fn {P = P} {Q = Q} f g c) ≡ c

  encode-decode-term {P = P} (var v1) (var v2) p =
    transport (λ i → encode-term-filler _ _ (λ j → var (p j)) i ≡ λ j → p (i ∧ j))
      refl
  encode-decode-term {P = P} (fn f) (fn g) c =
    transport
      (λ i → encode-term-filler _ _ (λ j → fn (decode-fn f g c j)) i ≡ coe1→i K i c) $
      sym (coei→j→k K i0 i1 i0 (encode-fn-refl f)) ∙
      ap (coe1→0 K) (encode-decode-fn f g c)
      where
        K : (i : I) → Type _
        K i = FnCodeP (λ _ → []) (λ j → P (i ∧ j)) f (decode-fn f g c i)

  encode-decode-fn {P = P} {Γ = Γ} {Q = Q} (op o1) (op o2) p =
    transport
      (λ i → encode-fn-filler {Γ = Γ} _ _ (λ j → op (p j)) i ≡
             λ j → p (i ∧ j))
      refl
  encode-decode-fn {P = P} {Q = Q} (app {A} f x) (app g y) (p , fnc , tmc) =
    transport
      (λ i → coe0→i (λ j → Σ[ t ∈ A ≡ p j ]
               (FnCodeP (λ k → t k ∷ P (j ∧ k)) (λ k → Q (j ∧ k)) f (decode-fn f g fnc j) ×
               TermCodeP (λ k → t k) x (decode-term {P = λ k → p k} x y tmc j))) i
               (refl , encode-fn-refl f , encode-term-refl x) ≡
             ((λ j → p (i ∧ j)) , coe1→i KFn i fnc , coe1→i KTm i tmc)) $
      refl ,ₚ
      sym (coei→j→k KFn i0 i1 i0 (encode-fn-refl f)) ∙ ap (coe1→0 KFn) (encode-decode-fn f g fnc) ,ₚ
      sym (coei→j→k KTm i0 i1 i0 (encode-term-refl x)) ∙ ap (coe1→0 KTm) (encode-decode-term {P = λ i → p i} x y tmc)
      where
        KFn : I → Type _
        KFn i = FnCodeP (λ j → p (i ∧ j) ∷ P (i ∧ j)) (λ j → Q (i ∧ j)) f (decode-fn _ _ fnc i)

        KTm : I → Type _
        KTm i = TermCodeP (λ j → p (i ∧ j)) x (decode-term {P = λ j → p j} x y tmc i)

  TermCodeP≃PathP : ∀ {Γ P} {x : Term Γ (P i0)} {y : Term Γ (P i1)}
                  → PathP (λ i → Term Γ (P i)) x y ≃ TermCodeP P x y
  TermCodeP≃PathP {P = P} {x = x} {y = y} = Iso→Equiv $
    (encode-term x y) ,
    iso (decode-term x y)
        (encode-decode-term {P = P} x y)
        (decode-encode-term {P = P} x y)

  FnCodeP≃PathP : ∀ {P Γ Q} {f : Fn (P i0) Γ (Q i0)} {g : Fn (P i1) Γ (Q i1)}
                → PathP (λ i → Fn (P i) Γ (Q i)) f g ≃ FnCodeP P Q f g
  FnCodeP≃PathP {P = P} {Q = Q} {f = f} {g = g} = Iso→Equiv $
    (encode-fn f g) ,
    iso (decode-fn f g)
        (encode-decode-fn f g)
        (decode-encode-fn f g)

  TermCodeP-is-hlevel : ∀ {P Γ} → (n : Nat)
                      → (x : Term Γ (P i0)) (y : Term Γ (P i1))
                      → is-hlevel (TermCodeP P x y) (suc n)
  FnCodeP-is-hlevel : ∀ {P Γ Q} → (n : Nat)
                    → (f : Fn (P i0) Γ (Q i0)) (g : Fn (P i1) Γ (Q i1))
                    → is-hlevel (FnCodeP P Q f g) (suc n)

  TermCodeP-is-hlevel n (var v1) (var v2) =
    PathP-is-hlevel' (suc n)
      (∈-is-hlevel n (is-set→is-hlevel+2 (is-tr Sort))) v1 v2
  TermCodeP-is-hlevel n (var _) (fn _) =
    hlevel!
  TermCodeP-is-hlevel n (fn _) (var _) =
    hlevel!
  TermCodeP-is-hlevel n (fn f) (fn g) =
    FnCodeP-is-hlevel n f g

  FnCodeP-is-hlevel n (op o1) (op o2) =
    PathP-is-hlevel' (suc n)
      (is-set→is-hlevel+2 (is-tr (Op _ _))) o1 o2
  FnCodeP-is-hlevel n (op _) (app _ _) =
    hlevel!
  FnCodeP-is-hlevel n (app f x) (op x₁) =
    hlevel!
  FnCodeP-is-hlevel n (app f x) (app g y) =
    Σ-is-hlevel (suc n) (is-prop→is-hlevel-suc (is-tr Sort _ _)) λ p →
    Σ-is-hlevel (suc n) (FnCodeP-is-hlevel n f g) λ _ →
    TermCodeP-is-hlevel {P = λ i → p i} n x y

Term-is-hlevel : ∀ {Γ X} → (n : Nat) → is-hlevel (Term Γ X) (2 + n)
Term-is-hlevel {X = X} n x y =
  is-hlevel≃ (suc n) TermCodeP≃PathP (TermCodeP-is-hlevel {P = λ _ → X} n x y)
  where
    open TermPath

Fn-is-hlevel : ∀ {Ψ Γ X} → (n : Nat) → is-hlevel (Fn Ψ Γ X) (2 + n)
Fn-is-hlevel n f g =
  is-hlevel≃ (suc n) FnCodeP≃PathP (FnCodeP-is-hlevel n f g)
  where
    open TermPath

Subst-is-hlevel : ∀ {Γ Δ} → (n : Nat) → is-hlevel (Subst Γ Δ) (2 + n)
Subst-is-hlevel {Δ = []} n = hlevel!
Subst-is-hlevel {Δ = A ∷ Δ} n = ×-is-hlevel (2 + n) (Term-is-hlevel n) (Subst-is-hlevel n)
```
