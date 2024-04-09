module 1Lab.Inductive where

open import 1Lab.Reflection
open import 1Lab.Equiv
open import 1Lab.Type hiding (case_of_ ; case_return_of_)

{-
Automation for induction principles
===================================
-}

record Inductive {ℓ} (A : Type ℓ) ℓm : Type (ℓ ⊔ lsuc ℓm) where
  field
    methods : Type ℓm
    from    : methods → A

open Inductive

private variable
  ℓ ℓ' ℓ'' ℓm : Level
  A B C : Type ℓ
  P Q R : A → Type ℓ

instance
  Inductive-default : Inductive A (level-of A)
  Inductive-default .methods = _
  Inductive-default .from x  = x

  {-# INCOHERENT Inductive-default #-}

  Inductive-Π
    : ⦃ _ : {x : A} → Inductive (P x) ℓm ⦄
    → Inductive (∀ x → P x) (level-of A ⊔ ℓm)
  Inductive-Π ⦃ r ⦄ .methods  = ∀ x → r {x} .methods
  Inductive-Π ⦃ r ⦄ .from f x = r .from (f x)

  {-# OVERLAPPABLE Inductive-Π #-}

  Inductive-Σ
    : ∀ {A : Type ℓ} {B : A → Type ℓ'} {C : (x : A) → B x → Type ℓ''}
    → ⦃ _ : Inductive ((x : A) (y : B x) → C x y) ℓm ⦄
    → Inductive ((x : Σ A B) → C (x .fst) (x .snd)) ℓm
  Inductive-Σ ⦃ r ⦄ .methods        = r .methods
  Inductive-Σ ⦃ r ⦄ .from f (x , y) = r .from f x y

  Inductive-≃
    : {C : A ≃ B → Type ℓ''}
    → Inductive (∀ x → C x) _
  Inductive-≃ = Inductive-default

  {-# OVERLAPPING Inductive-≃ #-}

rec! : ⦃ r : Inductive (A → B) ℓm ⦄ → r .methods → A → B
rec! ⦃ r ⦄ = r .from

elim! : ⦃ r : Inductive (∀ x → P x) ℓm ⦄ → r .methods → ∀ x → P x
elim! ⦃ r ⦄ = r .from

case_of_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} ⦃ r : Inductive (A → B) ℓm ⦄ → A → r .methods → B
case x of f = rec! f x

case_return_of_ : ∀ {ℓ ℓ'} {A : Type ℓ} (x : A) (B : A → Type ℓ') ⦃ r : Inductive (∀ x → B x) ℓm ⦄ (f : r .methods) → B x
case x return P of f = elim! f x

{-# INLINE case_of_        #-}
{-# INLINE case_return_of_ #-}
