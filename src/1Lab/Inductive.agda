module 1Lab.Inductive where

open import 1Lab.Reflection hiding (absurd)
open import 1Lab.Univalence
open import 1Lab.Equiv
open import 1Lab.Type hiding (case_of_ ; case_return_of_)
open import 1Lab.Path

open import Data.Sum.Base

{-
Automation for applying induction principles
============================================

When working with mixed truncations/products/quotients, the relevant
induction principles are often repeatedly applied in close succession,
like in the snippet below.

  □-rec! λ { (a , b , w) → □-rec! (λ { (c , d , x) →
      inc (c , d , inc (a , x , w)) }) b }

Applying these induction principles is entirely mechanical: like other
mechanical processes, it's annoying to do by hand, generates ugly code,
and causes a deep sense of existential uselessness. This module
implements automation for automatically applying these eliminators "as
far as possible", using overlapping instances.

The Inductive class
-------------------

The core of the implementation for rec!/elim! is the Inductive class,
which is a slight misnomer. To support *nested* types with a single
constructor, the Inductive class is applied to a section of the motive,
not just base type. That is, if we want to simplify

  □ (□ A × □ (□ A)) → B
  ^~~~~~~~~~~~~~~~~ domain

we don't look for an instance of `Inductive domain`, we look for an
instance of `Inductive (domain → B)`. The relevant instances then
manipulate the entire function type at once, much like Extensional.

Writing rules
-------------

Like Extensional, instances of 'Inductive' should be maximally lazy, so
that the structural rules can fire as often as possible. That is,
instead of writing

  ⦃ _ : ∀ {x} → Inductive (P (inc x)) ⦄ → Inductive (∀ x → P x)

we write

  ⦃ _ : Inductive (∀ x → P (inc x)) ⦄ → Inductive (∀ x → P x)
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
  -- The basic structural rules allow us to stop recurring (we can
  -- produce an A given an A) and to skip an argument, introducing a
  -- function type into the methods:

  Inductive-default : Inductive A (level-of A)
  Inductive-default .methods = _
  Inductive-default .from x  = x

  Inductive-Π
    : ⦃ _ : {x : A} → Inductive (P x) ℓm ⦄
    → Inductive (∀ x → P x) (level-of A ⊔ ℓm)
  Inductive-Π ⦃ r ⦄ .methods  = ∀ x → r {x} .methods
  Inductive-Π ⦃ r ⦄ .from f x = r .from (f x)

  {-# INCOHERENT Inductive-default #-}
  {-# OVERLAPPABLE Inductive-Π #-}

  -- Next, we have a rule for uncurrying pairs. This lets us handle types like
  --   □ (□ A × □ B) → C
  --
  -- by factoring through
  --
  --   □ (□ A × □ B) → C
  --   □ A × □ B → C
  --   □ A → □ B → C
  --   □ B → C

  Inductive-Σ
    : ∀ {A : Type ℓ} {B : A → Type ℓ'} {C : (x : A) → B x → Type ℓ''}
    → ⦃ _ : Inductive ((x : A) (y : B x) → C x y) ℓm ⦄
    → Inductive ((x : Σ A B) → C (x .fst) (x .snd)) ℓm
  Inductive-Σ ⦃ r ⦄ .methods        = r .methods
  Inductive-Σ ⦃ r ⦄ .from f (x , y) = r .from f x y

  Inductive-Lift
    : {B : Lift ℓ A → Type ℓ'}
    → ⦃ _ : Inductive (∀ x → B (lift x)) ℓm ⦄
    → Inductive (∀ x → B x) ℓm
  Inductive-Lift ⦃ i ⦄ = record { from = λ f (lift x) → i .from f x }

  -- However, we don't uncurry equivalences.

  Inductive-≃ : {C : A ≃ B → Type ℓ''} → Inductive (∀ x → C x) _
  Inductive-≃ = Inductive-default

  {-# OVERLAPPING Inductive-≃ #-}

  -- We split up sums, and apply rules to both sides of the eliminator.
  Inductive-⊎
    : ∀ {ℓm ℓm'} {C : A ⊎ B → Type ℓ}
    → ⦃ _ : Inductive ((a : A) → C (inl a)) ℓm ⦄
    → ⦃ _ : Inductive ((b : B) → C (inr b)) ℓm' ⦄
    → Inductive ((ab : A ⊎ B) → C ab) (ℓm ⊔ ℓm')
  Inductive-⊎ {C = _} ⦃ il ⦄ ⦃ ir ⦄ .methods = il .methods × ir .methods
  Inductive-⊎ {C = _} ⦃ il ⦄ ⦃ ir ⦄ .from (lm , rm) (inl a) = il .from lm a
  Inductive-⊎ {C = _} ⦃ il ⦄ ⦃ ir ⦄ .from (lm , rm) (inr b) = ir .from rm b

  -- If we ever see a proof of ⊥, then we stop resolving rules, and use ⊤
  -- for the methods of induction.
  Inductive-⊥
    : ∀ {B : ⊥ → Type ℓ}
    → Inductive ((ff : ⊥) → B ff) lzero
  Inductive-⊥ .methods = ⊤
  Inductive-⊥ .from _ ff = absurd ff

-- For constructing (dependent) functions, there are two distinct prefix
-- entry points: rec! and elim!. The difference is just in name, to
-- provide a modicum of documentation. In addition, they have an
-- explicit function type, so that the refine command will always
-- introduce a question mark.

rec! : ⦃ r : Inductive (A → B) ℓm ⦄ → r .methods → A → B
rec! ⦃ r ⦄ = r .from

elim! : ⦃ r : Inductive (∀ x → P x) ℓm ⦄ → r .methods → ∀ x → P x
elim! ⦃ r ⦄ = r .from

-- We also define versions of case_of_ and case_return_of_, shadowing
-- those from 1Lab.Type, which insert a rec!/elim!.

case_of_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} ⦃ r : Inductive (A → B) ℓm ⦄ → A → r .methods → B
case x of f = rec! f x

case_return_of_ : ∀ {ℓ ℓ'} {A : Type ℓ} (x : A) (B : A → Type ℓ') ⦃ r : Inductive (∀ x → B x) ℓm ⦄ (f : r .methods) → B x
case x return P of f = elim! f x

{-# INLINE case_of_        #-}
{-# INLINE case_return_of_ #-}

-- For path!, we insist on returning a PathP type. This helps infer the
-- line.

path! : ∀ {B : I → Type ℓ} {f g} ⦃ r : Inductive (PathP B f g) ℓm ⦄ → r .methods → PathP B f g
path! ⦃ r ⦄ = r .from

instance
  Inductive-ua→
    : ∀ {e : A ≃ B} {C : ∀ i → ua e i → Type ℓ} {f : ∀ a → C i0 a} {g : ∀ a → C i1 a}
    → ⦃ _ : Inductive ((x : A) → PathP (λ i → C i (ua-inc e x i)) (f x) (g (e .fst x))) ℓm ⦄
    → Inductive (PathP (λ i → (x : ua e i) → C i x) f g) ℓm
  Inductive-ua→ ⦃ r ⦄ .methods = r .methods
  Inductive-ua→ ⦃ r ⦄ .from f  = ua→ (λ a → r .from f a)

  Inductive-ua→'
    : ∀ {e : A ≃ B} {C : ∀ i → ua e i → Type ℓ} {f : ∀ {a} → C i0 a} {g : ∀ {a} → C i1 a}
    → ⦃ _ : Inductive ((x : A) → PathP (λ i → C i (ua-inc e x i)) (f {x}) (g {e .fst x})) ℓm ⦄
    → Inductive (PathP (λ i → {x : ua e i} → C i x) f g) ℓm
  Inductive-ua→' ⦃ r ⦄ .methods = r .methods
  Inductive-ua→' ⦃ r ⦄ .from f  = ua→' (λ a → r .from f a)

  Inductive-ua-path
    : ∀ {e : A ≃ B} {x : A} {y : B}
    → Inductive (PathP (λ i → ua e i) x y) (level-of B)
  Inductive-ua-path {e = e} {x} {y} .methods = e .fst x ≡ y
  Inductive-ua-path .from = path→ua-pathp _
