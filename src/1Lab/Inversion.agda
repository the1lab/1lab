open import Data.Reflection.Error
open import Data.String.Base
open import 1Lab.Reflection using (typeError; _∷_; []; TC; Term)
open import 1Lab.Type

module 1Lab.Inversion where

data Types : Typeω where
  [] : Types
  _,_ : ∀ {ℓ} → Type ℓ → Types → Types

private
  level-of-types : Types → Level
  level-of-types [] = lzero
  level-of-types (A , As) = level-of A ⊔ level-of-types As

  _++_ : Types → Types → Types
  [] ++ Bs = Bs
  (A , As) ++ Bs = A , (As ++ Bs)

  _→*_ : ∀ {ℓ} → (As : Types) → Type ℓ → Type (level-of-types As ⊔ ℓ)
  [] →* B = B
  (A , As) →* B = A → As →* B

  const* : ∀ {ℓ} (As : Types) {A : Type ℓ}  → A → As →* A
  const* [] a = a
  const* (_ , As) a = λ _ → const* As a

  Σ* : ∀ (As : Types) → Type (level-of-types As)
  Σ* [] = ⊤
  Σ* (A , As) = A × Σ* As

  λ* : ∀ {ℓ} {A : Type ℓ} → (As : Types) → (Σ* As → A) → As →* A
  λ* [] f = f tt
  λ* (_ , As) f = λ x → λ* As λ xs → f (x , xs)

  _,*_ : {As Bs : Types} → Σ* As → Σ* Bs → Σ* (As ++ Bs)
  _,*_ {As = []} as bs = bs
  _,*_ {As = x , As} (a , as) bs = a , (as ,* bs)

  _$*_ : ∀ {ℓ} {As : Types} {A : Type ℓ} → (As →* A) → Σ* As → A
  _$*_ {As = []} f xs = f
  _$*_ {As = A , As} f (x , xs) = f x $* xs

  infixr 5 _→*_
  infixr 4 _++_
  infixl 0 _$*_

{-
Rules
=====
-}

data RuleHead : Typeω where
  fact_ : ∀ {ℓ} → Type ℓ → RuleHead
  inverting_ : ∀ {ℓ} → Type ℓ → RuleHead
  _and_ : RuleHead → RuleHead → RuleHead

infix 3 fact_ inverting_
infixr 2 _and_

data Rules {ℓ} (A : Type ℓ) : Typeω where
  _by_ : RuleHead → Types → Rules A
  _or_ :  Rules A → Rules A → Rules A

infix 1 _by_
infix 0 _or_

level-of-rule-head : RuleHead → Level
level-of-rule-head (fact A) = level-of A
level-of-rule-head (inverting A) = level-of A
level-of-rule-head (H₁ and H₂) = level-of-rule-head H₁ ⊔ level-of-rule-head H₂

rule-head : (H : RuleHead) → Type (level-of-rule-head H)
rule-head (fact A) = A
rule-head (inverting A) = A
rule-head (H₁ and H₂) = rule-head H₁ × rule-head H₂

rule-head-facts : RuleHead → Types → Types
rule-head-facts (fact A) Facts = A , Facts
rule-head-facts (inverting _) Facts = Facts
rule-head-facts (H₁ and H₂) Facts = rule-head-facts H₁ (rule-head-facts H₂ Facts)

rule-head-inversions : RuleHead → Types → Types
rule-head-inversions (fact A) Facts = Facts
rule-head-inversions (inverting A) Facts = A , Facts
rule-head-inversions (H₁ and H₂) Facts = rule-head-inversions H₁ (rule-head-inversions H₂ Facts)

rule-head-split
  : ∀ {L R : Types} (Head : RuleHead)
  → rule-head Head → Σ* L → Σ* R
  → Σ* (rule-head-facts Head L) × Σ* (rule-head-inversions Head R)
rule-head-split (fact A) a l r = (a , l) , r
rule-head-split (inverting A) a l r = l , (a , r)
rule-head-split (H₁ and H₂) (h₁ , h₂) l r =
  let (l' , r') = rule-head-split H₂ h₂ l r
  in rule-head-split  H₁ h₁ l' r'

level-of-rules : ∀ {ℓ} {A : Type ℓ} → Rules A → Level
level-of-rules (Head by Body) = level-of-rule-head Head ⊔ level-of-types Body
level-of-rules (Rs₁ or Rs₂) = level-of-rules Rs₁ ⊔ level-of-rules Rs₂

rules-bodies : ∀ {ℓ} {A : Type ℓ} → Rules A → Types
rules-bodies (Head by Body) = Body
rules-bodies (Rs₁ or Rs₂) = rules-bodies Rs₁ ++ rules-bodies Rs₂

rules-facts : ∀ {ℓ} {A : Type ℓ} → Rules A → Types → Types
rules-facts (Head by Body) Facts = rule-head-facts Head Facts
rules-facts (Rs₁ or Rs₂) Facts = rules-facts Rs₁ (rules-facts Rs₂ Facts)

Rules-sound : ∀ {ℓ} → {A : Type ℓ} → (Rs : Rules A) → Type (ℓ ⊔ level-of-rules Rs)
Rules-sound {A = A} (Head by Body) = Body →* (A → rule-head Head)
Rules-sound {A = A} (Rs₁ or Rs₂) = Rules-sound Rs₁ × Rules-sound Rs₂

record Inversion {ℓ} (A : Type ℓ) : Typeω where
  field
    rules : Rules A
    inversion-rules : Rules-sound rules

open Inversion

instance
  -- Default 'Inversion' instance that treats 'A' as a fact.
  Inversion-Default
    : ∀ {ℓ} {A : Type ℓ}
    → Inversion A
  Inversion-Default {A = A} .rules = fact A by []
  Inversion-Default {A = A} .inversion-rules a = a
  {-# OVERLAPPABLE Inversion-Default #-}

{-
Forward Inference
=================
-}

private variable
  ℓ : Level
  A B H Fact Goal : Type ℓ
  Hyps Goals Facts Body : Types
  Head : RuleHead
  Rs Rs₁ Rs₂ : Rules H

data ForwardInference (Facts : Types) (Hyps : Types) (Goals : Types) : Typeω where
  failure : ForwardInference Facts Hyps Goals
  success : (Σ* Facts → Σ* Hyps → Σ* Goals) → ForwardInference Facts Hyps Goals

data TryFacts (Facts : Types) (Goal : Type ℓ) : Typeω where
  failure : TryFacts Facts Goal
  success : (Σ* Facts → Goal) → TryFacts Facts Goal

record Haltω : Typeω where
  instance constructor haltω

WhenFoundFact
  : TryFacts Facts Goal
  → Typeω
  → Typeω
WhenFoundFact failure _ = Haltω
WhenFoundFact (success _) T = T

WhenInferenceFails
  : ForwardInference Facts Hyps Goals
  → Typeω
  → Typeω
WhenInferenceFails failure T = T
WhenInferenceFails (success x) _ = Haltω

record SoundRules (A : Type ℓ) (Rs : Rules A) : Typeω where
  field
    inversion-rules : Rules-sound Rs

open SoundRules

Left-sound-rules
  : ∀ {ℓ} {A : Type ℓ} {Rs₁ Rs₂ : Rules A}
  → SoundRules A (Rs₁ or Rs₂)
  → SoundRules A Rs₁
Left-sound-rules I .inversion-rules = I .inversion-rules .fst

Right-sound-rules
  : ∀ {ℓ} {A : Type ℓ} {Rs₁ Rs₂ : Rules A}
  → SoundRules A (Rs₁ or Rs₂)
  → SoundRules A Rs₂
Right-sound-rules I .inversion-rules = I .inversion-rules .snd

unbundle-inversion : (I : Inversion A) → SoundRules A (I .rules)
unbundle-inversion I .inversion-rules = I .inversion-rules

record TryInversion (Facts : Types) (Hyps : Types) (Inv : SoundRules H Rs) : Typeω where
  field
    NewFacts : Types
    NewHyps : Types
    new-proofs : Σ* Facts → Σ* Hyps → (H → Σ* NewFacts × Σ* NewHyps)

open TryInversion

instance
  TryInversion-By
    : {Inv : SoundRules H (Head by Body)}
    → ⦃ i : ForwardInference Facts Hyps Body ⦄
    → TryInversion Facts Hyps Inv
  TryInversion-By {Head = Head} {Body} {Facts} {Hyps} {Inv} ⦃ failure ⦄ .NewFacts = []
  TryInversion-By {Head = Head} {Body} {Facts} {Hyps} {Inv} ⦃ failure ⦄ .NewHyps = []
  TryInversion-By {Head = Head} {Body} {Facts} {Hyps} {Inv} ⦃ failure ⦄ .new-proofs = λ _ _ _ → tt , tt
  TryInversion-By {Head = Head} {Body} {Facts} {Hyps} {Inv} ⦃ success pf ⦄ .NewFacts = rule-head-facts Head []
  TryInversion-By {Head = Head} {Body} {Facts} {Hyps} {Inv} ⦃ success pf ⦄ .NewHyps = rule-head-inversions Head []
  TryInversion-By {Head = Head} {Body} {Facts} {Hyps} {Inv} ⦃ success pf ⦄ .new-proofs =
    λ facts hyps h → rule-head-split Head (Inv .inversion-rules $* pf facts hyps $ h) tt tt

  TryRule-Or
    : {I : SoundRules H (Rs₁ or Rs₂)}
    → ⦃ i₁ : TryInversion Facts Hyps (Left-sound-rules I) ⦄
    → ⦃ i₂ : TryInversion Facts Hyps (Right-sound-rules I) ⦄
    → TryInversion Facts Hyps I
  TryRule-Or {Facts = Facts} {Hyps} {I} ⦃ i₁ ⦄ ⦃ i₂ ⦄ .NewFacts = i₁ .NewFacts ++ i₂ .NewFacts
  TryRule-Or {Facts = Facts} {Hyps} {I} ⦃ i₁ ⦄ ⦃ i₂ ⦄ .NewHyps = i₁ .NewHyps ++ i₂ .NewHyps
  TryRule-Or {Facts = Facts} {Hyps} {I} ⦃ i₁ ⦄ ⦃ i₂ ⦄ .new-proofs =
    λ facts hyps h →
      let (f₁ , h₁) = i₁ .new-proofs facts hyps h
          (f₂ , h₂) = i₂ .new-proofs facts hyps h
      in (f₁ ,* f₂) , (h₁ ,* h₂)

  -- If there are no more facts to try, then we fail.
  TryFacts-Fail
    : TryFacts [] Goal
  TryFacts-Fail = failure

  -- Solve a goal using a fact.
  TryFacts-Solve
    : TryFacts (Goal , Facts) Goal
  TryFacts-Solve {Facts = Facts} = success fst
  {-# OVERLAPS TryFacts-Solve #-}

  -- Try using the next fact to solve a goal.
  TryFacts-Next
    : ⦃ i : TryFacts Facts Goal ⦄
    → TryFacts (Fact , Facts) Goal
  TryFacts-Next {Facts = Facts} ⦃ i = failure ⦄ = failure
  TryFacts-Next {Facts = Facts} ⦃ i = success pf ⦄ = success (pf ∘ snd)

  TryFacts-False : TryFacts (⊥ , Facts) Goal
  TryFacts-False = success λ ff → absurd (fst ff)
  {-# OVERLAPPING TryFacts-False #-}

  -- If there are no more goals to solve, then we are done.
  ForwardInference-Done : ForwardInference Facts Hyps []
  ForwardInference-Done {Facts = Facts} {Hyps = Hyps} = success λ _ _ → tt

  -- Run all of our forward rules.
  ForwardInference-TryInversion
    : ⦃ I : Inversion H ⦄
    → ⦃ I? : TryInversion Facts Hyps (unbundle-inversion I) ⦄
    → ⦃ i* : ForwardInference (I? .NewFacts ++ H , Facts) (I? .NewHyps ++ Hyps) (Goal , Goals) ⦄
    → ForwardInference Facts (H , Hyps) (Goal , Goals)
  ForwardInference-TryInversion {Facts = Facts} {Hyps} ⦃ I = I ⦄ ⦃ I? ⦄ ⦃ failure ⦄ = failure
  ForwardInference-TryInversion {Facts = Facts} {Hyps} ⦃ I = I ⦄ ⦃ I? ⦄ ⦃ success pf ⦄ = success
    λ facts (h , hyps) →
      let (new-facts , new-inversions) = I? .new-proofs facts hyps h
      in pf (new-facts ,* (h , facts)) (new-inversions ,* hyps)
  {-# INCOHERENT ForwardInference-TryInversion #-}

  -- We try to use our facts once we've applied all of our forward lemmas.
  -- If we aren't able to resolve a goal by 'TryFacts', then we kill the search.
  ForwardInference-TryFacts
    : ⦃ Goal? : TryFacts Facts Goal ⦄
    → ⦃ WhenFoundFact Goal? (ForwardInference Facts [] Goals)  ⦄
    → ForwardInference Facts [] (Goal , Goals)
  ForwardInference-TryFacts {Facts = Facts} ⦃ Goal? = failure ⦄ ⦃ i* ⦄ = failure
  ForwardInference-TryFacts {Facts = Facts} ⦃ Goal? = success x ⦄ ⦃ failure ⦄ = failure
  ForwardInference-TryFacts {Facts = Facts} ⦃ Goal? = success pf-goal ⦄ ⦃ success pf-goals ⦄ = success
    λ facts _ → pf-goal facts , pf-goals facts tt


data FailWith (msg : String) : Typeω where

private
  failwith : String → Term → TC ⊤
  failwith str _ = typeError (strErr str ∷ [])

instance
  FailWith-Fail
    : ∀ {msg : String}
    → {@(tactic failwith msg) ff : ⊥}
    → FailWith msg
  FailWith-Fail {ff = ()}

inversion
  : ⦃ i* : ForwardInference [] (A , []) (B , []) ⦄
  → ⦃ _ : WhenInferenceFails i* (FailWith "Inversion failed.") ⦄
  → A → B
inversion ⦃ i* = success pf ⦄ a = fst (pf tt (a  , tt))

inversion-with
  : (Facts : Types)
  → ⦃ i* : ForwardInference Facts (A , []) (B , []) ⦄
  → ⦃ _ : WhenInferenceFails i* (FailWith "Inversion failed.") ⦄
  → Σ* Facts → A → B
inversion-with Facts ⦃ success pf ⦄ facts a = fst (pf facts (a  , tt))

-- Hacky tests.
private module Tests where
  open import Data.Vec.Base
  open import Data.Dec
  open import Data.Nat
  open import 1Lab.Prelude
  open import Meta.Invariant

  data Hamming {ℓ} {A : Type ℓ} : ∀ {n} → Vec A n → Vec A n → Nat → Type ℓ where
    zero : Hamming [] [] 0
    same
      : ∀ {n} {x y : A} {xs ys : Vec A n} {d}
      → x ≡ y → Hamming xs ys d
      → Hamming (x ∷ xs) (y ∷ ys) d
    diff
      : ∀ {n} {x y : A} {xs ys : Vec A n} {d}
      → x ≠ y → Hamming xs ys d
      → Hamming (x ∷ xs) (y ∷ ys) (suc d)

  private variable
    x y : A
    n d : Nat
    xs ys : Vec A n

  instance
    Inversion-Hamming-∷-zero
      : Inversion (Hamming (x ∷ xs) (y ∷ ys) 0)
    Inversion-Hamming-∷-zero {x = x} {xs = xs} {y} {ys} .rules =
      fact x ≡ y and inverting Hamming xs ys 0 by [] or
      fact ⊥ by x ≠ y , []
    Inversion-Hamming-∷-zero .inversion-rules .fst (same p h) = p , h
    Inversion-Hamming-∷-zero .inversion-rules .snd x≠y (same x=y h) = absurd (x≠y x=y)

    Inversion-Hamming-∷-suc
      : Inversion (Hamming (x ∷ xs) (y ∷ ys) (suc d))
    Inversion-Hamming-∷-suc {x = x} {xs = xs} {y} {ys} {d} .rules =
      inverting Hamming xs ys (suc d) by x ≡ y , [] or
      inverting Hamming xs ys d by x ≠ y , []
    Inversion-Hamming-∷-suc .inversion-rules .fst x=y (same _ h) = h
    Inversion-Hamming-∷-suc .inversion-rules .fst x=y (diff x≠y h) = absurd (x≠y x=y)
    Inversion-Hamming-∷-suc .inversion-rules .snd x≠y (same x=y h) = absurd (x≠y x=y)
    Inversion-Hamming-∷-suc .inversion-rules .snd x≠y (diff _ h) = h

    Inversion-Hamming-∷
      : Inversion (Hamming (x ∷ xs) (y ∷ ys) d)
    Inversion-Hamming-∷  {x = x} {xs = xs} {y} {ys} {d} .rules =
      inverting Hamming xs ys d by x ≡ y , [] or
      inverting Hamming xs ys (pred d) by x ≠ y , []
    Inversion-Hamming-∷ .inversion-rules .fst x=y (same _ s) = s
    Inversion-Hamming-∷ .inversion-rules .fst x=y (diff x≠y s) = absurd (x≠y x=y)
    Inversion-Hamming-∷ .inversion-rules .snd x≠y (same x=y h) = absurd (x≠y x=y)
    Inversion-Hamming-∷ .inversion-rules .snd x≠y (diff _ h) = h
    {-# OVERLAPS Inversion-Hamming-∷ #-}

  instance
    Dec-Hamming
      : ∀ {xs ys : Vec A n} {d : Nat}
      → ⦃ _ : Discrete A ⦄
      → Dec (Hamming xs ys d)
    Dec-Hamming {xs = []} {ys = []} {d = zero} = yes zero
    Dec-Hamming {xs = []} {ys = []} {d = suc d} = no λ ()
    Dec-Hamming {xs = x ∷ xs} {ys = y ∷ ys} {d = d} with x ≡? y
    Dec-Hamming {A = _} {_} {x ∷ xs} {y ∷ ys} {d = d} | yes x=y =
      invmap (same x=y) (inversion-with (x ≡ y , []) (x=y , tt)) (holds? (Hamming xs ys d))
    Dec-Hamming {A = _} {_} {x ∷ xs} {y ∷ ys} {d = d} | no ¬x=y =
      -- This should be forwards chaining?
      -- There are two valid constructors here:

      -- Backwards (Hamming (x ∷ xs) (y ∷ ys) d) via
      --   constructing Hamming xs ys (pred d) by x ≠ y or
      --   constructing Hamming (x ∷ xs) (y ∷ ys) d by x ≡ y
      invmap {!!} (inversion-with (x ≠ y , []) (¬x=y , tt)) (holds? (Hamming xs ys (pred d)))
