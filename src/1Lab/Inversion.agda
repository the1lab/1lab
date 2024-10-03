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

record Inversion_via_ {ℓ} (A : Type ℓ) (Rs : Rules A) : Typeω where
  field
    inversion-rules : Rules-sound Rs


infix -1 Inversion_via_
open Inversion_via_

inversionl
  : ∀ {ℓ} {A : Type ℓ} {Rs₁ Rs₂ : Rules A}
  → Inversion A via (Rs₁ or Rs₂)
  → Inversion A via Rs₁
inversionl I .inversion-rules = I .inversion-rules .fst

inversionr
  : ∀ {ℓ} {A : Type ℓ} {Rs₁ Rs₂ : Rules A}
  → Inversion A via (Rs₁ or Rs₂)
  → Inversion A via Rs₂
inversionr I .inversion-rules = I .inversion-rules .snd

instance
  -- Default 'Inversion' instance that treats 'A' as a fact.
  Inversion-Default
    : ∀ {ℓ} {A : Type ℓ}
    → Inversion A via
        fact A by []
  Inversion-Default .inversion-rules a = a
  {-# INCOHERENT Inversion-Default #-}

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
  success : (Facts →* Hyps →* Σ* Goals) → ForwardInference Facts Hyps Goals

data TryFacts (Facts : Types) (Goal : Type ℓ) : Typeω where
  failure : TryFacts Facts Goal
  success : (Facts →* Goal) → TryFacts Facts Goal

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

record TryInversion (Facts : Types) (Hyps : Types) (I : Inversion H via Rs) : Typeω where
  field
    NewFacts : Types
    NewHyps : Types
    new-proofs : Facts →* Hyps →* (H → Σ* NewFacts × Σ* NewHyps)

open TryInversion

instance
  TryInversion-By
    : { I : Inversion H via (Head by Body) }
    → ⦃ i : ForwardInference Facts Hyps Body ⦄
    → TryInversion Facts Hyps I
  TryInversion-By {Head = Head} {Body} {Facts} {Hyps} {I} ⦃ failure ⦄ .NewFacts = []
  TryInversion-By {Head = Head} {Body} {Facts} {Hyps} {I} ⦃ failure ⦄ .NewHyps = []
  TryInversion-By {Head = Head} {Body} {Facts} {Hyps} {I} ⦃ failure ⦄ .new-proofs = const* Facts (const* Hyps λ _ → tt , tt)
  TryInversion-By {Head = Head} {Body} {Facts} {Hyps} {I} ⦃ success pf ⦄ .NewFacts = rule-head-facts Head []
  TryInversion-By {Head = Head} {Body} {Facts} {Hyps} {I} ⦃ success pf ⦄ .NewHyps = rule-head-inversions Head []
  TryInversion-By {Head = Head} {Body} {Facts} {Hyps} {I} ⦃ success pf ⦄ .new-proofs =
    λ* Facts λ facts → λ* Hyps λ hyps h →
      rule-head-split Head (I .inversion-rules $* (pf $* facts $* hyps) $ h) tt tt

  TryRule-Or
    : {I : Inversion H via (Rs₁ or Rs₂)}
    → ⦃ i₁ : TryInversion Facts Hyps (inversionl I) ⦄
    → ⦃ i₂ : TryInversion Facts Hyps (inversionr I) ⦄
    → TryInversion Facts Hyps I
  TryRule-Or {Facts = Facts} {Hyps} {I} ⦃ i₁ ⦄ ⦃ i₂ ⦄ .NewFacts = i₁ .NewFacts ++ i₂ .NewFacts
  TryRule-Or {Facts = Facts} {Hyps} {I} ⦃ i₁ ⦄ ⦃ i₂ ⦄ .NewHyps = i₁ .NewHyps ++ i₂ .NewHyps
  TryRule-Or {Facts = Facts} {Hyps} {I} ⦃ i₁ ⦄ ⦃ i₂ ⦄ .new-proofs =
    λ* Facts λ facts → λ* Hyps λ hyps h →
    let (f₁ , h₁) = i₁ .new-proofs $* facts $* hyps $ h
        (f₂ , h₂) = i₂ .new-proofs $* facts $* hyps $ h
    in (f₁ ,* f₂) , (h₁ ,* h₂)

  -- If there are no more facts to try, then we fail.
  TryFacts-Fail
    : TryFacts [] Goal
  TryFacts-Fail = failure

  -- Solve a goal using a fact.
  TryFacts-Solve
    : TryFacts (Goal , Facts) Goal
  TryFacts-Solve {Facts = Facts} = success (λ goal → const* Facts goal)
  {-# OVERLAPPING TryFacts-Solve #-}

  -- Try using the next fact to solve a goal.
  TryFacts-Next
    : ⦃ i : TryFacts Facts Goal ⦄
    → TryFacts (Fact , Facts) Goal
  TryFacts-Next {Facts = Facts} ⦃ i = failure ⦄ = failure
  TryFacts-Next {Facts = Facts} ⦃ i = success pf ⦄ = success (λ _ → pf)

  -- If there are no more goals to solve, then we are done.
  ForwardInference-Done : ForwardInference Facts Hyps []
  ForwardInference-Done {Facts = Facts} {Hyps = Hyps} = success (const* Facts (const* Hyps tt))

  -- Run all of our forward rules.
  ForwardInference-TryInversion
    : ⦃ I : Inversion H via Rs ⦄
    → ⦃ I? : TryInversion Facts Hyps I ⦄
    → ⦃ i* : ForwardInference (I? .NewFacts ++ H , Facts) (I? .NewHyps ++ Hyps) (Goal , Goals) ⦄
    → ForwardInference Facts (H , Hyps) (Goal , Goals)
  ForwardInference-TryInversion {Facts = Facts} {Hyps} ⦃ I = I ⦄ ⦃ I? ⦄ ⦃ failure ⦄ = failure
  ForwardInference-TryInversion {Facts = Facts} {Hyps} ⦃ I = I ⦄ ⦃ I? ⦄ ⦃ success pf ⦄ = success
    (λ* Facts λ facts h → λ* Hyps λ hyps →
      let (new-facts , new-proofs) = I? .new-proofs $* facts $* hyps $ h
      in pf $* (new-facts ,* (h , facts)) $* (new-proofs ,* hyps))
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
    (λ* Facts λ facts → (pf-goal $* facts) , (pf-goals $* facts))


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
inversion ⦃ i* = success pf ⦄ a = fst (pf a)

inversion-with
  : (Facts : Types)
  → ⦃ i* : ForwardInference Facts (A , []) (B , []) ⦄
  → ⦃ _ : WhenInferenceFails i* (FailWith "Inversion failed.") ⦄
  → Σ* Facts → A → B
inversion-with Facts ⦃ success pf ⦄ facts a = fst (pf $* facts $ a)
