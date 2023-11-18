<!--
```agda
open import 1Lab.Prelude hiding (_∈_)

open import Data.Bool
open import Data.Fin using (Fin; fzero; fsuc; weaken; inject)
open import Data.List hiding (_++_)
open import Data.Nat
open import Data.Sum

open import Meta.Brackets
```
-->

```agda
module Logic.Propositional.Classical where
```

# Classical Propositional Logic

```agda
data Proposition (Γ : Nat) : Type where
  var : Fin Γ → Proposition Γ
  “⊤” : Proposition Γ
  “⊥” : Proposition Γ
  _“∧”_ : Proposition Γ → Proposition Γ → Proposition Γ
  _“∨”_ : Proposition Γ → Proposition Γ → Proposition Γ
  “¬”_ : Proposition Γ → Proposition Γ

data Ctx (Γ : Nat) : Type where
  [] : Ctx Γ
  _⨾_ : Ctx Γ → Proposition Γ → Ctx Γ

_++_ : ∀ {Γ} → Ctx Γ → Ctx Γ → Ctx Γ
ψ ++ [] = ψ
ψ ++ (θ ⨾ P) = (ψ ++ θ) ⨾ P

data _∈_ {Γ : Nat} (P : Proposition Γ) : Ctx Γ → Type where
  here : ∀ {ψ} → P ∈ (ψ ⨾ P)
  there : ∀ {ψ Q} → P ∈ ψ → P ∈ (ψ ⨾ Q)

infixr 12 _“⇒”_
infixr 11 _“∧”_
infixr 10 _“∨”_
infixl 10 _⨾_
infix 9 _⊢_ _⊨_

data _⊢_ {Γ : Nat} (ψ : Ctx Γ) : Proposition Γ → Type where
  hyp : ∀ {P} → P ∈ ψ → ψ ⊢ P
  ⊤-intro : ψ ⊢ “⊤”
  ⊥-elim : ∀ {P} → ψ ⊢ “⊥” → ψ ⊢ P
  ∧-intro : ∀ {P Q} → ψ ⊢ P → ψ ⊢ Q → ψ ⊢ P “∧” Q
  ∧-elim-l : ∀ {P Q} → ψ ⊢ P “∧” Q → ψ ⊢ P
  ∧-elim-r : ∀ {P Q} → ψ ⊢ P “∧” Q → ψ ⊢ Q
  ∨-intro-l : ∀ {P Q} → ψ ⊢ P → ψ ⊢ P “∨” Q
  ∨-intro-r : ∀ {P Q} → ψ ⊢ Q → ψ ⊢ P “∨” Q
  ∨-elim : ∀ {P Q R} → ψ ⊢ P “∨” Q → ψ ⨾ P ⊢ R → ψ ⨾ Q ⊢ R → ψ ⊢ R
  ¬-intro : ∀ {P} → ψ ⨾ P ⊢ “⊥” → ψ ⊢ “¬” P
  ¬-elim : ∀ {P} → ψ ⊢ “¬” P → ψ ⊢ P → ψ ⊢ “⊥”
  dneg-elim : ∀ {P} → ψ ⊢ “¬” (“¬” P) → ψ ⊢ P
```

<!--
```agda
private variable
  Γ Δ Θ : Nat
  ψ θ ζ : Ctx Γ
  P Q R : Proposition Γ
```
-->

## Weakening

```agda
data Weakening (Γ : Nat) : Nat → Type where
  done : Weakening Γ Γ
  weak : ∀ {Δ} → Weakening (suc Γ) Δ → Weakening Γ Δ

¬weaken-suc-zero : Weakening (suc Γ) 0 → ⊥
¬weaken-suc-zero (weak σ) = ¬weaken-suc-zero σ

inc-prop : Proposition Γ → Proposition (suc Γ)
inc-prop (var x) = var (weaken x)
inc-prop “⊤” = “⊤”
inc-prop “⊥” = “⊥”
inc-prop (p “∧” q) = inc-prop p “∧” inc-prop q
inc-prop (p “∨” q) = inc-prop p “∨” inc-prop q
inc-prop (“¬” p) = “¬” (inc-prop p)

inc-ctx : Ctx Γ → Ctx (suc Γ)
inc-ctx [] = []
inc-ctx (ψ ⨾ P) = inc-ctx ψ ⨾ inc-prop P

inc-var : P ∈ ψ → inc-prop P ∈ inc-ctx ψ
inc-var here = here
inc-var (there x) = there (inc-var x)

inc-proof : ψ ⊢ P → inc-ctx ψ ⊢ inc-prop P
inc-proof (hyp x) = hyp (inc-var  x)
inc-proof ⊤-intro = ⊤-intro
inc-proof (⊥-elim p) = ⊥-elim (inc-proof p)
inc-proof (∧-intro p q) = ∧-intro (inc-proof p) (inc-proof q)
inc-proof (∧-elim-l p) = ∧-elim-l (inc-proof p)
inc-proof (∧-elim-r p) = ∧-elim-r (inc-proof p)
inc-proof (∨-intro-l p) = ∨-intro-l (inc-proof p)
inc-proof (∨-intro-r p) = ∨-intro-r (inc-proof p)
inc-proof (∨-elim p q r) = ∨-elim (inc-proof p) (inc-proof q) (inc-proof r)
inc-proof (¬-intro p) = ¬-intro (inc-proof p)
inc-proof (¬-elim p q) = ¬-elim (inc-proof p) (inc-proof q)
inc-proof (dneg-elim p) = dneg-elim (inc-proof p)

wk-var : Weakening Γ Δ → Fin Γ → Fin Δ
wk-var done x = x
wk-var (weak σ) x = wk-var σ (fsuc x)

wk-prop : Weakening Γ Δ → Proposition Γ → Proposition Δ
wk-prop done P = P
wk-prop (weak σ) P = wk-prop σ (inc-prop P)

wk-ctx : Weakening Γ Δ → Ctx Γ → Ctx Δ
wk-ctx done ψ = ψ
wk-ctx (weak σ) ψ = wk-ctx σ (inc-ctx ψ)

wk-proof : (σ : Weakening Γ Δ) → ψ ⊢ P → wk-ctx σ ψ ⊢ wk-prop σ P
wk-proof done pf = pf
wk-proof (weak σ) pf = wk-proof σ (inc-proof pf)
```

## Renamings

```agda
data Rename {Γ} : Ctx Γ → Ctx Γ → Type where
  done : Rename [] []
  drop : ∀ {ψ θ P} → Rename ψ θ → Rename (ψ ⨾ P) θ
  keep : ∀ {ψ θ P} → Rename ψ θ → Rename (ψ ⨾ P) (θ ⨾ P)

idrn : Rename ψ ψ
idrn {ψ = []} = done
idrn {ψ = ψ ⨾ P} = keep (idrn {ψ = ψ})

_∘rn_ : Rename θ ζ → Rename ψ θ → Rename ψ ζ 
p ∘rn done = p
p ∘rn drop q = drop (p ∘rn q)
drop p ∘rn keep q = drop (p ∘rn q)
keep p ∘rn keep q = keep (p ∘rn q)

!rn : Rename ψ []
!rn {ψ = []} = done
!rn {ψ = ψ ⨾ x} = drop !rn

π₁-rn : Rename (ψ ++ θ) ψ
π₁-rn {θ = []} = idrn
π₁-rn {θ = θ ⨾ P} = drop π₁-rn

π₂-rn : Rename (ψ ++ θ) θ
π₂-rn {θ = []} = !rn
π₂-rn {θ = θ ⨾ P} = keep π₂-rn

rename-hyp : Rename ψ θ → P ∈ θ → P ∈ ψ
rename-hyp (drop rn) mem = there (rename-hyp rn mem)
rename-hyp (keep rn) here = here
rename-hyp (keep rn) (there mem) = there (rename-hyp rn mem)

rename : Rename ψ θ → θ ⊢ P → ψ ⊢ P
rename rn (hyp x) = hyp (rename-hyp rn x)
rename rn ⊤-intro = ⊤-intro
rename rn (⊥-elim p) = ⊥-elim (rename rn p)
rename rn (∧-intro p q) = ∧-intro (rename rn p) (rename rn q)
rename rn (∧-elim-l p) = ∧-elim-l (rename rn p)
rename rn (∧-elim-r p) = ∧-elim-r (rename rn p)
rename rn (∨-intro-l p) = ∨-intro-l (rename rn p)
rename rn (∨-intro-r p) = ∨-intro-r (rename rn p)
rename rn (∨-elim p q r) = ∨-elim (rename rn p) (rename (keep rn) q) (rename (keep rn) r)
rename rn (¬-intro p) = ¬-intro (rename (keep rn) p)
rename rn (¬-elim p q) = ¬-elim (rename rn p) (rename rn q)
rename rn (dneg-elim p) = dneg-elim (rename rn p)
```

## Some Elementary Theorems

```agda
lem : ∀ {Γ} {ψ : Ctx Γ} (P : Proposition Γ) → ψ ⊢ P “∨” (“¬” P)
lem P =
  dneg-elim $
  ¬-intro $
  ¬-elim (hyp here) $
  ∨-intro-r $
  ¬-intro $
  ¬-elim (hyp (there here)) $
  ∨-intro-l (hyp here)

dneg-intro : ψ ⊢ P → ψ ⊢ “¬” (“¬” P)
dneg-intro p = ¬-intro (¬-elim (hyp here) (rename (drop idrn) p))

¬∧-intro-l : ψ ⊢ “¬” P → ψ ⊢ “¬” (P “∧” Q)
¬∧-intro-l p = ¬-intro (¬-elim (rename (drop idrn) p) (∧-elim-l (hyp here)))

¬∧-intro-r : ψ ⊢ “¬” Q → ψ ⊢ “¬” (P “∧” Q)
¬∧-intro-r p = ¬-intro (¬-elim (rename (drop idrn) p) (∧-elim-r (hyp here)))

¬∧-elim : ψ ⊢ “¬” (P “∧” Q) → ψ ⊢ (“¬” P) “∨” (“¬” Q)
¬∧-elim {P = P} {Q = Q} p =
  ∨-elim (lem P)
    (∨-elim (lem Q)
      (⊥-elim
        (¬-elim (rename (drop (drop idrn)) p)
        (∧-intro (hyp (there here)) (hyp here))))
      (∨-intro-r (hyp here)))
    (∨-intro-l (hyp here))

¬∨-intro : ψ ⊢ “¬” P → ψ ⊢ “¬” Q → ψ ⊢ “¬” (P “∨” Q)
¬∨-intro p q =
  ¬-intro $
  ∨-elim (hyp here)
    (¬-elim (rename (drop (drop idrn)) p) (hyp here))
    (¬-elim (rename (drop (drop idrn)) q) (hyp here))

opaque
  _“⇒”_ : ∀ {Γ} → Proposition Γ → Proposition Γ → Proposition Γ
  P “⇒” Q = (“¬” P) “∨” Q
  
  ⇒-intro : ψ ⨾ P ⊢ Q → ψ ⊢ P “⇒” Q
  ⇒-intro {P = P} pf = ∨-elim (lem P) (∨-intro-r pf) (∨-intro-l (hyp here))
  
  ⇒-elim : ψ ⊢ P “⇒” Q → ψ ⊢ P → ψ ⊢ Q
  ⇒-elim {Q = Q} imp p =
    ∨-elim imp
      (⊥-elim (¬-elim (hyp here) (rename (drop idrn) p)))
      (hyp here)

⇒-uncurry : ψ ⊢ P “⇒” Q → ψ ⨾ P ⊢ Q
⇒-uncurry p = ⇒-elim (rename (drop idrn) p) (hyp here)

⇒-flip : ψ ⊢ P “⇒” Q “⇒” R → ψ ⊢ Q “⇒” P “⇒” R
⇒-flip p =
  ⇒-intro $ ⇒-intro $
  ⇒-elim
    (⇒-elim (rename (drop (drop idrn)) p) (hyp here))
    (hyp (there here))

“⋀” : Ctx Γ → Proposition Γ
“⋀” [] = “⊤”
“⋀” (ψ ⨾ P) = “⋀” ψ “∧” P

⋀-intro : (∀ {P} → P ∈ ψ → θ ⊢ P) → θ ⊢ “⋀” ψ  
⋀-intro {ψ = []} pfs = ⊤-intro
⋀-intro {ψ = ψ ⨾ P} pfs = ∧-intro (⋀-intro (pfs ∘ there)) (pfs here)

⋀-elim : P ∈ ψ → θ ⊢ “⋀” ψ → θ ⊢ P
⋀-elim here p = ∧-elim-r p
⋀-elim (there x) p = ⋀-elim x (∧-elim-l p)

_“⇛”_ : Ctx Γ → Proposition Γ → Proposition Γ
[] “⇛” P = P
(ψ ⨾ Q) “⇛” P = ψ “⇛” (Q “⇒” P)

⇛-intro : θ ++ ψ ⊢ P → θ ⊢ ψ “⇛” P
⇛-intro {ψ = []} p = p
⇛-intro {ψ = ψ ⨾ Q} p = ⇛-intro (⇒-intro p)

⇛-uncurry : θ ⊢ ψ “⇛” P → θ ++ ψ ⊢ P
⇛-uncurry {ψ = []} p = p
⇛-uncurry {ψ = ψ ⨾ Q} p = ⇒-uncurry (⇛-uncurry p)

⇛-closed : [] ⊢ ψ “⇛” P → ψ ⊢ P
⇛-closed {ψ = []} p = p
⇛-closed {ψ = ψ ⨾ Q} p = ⇒-uncurry (⇛-closed p)

⇛-elim : θ ⊢ (ψ ⨾ P) “⇛” Q → θ ⊢ P → θ ⊢ ψ “⇛” Q
⇛-elim {ψ = ψ} p q = ⇛-intro (⇒-elim (⇛-uncurry {ψ = ψ} p) (rename π₁-rn q))
```

## Semantics

```agda
sem-prop : ∀ {Γ} → Proposition Γ → (Fin Γ → Bool) → Bool
sem-prop (var x) ρ = ρ x
sem-prop “⊤” ρ = true
sem-prop “⊥” ρ = false
sem-prop (P “∧” Q) ρ = and (sem-prop P ρ) (sem-prop Q ρ)
sem-prop (P “∨” Q) ρ = or (sem-prop P ρ) (sem-prop Q ρ)
sem-prop (“¬” P) ρ = not (sem-prop P ρ)

sem-ctx : ∀ {Γ} → Ctx Γ → (Fin Γ → Bool) → Bool
sem-ctx ψ ρ = sem-prop (“⋀” ψ) ρ

instance
  ⟦⟧-Proposition : ∀ {Γ} → ⟦⟧-notation (Proposition Γ)
  ⟦⟧-Proposition {Γ = Γ} = brackets ((Fin Γ → Bool) → Bool) sem-prop

  ⟦⟧-Ctx : ∀ {Γ} → ⟦⟧-notation (Ctx Γ)
  ⟦⟧-Ctx {Γ = Γ} = brackets ((Fin Γ → Bool) → Bool) sem-ctx

opaque
  unfolding _“⇒”_
  ⇒-sem
    : ∀ {Γ} {P Q : Proposition Γ}
    → ∀ (ρ : Fin Γ → Bool) → ⟦ P “⇒” Q ⟧ ρ ≡ imp (⟦ P ⟧ ρ) (⟦ Q ⟧ ρ)
  ⇒-sem {P = P} {Q = Q} ρ =
    imp-not-or (⟦ P ⟧ ρ) (⟦ Q ⟧ ρ)

_⊨_ : ∀ {Γ} → Ctx Γ → Proposition Γ → Type
_⊨_ {Γ} ψ P = ∀ (ρ : Fin Γ → Bool) → ⟦ ψ ⟧ ρ ≡ true → ⟦ P ⟧ ρ ≡ true
```

## Soundness

```agda
hyp-sound : ∀ {Γ} {ψ : Ctx Γ} {P : Proposition Γ} → P ∈ ψ → ψ ⊨ P
hyp-sound here ρ hyps-true = and-reflect-true-r hyps-true
hyp-sound (there m) ρ hyps-true = hyp-sound m ρ (and-reflect-true-l hyps-true)

sound : ψ ⊢ P → ψ ⊨ P
sound (hyp x) ρ hyps-true = hyp-sound x ρ hyps-true
sound ⊤-intro ρ hyps-true = refl
sound (⊥-elim p) ρ hyps-true =
  absurd (true≠false (sym (sound p ρ hyps-true)))
sound (∧-intro p q) ρ hyps-true =
  ap₂ and (sound p ρ hyps-true) (sound q ρ hyps-true)
sound (∧-elim-l p) ρ hyps-true =
  and-reflect-true-l (sound p ρ hyps-true)
sound (∧-elim-r p) ρ hyps-true =
  and-reflect-true-r (sound p ρ hyps-true)
sound (∨-intro-l p) ρ hyps-true =
  ap₂ or (sound p ρ hyps-true) refl
sound (∨-intro-r p) ρ hyps-true =
  ap₂ or refl (sound p ρ hyps-true) ∙ or-truer _
sound (∨-elim p q r) ρ hyps-true =
  [ (λ P-true → sound q ρ (ap₂ and hyps-true P-true))
  , (λ Q-true → sound r ρ (ap₂ and hyps-true Q-true))
  ] (or-reflect-true (sound p ρ hyps-true))
sound (¬-intro {P = P} p) ρ hyps-true =
  Bool-elim (λ b → ⟦ P ⟧ ρ ≡ b → not b ≡ true)
    (λ P-true → sound p ρ (ap₂ and hyps-true P-true))
    (λ _ → refl)
    (⟦ P ⟧ ρ) refl
sound (¬-elim {P = P} p q) ρ hyps-true =
  absurd $ not-no-fixed (sound q ρ hyps-true ∙ sym (sound p ρ hyps-true))
sound (dneg-elim {P = P} p) ρ hyps-true =
  sym (not-involutive (⟦ P ⟧ ρ)) ∙ sound p ρ hyps-true
```

## Satisfiability

```agda
is-satisfiable : Proposition Γ → Type _
is-satisfiable {Γ = Γ} P = Σ[ ρ ∈ (Fin Γ → Bool) ] (⟦ P ⟧ ρ ≡ true)

equisat : Proposition Γ → Proposition Δ → Type _
equisat P Q =
  (is-satisfiable P → is-satisfiable Q) ×
  (is-satisfiable Q → is-satisfiable P)
```
