<!--
```agda
open import 1Lab.Prelude

open import Data.Bool
open import Data.Dec
open import Data.Fin using (Fin; fzero; fsuc; Discrete-Fin; avoid; _[_≔_]; delete)
open import Data.List hiding (_++_)
open import Data.Nat
open import Data.Sum

open import Logic.Propositional.Classical
open import Logic.Propositional.Classical.CNF

open import Meta.Brackets

import Data.Fin as Fin
```
-->

```agda
module Logic.Propositional.Classical.SAT where
```

<!--
```agda
private variable
  Γ Δ Θ : Nat
  ψ θ ζ : Ctx Γ
  P Q R : Proposition Γ
```
-->

# Unit Propagation

```agda
delete-literals
  : (x : Fin (suc Γ))
  → (ϕ : Disjunction (suc Γ))
  → Disjunction Γ
delete-literals {Γ = zero} i ϕ = []
delete-literals {Γ = suc Γ} i [] = []
delete-literals {Γ = suc Γ} i (x ∷ ϕ) =
  Dec-rec
    (λ _ → delete-literals i ϕ)
    (λ i≠x → avoid-lit i x i≠x ∷ delete-literals i ϕ)
    (Discrete-Fin i (lit-var x))

unit-propagate : Literal (suc Γ) → CNF (suc Γ) → CNF Γ
unit-propagate x [] = []
unit-propagate x (ϕ ∷ ϕs) =
  Dec-rec
    (λ _ → unit-propagate x ϕs)
    (λ _ → delete-literals (lit-var x) ϕ ∷ unit-propagate x ϕs)
    (elem? Discrete-Literal x ϕ)
```

```agda
avoid-lit-insert
  : ∀ (x y : Literal (suc Γ)) → (x≠y : ¬ (lit-var x ≡ lit-var y))
  → (ρ : Fin Γ → Bool)
  → ⟦ y ⟧ (ρ [ lit-var x ≔ lit-val x ]) ≡ ⟦ avoid-lit (lit-var x) y x≠y ⟧ ρ
avoid-lit-insert {Γ = Γ} x (lit y) x≠y ρ = Fin.avoid-insert ρ (lit-var x) (lit-val x) y x≠y
avoid-lit-insert {Γ = Γ} x (neg y) x≠y ρ = ap not (Fin.avoid-insert ρ (lit-var x) (lit-val x) y x≠y)

lit-assign-neg-false
  : ∀ (x : Literal (suc Γ))
  → (ρ : Fin Γ → Bool)
  → ⟦ x ⟧ (ρ [ lit-var (¬lit x) ≔ lit-val (¬lit x) ]) ≡ false
lit-assign-neg-false (lit x) ρ = Fin.insert-lookup ρ x false
lit-assign-neg-false (neg x) ρ = ap not (Fin.insert-lookup ρ x true)

lit-assign-true
  : ∀ (x : Literal (suc Γ))
  → (ρ : Fin Γ → Bool)
  → ⟦ x ⟧ (ρ [ lit-var x ≔ lit-val x ]) ≡ true
lit-assign-true (lit x) ρ = Fin.insert-lookup ρ x true
lit-assign-true (neg x) ρ = ap not (Fin.insert-lookup ρ x false)

delete-literals-sound
  : (x : Literal (suc Γ))
  → (ϕ : Disjunction (suc Γ))
  → ¬ (x ∈ₗ ϕ)
  → ∀ (ρ : Fin Γ → Bool)
  → ⟦ ϕ ⟧ (ρ [ lit-var x ≔ lit-val x ]) ≡ ⟦ delete-literals (lit-var x) ϕ ⟧ ρ
delete-literals-sound {zero} x [] x∉ϕ ρ = refl
delete-literals-sound {zero} (lit fzero) (lit fzero ∷ ϕ) x∉ϕ ρ =
  absurd (x∉ϕ (inl refl))
delete-literals-sound {zero} (lit fzero) (neg fzero ∷ ϕ) x∉ϕ ρ =
  delete-literals-sound (lit fzero) ϕ (x∉ϕ ∘ inr) ρ
delete-literals-sound {zero} (neg fzero) (lit fzero ∷ ϕ) x∉ϕ ρ =
  delete-literals-sound (neg fzero) ϕ (x∉ϕ ∘ inr) ρ
delete-literals-sound {zero} (neg fzero) (neg fzero ∷ ϕ) x∉ϕ ρ =
  absurd (x∉ϕ (inl refl))
delete-literals-sound {suc Γ} x [] x∉ϕ ρ = refl
delete-literals-sound {suc Γ} x (y ∷ ϕ) x∉ϕ ρ with Discrete-Fin (lit-var x) (lit-var y)
... | yes x=y =
  ap₂ or
    (subst (λ e → ⟦ y ⟧ (ρ [ lit-var e ≔ lit-val e ]) ≡ false)
      (sym (literal-eq-negate x y (x∉ϕ ∘ inl) x=y))
      (lit-assign-neg-false y ρ))
    refl
  ∙ delete-literals-sound x ϕ (x∉ϕ ∘ inr) ρ
... | no x≠y =
  ap₂ or
    (avoid-lit-insert x y x≠y ρ)
    (delete-literals-sound x ϕ (x∉ϕ ∘ inr) ρ)

unit-propagate-sound
  : (x : Literal (suc Γ))
  → (ϕs : CNF (suc Γ))
  → ∀ (ρ : Fin Γ → Bool)
  → ⟦ ϕs ⟧ (ρ [ lit-var x ≔ lit-val x ]) ≡ ⟦ unit-propagate x ϕs ⟧ ρ
unit-propagate-sound x [] ρ = refl
unit-propagate-sound x (ϕ ∷ ϕs) ρ with elem? Discrete-Literal x ϕ
... | yes x∈ϕ =
  ap₂ and
    (any-one-of (λ l → ⟦ l ⟧ (ρ [ lit-var x ≔ lit-val x ]))
      x ϕ x∈ϕ
      (lit-assign-true x ρ))
    (unit-propagate-sound x ϕs ρ)
... | no ¬x∉ϕ =
  ap₂ and
    (delete-literals-sound x ϕ ¬x∉ϕ ρ)
    (unit-propagate-sound x ϕs ρ)

unit-propagate-complete
  : (x : Literal (suc Γ))
  → (ϕs : CNF (suc Γ))
  → ∀ (ρ : Fin (suc Γ) → Bool)
  → ⟦ x ⟧ ρ ≡ true
  → ⟦ ϕs ⟧ ρ ≡ ⟦ unit-propagate x ϕs ⟧ (delete ρ (lit-var x))
unit-propagate-complete x ϕs ρ x-true =
  ap ⟦ ϕs ⟧ (sym $ funext $
    Fin.insert-delete ρ (lit-var x) (lit-val x) (literal-sat-val x ρ x-true))
  ∙ unit-propagate-sound x ϕs (delete ρ (lit-var x))
```

```agda
has-unit-clause? : ∀ (ϕs : CNF Γ) → Dec (Σ[ x ∈ Literal Γ ] ((x ∷ []) ∈ₗ ϕs))
has-unit-clause? [] = no (Lift.lower ∘ snd)
has-unit-clause? ([] ∷ ϕs) =
  Dec-rec
    (λ (x , x∈ϕs) → yes (x , inr x∈ϕs))
    (λ ¬ϕ-unit → no (λ (x , x∈ϕs) →
      [ ∷≠[]
      , (λ x∈ϕs → ¬ϕ-unit (x , x∈ϕs))
      ] x∈ϕs))
    (has-unit-clause? ϕs)
has-unit-clause? ((x ∷ []) ∷ ϕs) = yes (x , inl refl)
has-unit-clause? ((x ∷ y ∷ ϕ) ∷ ϕs) =
  Dec-rec
    (λ (x , x∈ϕs) → yes (x , inr x∈ϕs))
    (λ ¬ϕ-unit → no (λ (x , x∈ϕs) →
      [ ∷≠[] ∘ ∷-tail-inj ∘ sym
      , (λ x∈ϕs → ¬ϕ-unit (x , x∈ϕs))
      ] x∈ϕs))
    (has-unit-clause? ϕs)

unit-clause-sat
  : (x : Literal Γ)
  → (ϕs : CNF Γ)
  → (x ∷ []) ∈ₗ ϕs
  → (ρ : Fin Γ → Bool)
  → ⟦ ϕs ⟧ ρ ≡ true
  → ⟦ x ⟧ ρ ≡ true
unit-clause-sat x (ϕ ∷ ϕs) (inl [x]=ϕ) ρ ϕs-sat =
  sym (or-falser _)
  ∙ ap (λ e → (⟦ e ⟧ ρ)) [x]=ϕ
  ∙ and-reflect-true-l ϕs-sat
unit-clause-sat x (y ∷ ϕs) (inr [x]∈ϕs) ρ ϕs-sat =
  unit-clause-sat x ϕs [x]∈ϕs ρ (and-reflect-true-r ϕs-sat)
```


# Pure Literal Elimination

```agda
is-pure-literal : Fin Γ → CNF Γ → Type
is-pure-literal {Γ = Γ} i ϕs =
  Σ[ b ∈ Bool ] (∀ ϕ → ϕ ∈ₗ ϕs → (x : Literal Γ) → x ∈ₗ ϕ → lit-var x ≡ i → lit-val x ≡ b)
  -- {!∀ ϕ → ϕ ∈ₗ !} ⊎ {!!}
  -- (∀ ϕ → ϕ ∈ₗ ϕs → x ∈ₗ ϕ → ?) ⊎
  -- (∀ ϕ → ϕ ∈ₗ ϕs → x ∈ₗ ϕ → ?)

-- is-pure-literal? : (x : Literal Γ) → (ϕs : CNF Γ) → Dec (is-pure-literal x ϕs)
-- is-pure-literal? x [] = yes (inl λ _ ff _ → absurd (Lift.lower ff))
-- is-pure-literal? x (y ∷ ϕs) = {!!}
-- data Polarity -- : Type where
--   pos : Polarity
--   neg : Polarity
--   mixed : Polarity
--   none : Polarity

-- _⊗p_ : Polarity → Polarity → Polarity
-- pos ⊗p pos = pos
-- pos ⊗p neg = mixed
-- pos ⊗p mixed = mixed
-- pos ⊗p none = pos
-- neg ⊗p pos = mixed
-- neg ⊗p neg = neg
-- neg ⊗p mixed = mixed
-- neg ⊗p none = neg
-- mixed ⊗p q = mixed
-- none ⊗p q = q

-- is-pos : Polarity → Type
-- is-pos pos = ⊤
-- is-pos neg = ⊥
-- is-pos mixed = ⊥
-- is-pos none = ⊥

-- pos≠neg : pos ≡ neg → ⊥
-- pos≠neg p = subst is-pos p tt 

-- Discrete-Polarity : Discrete Polarity
-- Discrete-Polarity pos pos = yes refl
-- Discrete-Polarity pos neg = no pos≠neg
-- Discrete-Polarity pos mixed = {!!}
-- Discrete-Polarity pos none = {!!}
-- Discrete-Polarity neg q = {!!}
-- Discrete-Polarity mixed q = {!!}
-- Discrete-Polarity none q = {!!}

-- lit-polarity : Literal Γ → Polarity
-- lit-polarity (lit _) = pos
-- lit-polarity (neg _) = neg

-- disj-polarity : Fin Γ → Disjunction Γ → Polarity
-- disj-polarity i [] = none
-- disj-polarity i (x ∷ ϕ) =
--   Dec-rec
--     (λ _ → lit-polarity x ⊗p disj-polarity i ϕ)
--     (λ _ → disj-polarity i ϕ)
--     (Discrete-Fin i (lit-var x))

-- cnf-polarity : Fin Γ → CNF Γ → Polarity
-- cnf-polarity i = foldr (λ ϕ p → disj-polarity i ϕ ⊗p p) none

-- pure-literal : Fin Γ → CNF Γ → Type
-- pure-literal i ϕs = cnf-polarity i ϕs ≡ pos ⊎ cnf-polarity i ϕs ≡ neg

-- pure-literal? : (i : Fin Γ) → (ϕs : CNF Γ) → Dec (pure-literal i ϕs)
-- pure-literal? i ϕs =
--   Dec-⊎
--     (Discrete-Polarity (cnf-polarity i ϕs) pos)
--     (Discrete-Polarity (cnf-polarity i ϕs) neg)
```


```agda
¬empty-disj-sat : ∀ (ϕ : Disjunction 0) → (ρ : Fin 0 → Bool) → ⟦ ϕ ⟧ ρ ≡ true → ⊥
¬empty-disj-sat [] ρ sat = true≠false (sym sat)
¬empty-disj-sat (lit () ∷ ϕ) ρ sat
¬empty-disj-sat (neg () ∷ ϕ) ρ sat

unit-propagate-sat
  : (x : Literal (suc Γ))
  → (ϕs : CNF (suc Γ))
  → Σ[ ρ ∈ (Fin Γ → Bool) ] (⟦ unit-propagate x ϕs ⟧ ρ ≡ true)
  → Σ[ ρ ∈ (Fin (suc Γ) → Bool) ] (⟦ ϕs ⟧ ρ ≡ true)
unit-propagate-sat x ϕs (ρ , ρ-sat) =
  (ρ [ lit-var x ≔ lit-val x ]) , unit-propagate-sound x ϕs ρ ∙ ρ-sat

unit-propagate-unsat
  : (x : Literal (suc Γ))
  → (ϕs : CNF (suc Γ))
  → ¬ Σ[ ρ ∈ (Fin Γ → Bool) ] (⟦ unit-propagate x ϕs ⟧ ρ ≡ true)
  → ¬ Σ[ ρ ∈ (Fin (suc Γ) → Bool) ] ((⟦ ϕs ⟧ ρ ≡ true) × (⟦ x ⟧ ρ ≡ true))
unit-propagate-unsat x ϕs ¬sat (ρ , ρ-sat , x-sat) =
  ¬sat $
  delete ρ (lit-var x) ,
  sym (unit-propagate-complete x ϕs ρ x-sat)
  ∙ ρ-sat

cnf-sat? : (ϕs : CNF Γ) → Dec (Σ[ ρ ∈ (Fin Γ → Bool) ] (⟦ ϕs ⟧ ρ ≡ true))
cnf-sat? {Γ = zero} [] =
  yes (((λ ()) , refl))
cnf-sat? {Γ = zero} (ϕ ∷ ϕs) =
  no (λ (ρ , sat) → ¬empty-disj-sat ϕ ρ (and-reflect-true-l sat))
cnf-sat? {Γ = suc Γ} ϕs =
  Dec-rec
    (λ (x , x∈ϕs) →
      Dec-rec
        (yes ∘ unit-propagate-sat x ϕs)
        (λ ¬sat → no (λ (ρ , ρ-sat) → unit-propagate-unsat x ϕs ¬sat (ρ , ρ-sat , unit-clause-sat x ϕs x∈ϕs ρ ρ-sat)))
        (cnf-sat? (unit-propagate x ϕs)))
    (λ ¬ϕs-unit → -- TODO: pure literal elimination
      Dec-rec
        (yes ∘ unit-propagate-sat (lit fzero) ϕs)
        (λ ¬sat-true →
          Dec-rec
            (yes ∘ unit-propagate-sat (neg fzero) ϕs)
            (λ ¬sat-false → no λ (ρ , ρ-sat) →
              Bool-elim (λ b → ρ fzero ≡ b → ⊥)
                (λ ρ₀-true → unit-propagate-unsat (lit fzero) ϕs ¬sat-true (ρ , ρ-sat , ρ₀-true))
                (λ ρ₀-false → unit-propagate-unsat (neg fzero) ϕs ¬sat-false (ρ , ρ-sat , ap not ρ₀-false))
                (ρ fzero) refl)
            (cnf-sat? (unit-propagate (neg fzero) ϕs)))
        (cnf-sat? (unit-propagate (lit fzero) ϕs))) 
    (has-unit-clause? ϕs)
```

```agda
test-cnf : CNF 4
test-cnf =
  (neg 0 ∷ lit 1 ∷ lit 2 ∷ []) ∷
  (lit 0 ∷ lit 2 ∷ lit 3 ∷ []) ∷
  (lit 0 ∷ lit 2 ∷ neg 3 ∷ []) ∷
  (lit 0 ∷ neg 2 ∷ lit 3 ∷ []) ∷
  (lit 0 ∷ neg 2 ∷ neg 3 ∷ []) ∷
  (lit 1 ∷ neg 2 ∷ lit 3 ∷ []) ∷
  (neg 0 ∷ lit 1 ∷ neg 2 ∷ []) ∷
  (neg 0 ∷ neg 1 ∷ lit 2 ∷ []) ∷
  []

test-sat : Dec (Σ[ ρ ∈ (Fin 4 → Bool) ] (⟦ test-cnf ⟧ ρ ≡ true))
test-sat = cnf-sat? test-cnf
```
