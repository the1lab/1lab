<!--
```agda
open import 1Lab.Prelude hiding (_∈_)

open import Data.Bool
open import Data.Dec
open import Data.Fin using (Fin; fzero; fsuc; Discrete-Fin; avoid)
open import Data.List hiding (_++_)
open import Data.Nat
open import Data.Sum

open import Logic.Propositional.Classical

open import Meta.Brackets

import Data.List as List
```
-->

```agda
module Logic.Propositional.Classical.CNF where
```

## Conjunctive Normal Forms

```agda
data Literal (Γ : Nat) : Type where
  lit : Fin Γ → Literal Γ
  neg : Fin Γ → Literal Γ

Disjunction : (Γ : Nat) → Type
Disjunction Γ = List (Literal Γ)

CNF : (Γ : Nat) → Type
CNF Γ = List (Disjunction Γ)
```

<!--
```agda
private variable
  Γ Δ Θ : Nat
  ψ θ ζ : Ctx Γ
  P Q R : Proposition Γ
```
-->

<!--
```agda
lit≠neg : ∀ {x y : Fin Γ} → lit x ≡ neg y → ⊥
lit≠neg {Γ = Γ} p = subst is-lit p tt where
  is-lit : Literal Γ → Type
  is-lit (lit x) = ⊤
  is-lit (neg x) = ⊥

lit-var : Literal Γ → Fin Γ
lit-var (lit x) = x
lit-var (neg x) = x

lit-val : Literal Γ → Bool
lit-val (lit x) = true
lit-val (neg x) = false

lit-inj : ∀ {x y : Fin Γ} → lit x ≡ lit y → x ≡ y
lit-inj p = ap lit-var p

neg-inj : ∀ {x y : Fin Γ} → neg x ≡ neg y → x ≡ y
neg-inj p = ap lit-var p

Discrete-Literal : Discrete (Literal Γ)
Discrete-Literal (lit x) (lit y) = Dec-map (ap lit) lit-inj (Discrete-Fin x y)
Discrete-Literal (lit x) (neg y) = no lit≠neg
Discrete-Literal (neg x) (lit y) = no (lit≠neg ∘ sym)
Discrete-Literal (neg x) (neg y) = Dec-map (ap neg) neg-inj (Discrete-Fin x y)

avoid-lit : (i : Fin (suc Γ)) → (x : Literal (suc Γ)) → ¬ i ≡ lit-var x → Literal Γ
avoid-lit i (lit x) p = lit (avoid i x p)
avoid-lit i (neg x) p = neg (avoid i x p)

```
-->


## Semantics

```agda
lit-sem : Literal Γ → (Fin Γ → Bool) → Bool
lit-sem (lit x) ρ = ρ x
lit-sem (neg x) ρ = not (ρ x)

disj-sem : Disjunction Γ → (Fin Γ → Bool) → Bool
disj-sem Ps ρ = any-of (λ a → lit-sem a ρ) Ps

cnf-sem : CNF Γ → (Fin Γ → Bool) → Bool
cnf-sem Ps ρ = all-of (λ d → disj-sem d ρ) Ps

instance
  ⟦⟧-Literal : ⟦⟧-notation (Literal Γ)
  ⟦⟧-Literal {Γ = Γ} = brackets ((Fin Γ → Bool) → Bool) lit-sem

  ⟦⟧-Disjunction : ⟦⟧-notation (Disjunction Γ)
  ⟦⟧-Disjunction {Γ = Γ} = brackets ((Fin Γ → Bool) → Bool) disj-sem

  ⟦⟧-CNF : ⟦⟧-notation (CNF Γ)
  ⟦⟧-CNF {Γ = Γ} = brackets ((Fin Γ → Bool) → Bool) cnf-sem

cnf-lit : Fin Γ → CNF Γ
cnf-lit x = (lit x ∷ []) ∷ []

⊤cnf : CNF Γ
⊤cnf = []

⊥cnf : CNF Γ
⊥cnf = [] ∷ []

⊥cnf-sound : ∀ (ρ : Fin Γ → Bool) → ⟦ ⊥cnf ⟧ ρ ≡ false
⊥cnf-sound ρ = refl

_∧cnf_ : CNF Γ → CNF Γ → CNF Γ
xs ∧cnf ys = xs List.++ ys

cnf-distrib : Disjunction Γ → CNF Γ → CNF Γ
cnf-distrib P Q = map (P List.++_) Q

_∨cnf_ : CNF Γ → CNF Γ → CNF Γ
[] ∨cnf Q = []
(P ∷ Ps) ∨cnf Q = cnf-distrib P Q ∧cnf (Ps ∨cnf Q)

¬lit : Literal Γ → Literal Γ
¬lit (lit x) = neg x
¬lit (neg x) = lit x

¬disj : Disjunction Γ → CNF Γ
¬disj P = map (λ a → ¬lit a ∷ []) P

¬cnf : CNF Γ → CNF Γ
¬cnf [] = ⊥cnf
¬cnf (P ∷ Q) = ¬disj P ∨cnf ¬cnf Q
```

## Soundness

```agda
cnf-lit-sound : ∀ (x : Fin Γ) (ρ : Fin Γ → Bool) → ⟦ cnf-lit x ⟧ ρ ≡ ρ x
cnf-lit-sound x ρ = and-truer _ ∙ or-falser _

⊤cnf-sound : ∀ (ρ : Fin Γ → Bool) → ⟦ ⊤cnf ⟧ ρ ≡ true
⊤cnf-sound ρ = refl

∧cnf-sound : ∀ (P Q : CNF Γ) → (ρ : Fin Γ → Bool) → ⟦ P ∧cnf Q ⟧ ρ ≡ and (⟦ P ⟧ ρ) (⟦ Q ⟧ ρ)
∧cnf-sound P Q ρ = all-of-++ (any-of (λ a → lit-sem a ρ)) P Q

cnf-distrib-sound
  : (P : Disjunction Γ) (Q : CNF Γ)
  → (ρ : Fin Γ → Bool)
  → ⟦ cnf-distrib P Q ⟧ ρ ≡ or (⟦ P ⟧ ρ) (⟦ Q ⟧ ρ)
cnf-distrib-sound [] Q ρ = ap (all-of (λ d → disj-sem d ρ)) (map-id Q)
cnf-distrib-sound (P ∷ Ps) Q ρ =
  all-of (λ d → ⟦ d ⟧ ρ) (map (λ ys → P ∷ (Ps List.++ ys)) Q) ≡⟨ all-of-map _ _ Q ⟩
  all-of (λ d → ⟦ P ∷ (Ps List.++ d) ⟧ ρ) Q                   ≡⟨ ap (λ ϕ → all-of ϕ Q) (funext λ d → any-of-++ _ (P ∷ Ps) d) ⟩
  all-of (λ d → or (⟦ P ∷ Ps ⟧ ρ) (⟦ d ⟧ ρ)) Q                ≡⟨ all-of-or (λ d → ⟦ d ⟧ ρ) (⟦ P ∷ Ps ⟧ ρ) Q ⟩
  or (⟦ P ∷ Ps ⟧ ρ) (⟦ Q ⟧ ρ)                                 ∎

∨cnf-sound : ∀ (P Q : CNF Γ) → (ρ : Fin Γ → Bool) → ⟦ P ∨cnf Q ⟧ ρ ≡ or (⟦ P ⟧ ρ) (⟦ Q ⟧ ρ)
∨cnf-sound [] Q ρ = refl
∨cnf-sound (P ∷ Ps) Q ρ =
  ⟦ (P ∷ Ps) ∨cnf Q ⟧ ρ                                  ≡⟨ all-of-++ (λ d → disj-sem d ρ) (cnf-distrib P Q) (Ps ∨cnf Q) ⟩
  and (⟦ cnf-distrib P Q ⟧ ρ) (⟦ Ps ∨cnf Q ⟧ ρ)          ≡⟨ ap₂ and (cnf-distrib-sound P Q ρ) (∨cnf-sound Ps Q ρ) ⟩
  and (or (⟦ P ⟧ ρ) (⟦ Q ⟧ ρ)) (or (⟦ Ps ⟧ ρ) (⟦ Q ⟧ ρ)) ≡˘⟨ or-distrib-andr (⟦ P ⟧ ρ) (⟦ Ps ⟧ ρ) (⟦ Q ⟧ ρ) ⟩
  or (⟦ P ∷ Ps ⟧ ρ) (⟦ Q ⟧ ρ) ∎

¬lit-sound : (a : Literal Γ) → (ρ : Fin Γ → Bool) → ⟦ ¬lit a ⟧ ρ ≡ not (⟦ a ⟧ ρ)
¬lit-sound (lit x) ρ = refl
¬lit-sound (neg x) ρ = sym (not-involutive (ρ x))

¬disj-sound : ∀ (P : Disjunction Γ) → (ρ : Fin Γ → Bool) → ⟦ ¬disj P ⟧ ρ ≡ not (⟦ P ⟧ ρ)
¬disj-sound P ρ =
  all-of (λ d → ⟦ d ⟧ ρ) (map (λ a → ¬lit a ∷ []) P) ≡⟨ all-of-map (λ d → ⟦ d ⟧ ρ) (λ a → ¬lit a ∷ []) P ⟩
  all-of (λ a → or (⟦ ¬lit a ⟧ ρ) false) P       ≡⟨ ap (λ ϕ → all-of ϕ P) (funext λ a → or-falser (⟦ ¬lit a ⟧ ρ)) ⟩
  all-of (λ a → ⟦ ¬lit a ⟧ ρ) P                  ≡⟨ ap (λ ϕ → all-of ϕ P) (funext λ a → ¬lit-sound a ρ) ⟩
  all-of (λ a → not (⟦ a ⟧ ρ)) P                  ≡˘⟨ not-any-of (λ a → ⟦ a ⟧ ρ) P ⟩
  not (⟦ P ⟧ ρ)                                   ∎

¬cnf-sound : ∀ (P : CNF Γ) → (ρ : Fin Γ → Bool) → ⟦ ¬cnf P ⟧ ρ ≡ not (⟦ P ⟧ ρ)
¬cnf-sound [] ρ = refl
¬cnf-sound (P ∷ Ps) ρ =
  ⟦ (¬disj P ∨cnf ¬cnf Ps) ⟧ ρ        ≡⟨ ∨cnf-sound (¬disj P) (¬cnf Ps) ρ ⟩
  or (⟦ ¬disj P ⟧ ρ) (⟦ ¬cnf Ps ⟧ ρ)  ≡⟨ ap₂ or (¬disj-sound P ρ) (¬cnf-sound Ps ρ) ⟩
  or (not (⟦ P ⟧ ρ)) (not (⟦ Ps ⟧ ρ)) ≡˘⟨ not-and≡or-not (⟦ P  ⟧ ρ) (⟦ Ps ⟧ ρ) ⟩
  not (⟦ P ∷ Ps ⟧ ρ)                  ∎
```

## A Naive Algorithm

```agda
cnf : Proposition Γ → CNF Γ
cnf (var x) = cnf-lit x
cnf “⊤” = ⊤cnf
cnf “⊥” = ⊥cnf
cnf (P “∧” Q) = cnf P ∧cnf cnf Q
cnf (P “∨” Q) = cnf P ∨cnf cnf Q
cnf (“¬” P) = ¬cnf (cnf P)

cnf-sound
  : ∀ (P : Proposition Γ)
  → (ρ : Fin Γ → Bool)
  → ⟦ cnf P ⟧ ρ ≡ ⟦ P ⟧ ρ
cnf-sound (var x) ρ =
  and-truer (or (ρ x) false)
  ∙ or-falser (ρ x)
cnf-sound “⊤” ρ = refl
cnf-sound “⊥” ρ = refl
cnf-sound (P “∧” Q) ρ =
  ∧cnf-sound (cnf P) (cnf Q) ρ
  ∙ ap₂ and (cnf-sound P ρ) (cnf-sound Q ρ)
cnf-sound (P “∨” Q) ρ =
  ∨cnf-sound (cnf P) (cnf Q) ρ
  ∙ ap₂ or (cnf-sound P ρ) (cnf-sound Q ρ)
cnf-sound (“¬” P) ρ =
  ¬cnf-sound (cnf P) ρ
  ∙ ap not (cnf-sound P ρ)
```

## Quotation

```agda
quote-lit : Literal Γ → Proposition Γ
quote-lit (lit x) = var x
quote-lit (neg x) = “¬” (var x)

quote-disj : Disjunction Γ → Proposition Γ
quote-disj [] = “⊥”
quote-disj (x ∷ ϕ) = quote-lit x “∨” quote-disj ϕ

quote-cnf : CNF Γ → Proposition Γ
quote-cnf [] = “⊤”
quote-cnf (ϕ ∷ ϕs) = quote-disj ϕ “∧” quote-cnf ϕs

quote-lit-sound : ∀ (x : Literal Γ) → (ρ : Fin Γ → Bool) → ⟦ x ⟧ ρ ≡ ⟦ quote-lit x ⟧ ρ
quote-lit-sound (lit x) ρ = refl
quote-lit-sound (neg x) ρ = refl

quote-disj-sound : ∀ (ϕ : Disjunction Γ) → (ρ : Fin Γ → Bool) → ⟦ ϕ ⟧ ρ ≡ ⟦ quote-disj ϕ ⟧ ρ
quote-disj-sound [] ρ = refl
quote-disj-sound (x ∷ ϕ) ρ = ap₂ or (quote-lit-sound x ρ) (quote-disj-sound ϕ ρ)

quote-cnf-sound : ∀ (ϕ : CNF Γ) → (ρ : Fin Γ → Bool) → ⟦ ϕ ⟧ ρ ≡ ⟦ quote-cnf ϕ ⟧ ρ
quote-cnf-sound [] ρ = refl
quote-cnf-sound (ϕ ∷ ϕs) ρ = ap₂ and (quote-disj-sound ϕ ρ) (quote-cnf-sound ϕs ρ)
```

<!--
```agda
literal-eq-negate : ∀ (x y : Literal Γ) → ¬ x ≡ y → lit-var x ≡ lit-var y → x ≡ ¬lit y
literal-eq-negate (lit x) (lit y) x≠y p = absurd (x≠y (ap lit p))
literal-eq-negate (lit x) (neg y) x≠y p = ap lit p
literal-eq-negate (neg x) (lit y) x≠y p = ap neg p
literal-eq-negate (neg x) (neg y) x≠y p = absurd (x≠y (ap neg p))

literal-sat-val : ∀ (x : Literal Γ) → (ρ : Fin Γ → Bool) → ⟦ x ⟧ ρ ≡ true → ρ (lit-var x) ≡ lit-val x
literal-sat-val (lit x) ρ x-true = x-true
literal-sat-val (neg x) ρ x-true = not-inj x-true
```
-->
