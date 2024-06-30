<!--
```agda
open import 1Lab.Prelude

open import Data.Bool
open import Data.List hiding (_++_)
open import Data.Dec
open import Data.Fin using (Fin; fzero; fsuc; avoid)
open import Data.Nat
open import Data.Sum

open import Logic.Propositional.Classical

open import Meta.Invariant
open import Meta.Brackets

import Data.List as List
```
-->

```agda
module Logic.Propositional.Classical.CNF where
```

## Conjunctive normal forms {defines="conjunctive-normal-form CNF"}

As a general theme, it is often very useful to have some notion of
normal-form for logical and algebraic expressions, and
[[Classical propositional logic]] is no different! There are multiple
possible choices of normal form, but we will be focusing on
**conjunctive normal form**, or CNF for short.

A statement in propositional logic is in conjunctive normal form if
it is written as a conjunction of disjunctions of (potentially negated)
atoms. As an example, something like $(P \vee \neg Q) \wedge (\neg R \vee P)$
is in conjunctive normal form, yet something like $(P \wedge Q) \vee \neg R$
is not.

We call the potentially negated atoms in a CNF expression **literals**,
and the disjunctions **clauses**.

```agda
data Literal (Γ : Nat) : Type where
  lit : Fin Γ → Literal Γ
  neg : Fin Γ → Literal Γ

Clause : (Γ : Nat) → Type
Clause Γ = List (Literal Γ)

CNF : (Γ : Nat) → Type
CNF Γ = List (Clause Γ)
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

instance
  Discrete-Literal : Discrete (Literal Γ)
  Discrete-Literal {x = lit x} {lit y} = invmap (ap lit) lit-inj (x ≡? y)
  Discrete-Literal {x = lit x} {neg y} = no lit≠neg
  Discrete-Literal {x = neg x} {lit y} = no (lit≠neg ∘ sym)
  Discrete-Literal {x = neg x} {neg y} = invmap (ap neg) neg-inj (x ≡? y)

avoid-lit : (i : Fin (suc Γ)) (x : Literal (suc Γ)) → ¬ i ≡ lit-var x → Literal Γ
avoid-lit i (lit x) p = lit (avoid i x p)
avoid-lit i (neg x) p = neg (avoid i x p)

```
-->

## Semantics

Like their non-normal form brethren, expressions in CNF have a natural
semantics in booleans. However, evaluation is particularly easy!

```agda
lit-sem : Literal Γ → (Fin Γ → Bool) → Bool
lit-sem (lit x) ρ = ρ x
lit-sem (neg x) ρ = not (ρ x)

clause-sem : Clause Γ → (Fin Γ → Bool) → Bool
clause-sem Ps ρ = any-of (λ a → lit-sem a ρ) Ps

cnf-sem : CNF Γ → (Fin Γ → Bool) → Bool
cnf-sem Ps ρ = all-of (λ d → clause-sem d ρ) Ps

instance
  ⟦⟧-Literal : ⟦⟧-notation (Literal Γ)
  ⟦⟧-Literal {Γ = Γ} = brackets ((Fin Γ → Bool) → Bool) lit-sem

  ⟦⟧-Clause : ⟦⟧-notation (Clause Γ)
  ⟦⟧-Clause {Γ = Γ} = brackets ((Fin Γ → Bool) → Bool) clause-sem

  ⟦⟧-CNF : ⟦⟧-notation (CNF Γ)
  ⟦⟧-CNF {Γ = Γ} = brackets ((Fin Γ → Bool) → Bool) cnf-sem
```

## Soundness

We can extend the normal operations on propositions to expressions
in CNF.

Atoms $P$ are represented by a single clause.

```agda
cnf-atom : Fin Γ → CNF Γ
cnf-atom x = (lit x ∷ []) ∷ []
```

True and false are represented by an expression with no clauses,
and an expression with a single empty clause, respectively.

```agda
⊤cnf : CNF Γ
⊤cnf = []

⊥cnf : CNF Γ
⊥cnf = [] ∷ []
```

Conjunction can be defined by appending lists.

```agda
_∧cnf_ : CNF Γ → CNF Γ → CNF Γ
xs ∧cnf ys = xs List.++ ys
```

Disjunction is somewhat tricky, but can be handled by distributing
each clause.

```agda
cnf-distrib : Clause Γ → CNF Γ → CNF Γ
cnf-distrib P Q = map (P List.++_) Q

_∨cnf_ : CNF Γ → CNF Γ → CNF Γ
[]       ∨cnf Q = []
(P ∷ Ps) ∨cnf Q = cnf-distrib P Q ∧cnf (Ps ∨cnf Q)
```

Negation is performed by negating all the clauses, and then taking the
disjunction of the negated clauses.

```agda
¬lit : Literal Γ → Literal Γ
¬lit (lit x) = neg x
¬lit (neg x) = lit x

¬clause : Clause Γ → CNF Γ
¬clause P = map (λ a → ¬lit a ∷ []) P

¬cnf : CNF Γ → CNF Γ
¬cnf []      = ⊥cnf
¬cnf (P ∷ Q) = ¬clause P ∨cnf ¬cnf Q
```

<details>
<summary>
All of these operations commute with interpretation in the expected way,
but showing this requires a few nightmare inductive arguments over
syntax.
</summary>

```agda
cnf-atom-sound : ∀ (x : Fin Γ) (ρ : Fin Γ → Bool) → ⟦ cnf-atom x ⟧ ρ ≡ ρ x
cnf-atom-sound x ρ = and-truer _ ∙ or-falser _

⊥cnf-sound : ∀ (ρ : Fin Γ → Bool) → ⟦ ⊥cnf ⟧ ρ ≡ false
⊥cnf-sound ρ = refl

⊤cnf-sound : ∀ (ρ : Fin Γ → Bool) → ⟦ ⊤cnf ⟧ ρ ≡ true
⊤cnf-sound ρ = refl

∧cnf-sound : ∀ (P Q : CNF Γ) → (ρ : Fin Γ → Bool) → ⟦ P ∧cnf Q ⟧ ρ ≡ and (⟦ P ⟧ ρ) (⟦ Q ⟧ ρ)
∧cnf-sound P Q ρ = all-of-++ (any-of (λ a → lit-sem a ρ)) P Q

cnf-distrib-sound
  : (P : Clause Γ) (Q : CNF Γ)
  → (ρ : Fin Γ → Bool)
  → ⟦ cnf-distrib P Q ⟧ ρ ≡ or (⟦ P ⟧ ρ) (⟦ Q ⟧ ρ)
cnf-distrib-sound []       Q ρ = ap (all-of (λ d → clause-sem d ρ)) (map-id Q)
cnf-distrib-sound (P ∷ Ps) Q ρ =
  all-of (λ d → ⟦ d ⟧ ρ) (map (λ ys → P ∷ (Ps List.++ ys)) Q) ≡⟨ all-of-map _ _ Q ⟩
  all-of (λ d → ⟦ P ∷ (Ps List.++ d) ⟧ ρ) Q                   ≡⟨ ap (λ ϕ → all-of ϕ Q) (funext λ d → any-of-++ _ (P ∷ Ps) d) ⟩
  all-of (λ d → or (⟦ P ∷ Ps ⟧ ρ) (⟦ d ⟧ ρ)) Q                ≡⟨ all-of-or (λ d → ⟦ d ⟧ ρ) (⟦ P ∷ Ps ⟧ ρ) Q ⟩
  or (⟦ P ∷ Ps ⟧ ρ) (⟦ Q ⟧ ρ)                                 ∎

∨cnf-sound : ∀ (P Q : CNF Γ) → (ρ : Fin Γ → Bool) → ⟦ P ∨cnf Q ⟧ ρ ≡ or (⟦ P ⟧ ρ) (⟦ Q ⟧ ρ)
∨cnf-sound []       Q ρ = refl
∨cnf-sound (P ∷ Ps) Q ρ =
  ⟦ (P ∷ Ps) ∨cnf Q ⟧ ρ                                    ≡⟨ all-of-++ (λ d → clause-sem d ρ) (cnf-distrib P Q) (Ps ∨cnf Q) ⟩
  and (⟦ cnf-distrib P Q ⟧ ρ) (⟦ Ps ∨cnf Q ⟧ ρ)            ≡⟨ ap₂ and (cnf-distrib-sound P Q ρ) (∨cnf-sound Ps Q ρ) ⟩
  and (or (⟦ P ⟧ ρ) (⟦ Q ⟧ ρ)) (or (⟦ Ps ⟧ ρ) (⟦ Q ⟧ ρ))   ≡˘⟨ or-distrib-andr (⟦ P ⟧ ρ) (⟦ Ps ⟧ ρ) (⟦ Q ⟧ ρ) ⟩
  or (⟦ P ∷ Ps ⟧ ρ) (⟦ Q ⟧ ρ) ∎

¬lit-sound : (a : Literal Γ) → (ρ : Fin Γ → Bool) → ⟦ ¬lit a ⟧ ρ ≡ not (⟦ a ⟧ ρ)
¬lit-sound (lit x) ρ = refl
¬lit-sound (neg x) ρ = sym (not-involutive (ρ x))

¬clause-sound : ∀ (P : Clause Γ) → (ρ : Fin Γ → Bool) → ⟦ ¬clause P ⟧ ρ ≡ not (⟦ P ⟧ ρ)
¬clause-sound P ρ =
  all-of (λ d → ⟦ d ⟧ ρ) (map (λ a → ¬lit a ∷ []) P)  ≡⟨ all-of-map (λ d → ⟦ d ⟧ ρ) (λ a → ¬lit a ∷ []) P ⟩
  all-of (λ a → or (⟦ ¬lit a ⟧ ρ) false) P            ≡⟨ ap (λ ϕ → all-of ϕ P) (funext λ a → or-falser (⟦ ¬lit a ⟧ ρ)) ⟩
  all-of (λ a → ⟦ ¬lit a ⟧ ρ) P                       ≡⟨ ap (λ ϕ → all-of ϕ P) (funext λ a → ¬lit-sound a ρ) ⟩
  all-of (λ a → not (⟦ a ⟧ ρ)) P                      ≡˘⟨ not-any-of (λ a → ⟦ a ⟧ ρ) P ⟩
  not (⟦ P ⟧ ρ)                                       ∎

¬cnf-sound : ∀ (P : CNF Γ) → (ρ : Fin Γ → Bool) → ⟦ ¬cnf P ⟧ ρ ≡ not (⟦ P ⟧ ρ)
¬cnf-sound []       ρ = refl
¬cnf-sound (P ∷ Ps) ρ =
  ⟦ (¬clause P ∨cnf ¬cnf Ps) ⟧ ρ        ≡⟨ ∨cnf-sound (¬clause P) (¬cnf Ps) ρ ⟩
  or (⟦ ¬clause P ⟧ ρ) (⟦ ¬cnf Ps ⟧ ρ)  ≡⟨ ap₂ or (¬clause-sound P ρ) (¬cnf-sound Ps ρ) ⟩
  or (not (⟦ P ⟧ ρ)) (not (⟦ Ps ⟧ ρ))   ≡˘⟨ not-and≡or-not (⟦ P  ⟧ ρ) (⟦ Ps ⟧ ρ) ⟩
  not (⟦ P ∷ Ps ⟧ ρ)                    ∎
```
</details>

## A naive algorithm

Armed with these operations on CNFs, we can give a translation from
propositions into CNF. However, note that this is extremely naive, and
will result in huge clause sizes! This is due to the fact that
disjunction and negation distribute clauses, which will result in
potentially exponential blow-ups in expression sizes.

```agda
cnf : Proposition Γ → CNF Γ
cnf (atom x)  = cnf-atom x
cnf “⊤”       = ⊤cnf
cnf “⊥”       = ⊥cnf
cnf (P “∧” Q) = cnf P ∧cnf cnf Q
cnf (P “∨” Q) = cnf P ∨cnf cnf Q
cnf (“¬” P)   = ¬cnf (cnf P)

cnf-sound
  : ∀ (P : Proposition Γ) (ρ : Fin Γ → Bool)
  → ⟦ cnf P ⟧ ρ ≡ ⟦ P ⟧ ρ
cnf-sound (atom x) ρ = and-truer (or (ρ x) false) ∙ or-falser (ρ x)

cnf-sound “⊤” ρ = refl
cnf-sound “⊥” ρ = refl

cnf-sound (P “∧” Q) ρ =
  ⟦ cnf P ∧cnf cnf Q ⟧ ρ           ≡⟨ ∧cnf-sound (cnf P) (cnf Q) ρ ⟩
  and (⟦ cnf P ⟧ ρ) (⟦ cnf Q ⟧ ρ)  ≡⟨ ap₂ and (cnf-sound P ρ) (cnf-sound Q ρ) ⟩
  and (⟦ P ⟧ ρ) (⟦ Q ⟧ ρ)          ∎
cnf-sound (P “∨” Q) ρ =
  ⟦ cnf P ∨cnf cnf Q ⟧ ρ          ≡⟨ ∨cnf-sound (cnf P) (cnf Q) ρ ⟩
  or (⟦ cnf P ⟧ ρ) (⟦ cnf Q ⟧ ρ)  ≡⟨ ap₂ or (cnf-sound P ρ) (cnf-sound Q ρ) ⟩
  or (⟦ P ⟧ ρ) (⟦ Q ⟧ ρ)          ∎
cnf-sound (“¬” P) ρ =
  ⟦ ¬cnf (cnf P) ⟧ ρ  ≡⟨ ¬cnf-sound (cnf P) ρ ⟩
  not (⟦ cnf P ⟧ ρ)   ≡⟨ ap not (cnf-sound P ρ) ⟩
  not (⟦ P ⟧ ρ)       ∎
```

## Quotation

We can also read expressions in CNF back into propositions. Luckily,
there are no exponential blow-ups here!

```agda
quote-lit : Literal Γ → Proposition Γ
quote-lit (lit x) = atom x
quote-lit (neg x) = “¬” (atom x)

quote-clause : Clause Γ → Proposition Γ
quote-clause []      = “⊥”
quote-clause (x ∷ ϕ) = quote-lit x “∨” quote-clause ϕ

quote-cnf : CNF Γ → Proposition Γ
quote-cnf []       = “⊤”
quote-cnf (ϕ ∷ ϕs) = quote-clause ϕ “∧” quote-cnf ϕs

quote-lit-sound : ∀ (x : Literal Γ) → (ρ : Fin Γ → Bool) → ⟦ x ⟧ ρ ≡ ⟦ quote-lit x ⟧ ρ
quote-lit-sound (lit x) ρ = refl
quote-lit-sound (neg x) ρ = refl

quote-clause-sound : ∀ (ϕ : Clause Γ) → (ρ : Fin Γ → Bool) → ⟦ ϕ ⟧ ρ ≡ ⟦ quote-clause ϕ ⟧ ρ
quote-clause-sound []      ρ = refl
quote-clause-sound (x ∷ ϕ) ρ = ap₂ or (quote-lit-sound x ρ) (quote-clause-sound ϕ ρ)

quote-cnf-sound : ∀ (ϕ : CNF Γ) → (ρ : Fin Γ → Bool) → ⟦ ϕ ⟧ ρ ≡ ⟦ quote-cnf ϕ ⟧ ρ
quote-cnf-sound []       ρ = refl
quote-cnf-sound (ϕ ∷ ϕs) ρ = ap₂ and (quote-clause-sound ϕ ρ) (quote-cnf-sound ϕs ρ)
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
