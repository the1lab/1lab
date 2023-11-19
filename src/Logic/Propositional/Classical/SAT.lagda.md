<!--
```agda
open import 1Lab.Prelude

open import Data.Bool
open import Data.List hiding (_++_)
open import Data.Dec
open import Data.Fin using (Fin; fzero; fsuc; Discrete-Fin; avoid; _[_≔_]; delete)
open import Data.Nat
open import Data.Sum

open import Logic.Propositional.Classical.CNF
open import Logic.Propositional.Classical

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

# SAT Solving

SAT solving is the process of determining if we can find some assignment
of variables $\rho$ that makes a given formula $\phi$ in classical propositional
logic true. Such an assignment is called a **satisfying** assignment,
hence the name SAT. This is a classic problem in Computer Science, and
many other important and interesting problems can be reduced to finding
satisfying assignments to huge formulae.

Unfortunately, SAT solving is provably hard from a complexity standpoint.
However, this will not stop us from writing a solver anyways! For the sake
of efficiency, our solver will operate on expressions in [[CNF]].

# Unit Propagation

The algorithm we will use is a simplified version of the classic DPLL
algorithm, which combines backtracking search with a mechanism for
pruning the search space, known as **unit propagation**. The idea
behind this is as follows: if we see an clause that contains a single
literal $P$ in our expression, then we know that $P$ must be true.
Furthermore, any clause containing $P$ can be deleted, as we know it must
be true! Even better, we can remove any occurance of $\neg P$ from
our expression, as we know that $\neg P$ must be false. This reduces
the size of the search space considerably, and makes the problem a bit
more tractable.

Luckily, unit propagation is rather easy to implement.

```agda
delete-literal
  : (x : Fin (suc Γ))
  → (ϕ : Clause (suc Γ))
  → Clause Γ
delete-literal {Γ = zero} i ϕ = []
delete-literal {Γ = suc Γ} i [] = []
delete-literal {Γ = suc Γ} i (x ∷ ϕ) with Discrete-Fin i (lit-var x)
... | yes _ = delete-literal i ϕ
... | no i≠x = avoid-lit i x i≠x ∷ delete-literal i ϕ

unit-propagate : Literal (suc Γ) → CNF (suc Γ) → CNF Γ
unit-propagate x [] = []
unit-propagate x (ϕ ∷ ϕs) with elem? Discrete-Literal x ϕ
... | yes _ = unit-propagate x ϕs
... | no _ = delete-literal (lit-var x) ϕ ∷ unit-propagate x ϕs
```

However, it is slightly *less* trivial to prove correct. First,
we will show a couple of quick lemmas regarding assignment of variables.

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
```

Next, we show that deleting literals preserves the truth value of
a given assignment when the literal doesn't show up in the clause.
This is not hard to show, just tedious.

```agda
delete-literal-sound
  : (x : Literal (suc Γ))
  → (ϕ : Clause (suc Γ))
  → ¬ (x ∈ₗ ϕ)
  → ∀ (ρ : Fin Γ → Bool)
  → ⟦ ϕ ⟧ (ρ [ lit-var x ≔ lit-val x ]) ≡ ⟦ delete-literal (lit-var x) ϕ ⟧ ρ
delete-literal-sound {zero} x [] x∉ϕ ρ = refl
delete-literal-sound {zero} (lit fzero) (lit fzero ∷ ϕ) x∉ϕ ρ =
  absurd (x∉ϕ (here refl))
delete-literal-sound {zero} (lit fzero) (neg fzero ∷ ϕ) x∉ϕ ρ =
  delete-literal-sound (lit fzero) ϕ (x∉ϕ ∘ there) ρ
delete-literal-sound {zero} (neg fzero) (lit fzero ∷ ϕ) x∉ϕ ρ =
  delete-literal-sound (neg fzero) ϕ (x∉ϕ ∘ there) ρ
delete-literal-sound {zero} (neg fzero) (neg fzero ∷ ϕ) x∉ϕ ρ =
  absurd (x∉ϕ (here refl))
delete-literal-sound {suc Γ} x [] x∉ϕ ρ = refl
delete-literal-sound {suc Γ} x (y ∷ ϕ) x∉ϕ ρ with Discrete-Fin (lit-var x) (lit-var y)
... | yes x=y =
  ap₂ or
    (subst (λ e → ⟦ y ⟧ (ρ [ lit-var e ≔ lit-val e ]) ≡ false)
      (sym (literal-eq-negate x y (x∉ϕ ∘ here) x=y))
      (lit-assign-neg-false y ρ))
    refl
  ∙ delete-literal-sound x ϕ (x∉ϕ ∘ there) ρ
... | no x≠y =
  ap₂ or
    (avoid-lit-insert x y x≠y ρ)
    (delete-literal-sound x ϕ (x∉ϕ ∘ there) ρ)
```

Soundness and completeness of unit propagation follows quickly.

```agda
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
    (delete-literal-sound x ϕ ¬x∉ϕ ρ)
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

We also have a decision procedure that determines if there are any
unit clauses in an expression.

```agda
has-unit-clause? : ∀ (ϕs : CNF Γ) → Dec (Σ[ x ∈ Literal Γ ] ((x ∷ []) ∈ₗ ϕs))
has-unit-clause? [] = no (¬some-[] ∘ snd)
has-unit-clause? ([] ∷ ϕs) =
  Dec-rec
    (λ (x , x∈ϕs) → yes (x , there x∈ϕs))
    (λ ¬ϕ-unit → no (λ (x , x∈ϕs) →
      [ ∷≠[]
      , (λ x∈ϕs → ¬ϕ-unit (x , x∈ϕs))
      ] (∷-some-⊎ x∈ϕs)))
    (has-unit-clause? ϕs)
has-unit-clause? ((x ∷ []) ∷ ϕs) = yes (x , here refl)
has-unit-clause? ((x ∷ y ∷ ϕ) ∷ ϕs) =
  Dec-rec
    (λ (x , x∈ϕs) → yes (x , there x∈ϕs))
    (λ ¬ϕ-unit → no (λ (x , x∈ϕs) →
      [ ∷≠[] ∘ ∷-tail-inj ∘ sym
      , (λ x∈ϕs → ¬ϕ-unit (x , x∈ϕs))
      ] (∷-some-⊎ x∈ϕs)))
    (has-unit-clause? ϕs)
```

If $x$ is a unit clause in $\phi$, and an assignment $\rho$ satisfies
$\phi$, then $\rho(x)$ must be true.

```agda
unit-clause-sat
  : (x : Literal Γ)
  → (ϕs : CNF Γ)
  → (x ∷ []) ∈ₗ ϕs
  → (ρ : Fin Γ → Bool)
  → ⟦ ϕs ⟧ ρ ≡ true
  → ⟦ x ⟧ ρ ≡ true
unit-clause-sat x (ϕ ∷ ϕs) (here [x]=ϕ) ρ ϕs-sat =
  sym (or-falser _)
  ∙ ap (λ e → (⟦ e ⟧ ρ)) [x]=ϕ
  ∙ and-reflect-true-l ϕs-sat
unit-clause-sat x (y ∷ ϕs) (there [x]∈ϕs) ρ ϕs-sat =
  unit-clause-sat x ϕs [x]∈ϕs ρ (and-reflect-true-r ϕs-sat)
```

We also note that it is impossible to find a satisfying assignment to a
clause with no atoms.

```agda
¬empty-clause-sat : ∀ (ϕ : Clause 0) → (ρ : Fin 0 → Bool) → ⟦ ϕ ⟧ ρ ≡ true → ⊥
¬empty-clause-sat [] ρ sat = true≠false (sym sat)
¬empty-clause-sat (lit () ∷ ϕ) ρ sat
¬empty-clause-sat (neg () ∷ ϕ) ρ sat
```

Next, we observe that if the result of unit propagation is satisfiable,
then the original expression must be satisfiable. Likewise, if
the result of unit propagation is unsatisfiable, then the original
expression is unsatisfiable.

```agda
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
```

Armed with these lemmas, we can finally write our SAT solver.
We shall perform induction on the number of atoms in our CNF
expression $\phi$. If $\phi$ contains no atoms, then we simply
need to check if it has any clauses.

```agda
cnf-sat? : (ϕs : CNF Γ) → Dec (Σ[ ρ ∈ (Fin Γ → Bool) ] (⟦ ϕs ⟧ ρ ≡ true))
cnf-sat? {Γ = zero} [] =
  yes (((λ ()) , refl))
cnf-sat? {Γ = zero} (ϕ ∷ ϕs) =
  no (λ (ρ , sat) → ¬empty-clause-sat ϕ ρ (and-reflect-true-l sat))
```

If $\phi$ contains at least one atom, we first check to see if there
are any unit clauses. If there are, we perform unit propagation, and
recurse. If there aren't, then we perform backtracking search, first
trying to see if the first atom is true, and then checking to see if
it is false.

```agda
cnf-sat? {Γ = suc Γ} ϕs with has-unit-clause? ϕs
... | yes (x , [x]∈ϕs) with cnf-sat? (unit-propagate x ϕs)
...   | yes sat = yes (unit-propagate-sat x ϕs sat)
...   | no ¬sat = no λ (ρ , ρ-sat) →
        unit-propagate-unsat x ϕs ¬sat
          (ρ , ρ-sat , unit-clause-sat x ϕs [x]∈ϕs ρ ρ-sat)
cnf-sat? {Γ = suc Γ} ϕs | no ¬ϕs-unit with (cnf-sat? (unit-propagate (lit fzero) ϕs))
... | yes sat-true = yes (unit-propagate-sat (lit fzero) ϕs sat-true)
... | no ¬sat-true with cnf-sat? (unit-propagate (neg fzero) ϕs)
...   | yes sat-false = yes (unit-propagate-sat (neg fzero) ϕs sat-false)
...   | no ¬sat-false = no λ (ρ , ρ-sat) →
        Bool-elim (λ b → ρ fzero ≡ b → ⊥)
          (λ ρ₀-true → unit-propagate-unsat (lit fzero) ϕs ¬sat-true (ρ , ρ-sat , ρ₀-true))
          (λ ρ₀-false → unit-propagate-unsat (neg fzero) ϕs ¬sat-false (ρ , ρ-sat , ap not ρ₀-false))
          (ρ fzero) refl
```

And that's it! Note that "classic" DPLL also includes a second rule
known as "pure literal elimination". The idea here is that if a literal
only shows up as negated or not negated, then we can delete all occurances
of that literal. However, this operation is somewhat expensive to perform,
and also rather annoying to program in Agda. Therefore, it has been omitted
from this implementation.
