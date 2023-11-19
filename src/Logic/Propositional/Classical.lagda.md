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

# Classical Propositional Logic {defines="classical-propositional-logic"}

Classical propositional logic is a simple classical logic that only
contains "atomic" propositions and connectives like "and", "or" and "not".
Notably, it does not contain any quantifiers like "forall" and "exists".

We can define the syntax of classical propositional logic in Agda as
the following indexed inductive type.

```agda
data Proposition (Γ : Nat) : Type where
  atom : Fin Γ → Proposition Γ
  “⊤” : Proposition Γ
  “⊥” : Proposition Γ
  _“∧”_ : Proposition Γ → Proposition Γ → Proposition Γ
  _“∨”_ : Proposition Γ → Proposition Γ → Proposition Γ
  “¬”_ : Proposition Γ → Proposition Γ
```

We represent atomic propositions as elements of `Fin`{.Agda},
and our indexing scheme gives an upper bound on the number of
atomic propositions.

Next, we introduce contexts; these are simply lists of propositions.

```agda
data Ctx (Γ : Nat) : Type where
  [] : Ctx Γ
  _⨾_ : Ctx Γ → Proposition Γ → Ctx Γ

_++_ : ∀ {Γ} → Ctx Γ → Ctx Γ → Ctx Γ
ψ ++ [] = ψ
ψ ++ (θ ⨾ P) = (ψ ++ θ) ⨾ P
```

We also define a membership relation for contexts.

```agda
data _∈_ {Γ : Nat} (P : Proposition Γ) : Ctx Γ → Type where
  here : ∀ {ψ} → P ∈ (ψ ⨾ P)
  there : ∀ {ψ Q} → P ∈ ψ → P ∈ (ψ ⨾ Q)
```

<!--
```agda
infixr 12 _“⇒”_
infixr 11 _“∧”_
infixr 10 _“∨”_
infixl 10 _⨾_
infix 9 _⊢_ _⊨_
```
-->

Finally, we define a natural deduction proof calculus for classical
propositional logic. Our proof systems is encoded as an indexed inductive
`_⊢_`{.Agda}; elements of `ψ ⊢ P` are proof trees that show `P` from some
set of hypotheses `ψ`.

```agda
data _⊢_ {Γ : Nat} (ψ : Ctx Γ) : Proposition Γ → Type where
```

Our first rule is pretty intuitive: If `P` is in our hypotheses `ψ`,
then we can deduce `P` from `ψ`.

```agda
  hyp : ∀ {P} → P ∈ ψ → ψ ⊢ P
```

Next, we give an introduction rule for "true" and an elimination rule
for "false".

```agda
  ⊤-intro : ψ ⊢ “⊤”
  ⊥-elim : ∀ {P} → ψ ⊢ “⊥” → ψ ⊢ P
```

The rules for "and" are more or less what one would expect.

```agda
  ∧-intro : ∀ {P Q} → ψ ⊢ P → ψ ⊢ Q → ψ ⊢ P “∧” Q
  ∧-elim-l : ∀ {P Q} → ψ ⊢ P “∧” Q → ψ ⊢ P
  ∧-elim-r : ∀ {P Q} → ψ ⊢ P “∧” Q → ψ ⊢ Q
```

However, "or" is a bit trickier, as we need to add things to our
hypotheses in the elimination rule.

```agda
  ∨-intro-l : ∀ {P Q} → ψ ⊢ P → ψ ⊢ P “∨” Q
  ∨-intro-r : ∀ {P Q} → ψ ⊢ Q → ψ ⊢ P “∨” Q
  ∨-elim : ∀ {P Q R} → ψ ⊢ P “∨” Q → ψ ⨾ P ⊢ R → ψ ⨾ Q ⊢ R → ψ ⊢ R
```

Finally, we add the rules for negation. To ensure that we
are working with classical logic, we add a rule for double-negation
elimination.

```agda
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

Indexing the type of propositions by the number of atomic propositions
makes our life easier later. However, it does mean that we need to
define **weakening**, which lets us increase the upper bound on the
number of atoms in a proposition.

```agda
data Weakening (Γ : Nat) : Nat → Type where
  done : Weakening Γ Γ
  weak : ∀ {Δ} → Weakening (suc Γ) Δ → Weakening Γ Δ
```

<details>
<summary>We omit the details of weakening, as it is more or less
boilerplate.
</summary>

```agda
¬weaken-suc-zero : Weakening (suc Γ) 0 → ⊥
¬weaken-suc-zero (weak σ) = ¬weaken-suc-zero σ

inc-prop : Proposition Γ → Proposition (suc Γ)
inc-prop (atom x) = atom (weaken x)
inc-prop “⊤” = “⊤”
inc-prop “⊥” = “⊥”
inc-prop (p “∧” q) = inc-prop p “∧” inc-prop q
inc-prop (p “∨” q) = inc-prop p “∨” inc-prop q
inc-prop (“¬” p) = “¬” (inc-prop p)

inc-ctx : Ctx Γ → Ctx (suc Γ)
inc-ctx [] = []
inc-ctx (ψ ⨾ P) = inc-ctx ψ ⨾ inc-prop P

inc-atom : P ∈ ψ → inc-prop P ∈ inc-ctx ψ
inc-atom here = here
inc-atom (there x) = there (inc-atom x)

inc-proof : ψ ⊢ P → inc-ctx ψ ⊢ inc-prop P
inc-proof (hyp x) = hyp (inc-atom  x)
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

wk-atom : Weakening Γ Δ → Fin Γ → Fin Δ
wk-atom done x = x
wk-atom (weak σ) x = wk-atom σ (fsuc x)

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
</details>

## Context inclusions

We also want to be able to modify our collection of hypotheses.
We do this by defining a notion of context inclusion, where
an inclusion $\Gamma \to \Delta$ denotes that we can obtain every
hypotheses in $\Delta$ dropping some hypotheses in $\Gamma$. We call
such context inclusions **renamings**.

```agda
data Rename {Γ} : Ctx Γ → Ctx Γ → Type where
  done : Rename [] []
  drop : ∀ {ψ θ P} → Rename ψ θ → Rename (ψ ⨾ P) θ
  keep : ∀ {ψ θ P} → Rename ψ θ → Rename (ψ ⨾ P) (θ ⨾ P)
```

Identity renamings exist, and renamings are closed under composition.
With a bit of elbow grease, we could show that contexts and renamings
form a [[precategory]], thought we do not do so here.

```agda
idrn : Rename ψ ψ
idrn {ψ = []} = done
idrn {ψ = ψ ⨾ P} = keep (idrn {ψ = ψ})

_∘rn_ : Rename θ ζ → Rename ψ θ → Rename ψ ζ 
p ∘rn done = p
p ∘rn drop q = drop (p ∘rn q)
drop p ∘rn keep q = drop (p ∘rn q)
keep p ∘rn keep q = keep (p ∘rn q)
```

We also have a renaming that drops every hypothesis, and
renamings that project out half of a context. Categorically,
these correspond to the maps into the [[terminal object]]
and maps out of the [[product]], resp.

```agda
!rn : Rename ψ []
!rn {ψ = []} = done
!rn {ψ = ψ ⨾ x} = drop !rn

π₁-rn : Rename (ψ ++ θ) ψ
π₁-rn {θ = []} = idrn
π₁-rn {θ = θ ⨾ P} = drop π₁-rn

π₂-rn : Rename (ψ ++ θ) θ
π₂-rn {θ = []} = !rn
π₂-rn {θ = θ ⨾ P} = keep π₂-rn
```

Renamings act contravariantly on variables and derivations.
In categorical terms, this induces a presheaf on the category of
contexts.

```agda
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

With those bits of structural work completed, we can focus our attention
to some theorems. First, note that we can prove the law of excluded middle.

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
```

We also have all four DeMorgan laws.

```agda
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
```

As we are working in a classical setting, we can define implication
`P ⇒ Q` as `¬ P ∨ Q`. Note that the normal introduction and elimination
rules for implications are theorems.

```agda
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
```

We also prove some helpful extra lemmas regarding implications.

```agda
⇒-uncurry : ψ ⊢ P “⇒” Q → ψ ⨾ P ⊢ Q
⇒-uncurry p = ⇒-elim (rename (drop idrn) p) (hyp here)

⇒-flip : ψ ⊢ P “⇒” Q “⇒” R → ψ ⊢ Q “⇒” P “⇒” R
⇒-flip p =
  ⇒-intro $ ⇒-intro $
  ⇒-elim
    (⇒-elim (rename (drop (drop idrn)) p) (hyp here))
    (hyp (there here))
```

Next, we define a conjunction operator that works on lists of
propositions.

```agda
“⋀” : Ctx Γ → Proposition Γ
“⋀” [] = “⊤”
“⋀” (ψ ⨾ P) = “⋀” ψ “∧” P

⋀-intro : (∀ {P} → P ∈ ψ → θ ⊢ P) → θ ⊢ “⋀” ψ  
⋀-intro {ψ = []} pfs = ⊤-intro
⋀-intro {ψ = ψ ⨾ P} pfs = ∧-intro (⋀-intro (pfs ∘ there)) (pfs here)

⋀-elim : P ∈ ψ → θ ⊢ “⋀” ψ → θ ⊢ P
⋀-elim here p = ∧-elim-r p
⋀-elim (there x) p = ⋀-elim x (∧-elim-l p)
```

We can also define an n-ary implication connective.

```agda
_“⇛”_ : Ctx Γ → Proposition Γ → Proposition Γ
[] “⇛” P = P
(ψ ⨾ Q) “⇛” P = ψ “⇛” (Q “⇒” P)

⇛-intro : θ ++ ψ ⊢ P → θ ⊢ ψ “⇛” P
⇛-intro {ψ = []} p = p
⇛-intro {ψ = ψ ⨾ Q} p = ⇛-intro (⇒-intro p)

⇛-uncurry : θ ⊢ ψ “⇛” P → θ ++ ψ ⊢ P
⇛-uncurry {ψ = []} p = p
⇛-uncurry {ψ = ψ ⨾ Q} p = ⇒-uncurry (⇛-uncurry p)

⇛-elim : θ ⊢ (ψ ⨾ P) “⇛” Q → θ ⊢ P → θ ⊢ ψ “⇛” Q
⇛-elim {ψ = ψ} p q = ⇛-intro (⇒-elim (⇛-uncurry {ψ = ψ} p) (rename π₁-rn q))
```

This connective has a very useful property: if `ψ “⇛” P` in
an empty context, then `ψ ⊢ P`.

```agda
⇛-closed : [] ⊢ ψ “⇛” P → ψ ⊢ P
⇛-closed {ψ = []} p = p
⇛-closed {ψ = ψ ⨾ Q} p = ⇒-uncurry (⇛-closed p)
```

## Semantics

The most obvious way to interpret classical logic is as operations
on booleans.

```agda
sem-prop : ∀ {Γ} → Proposition Γ → (Fin Γ → Bool) → Bool
sem-prop (atom x) ρ = ρ x
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
```

<!--
```agda
opaque
  unfolding _“⇒”_
  ⇒-sem
    : ∀ {Γ} {P Q : Proposition Γ}
    → ∀ (ρ : Fin Γ → Bool) → ⟦ P “⇒” Q ⟧ ρ ≡ imp (⟦ P ⟧ ρ) (⟦ Q ⟧ ρ)
  ⇒-sem {P = P} {Q = Q} ρ =
    imp-not-or (⟦ P ⟧ ρ) (⟦ Q ⟧ ρ)
```
-->

We also define a notion of semantic entailment, wherein `ψ`
semantically entails `P` when for every assigment of variables
`ρ`, if `⟦ ψ ⟧ ρ ≡ true`, then `⟦ P ⟧ ρ ≡ true`.

```agda
_⊨_ : ∀ {Γ} → Ctx Γ → Proposition Γ → Type
_⊨_ {Γ} ψ P = ∀ (ρ : Fin Γ → Bool) → ⟦ ψ ⟧ ρ ≡ true → ⟦ P ⟧ ρ ≡ true
```

## Soundness

Soundness is something that is often poorly explained in classical logic.
The "normal" definition goes something like this: a logic is sound
if every provable theorem `ψ ⊢ P` is true. This definition obscures
what is really going on: what we care about is that a provable theorem
`ψ ⊢ P` is true **in some semantics**. For classical propositional logic,
it just so happens that we only care about one semantics[^1] (the booleans),
so authors often conflate "true" with "true in thhis particular semantics".

[^1]: We will see why this is the case in just a bit!

The actual statement of soundness that we will be using is the following:
if `ψ ⊢ P` is provable, then we have the semantic entailment `ψ ⊨ P`.
This follows by a rather easy induction on proof trees.

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
