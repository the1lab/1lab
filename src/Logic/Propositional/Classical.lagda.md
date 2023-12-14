<!--
```agda
open import 1Lab.Prelude hiding (_∈_)

open import Data.Bool
open import Data.List hiding (_++_ ; drop ; tabulate)
open import Data.Fin using (Fin; fzero; fsuc; weaken; inject; _[_≔_])
open import Data.Nat
open import Data.Sum

open import Meta.Brackets
```
-->

```agda
module Logic.Propositional.Classical where
```

# Classical propositional logic {defines="classical-propositional-logic"}

Classical propositional logic is a simple classical logic that only
contains "atomic" propositions and connectives like "and", "or" and "not".
Notably, it does not contain any quantifiers like "forall" and "exists".

We can define the syntax of classical propositional logic in Agda as
the following indexed inductive type.

```agda
data Proposition (Γ : Nat) : Type where
  atom        : Fin Γ → Proposition Γ
  “⊤” “⊥”     : Proposition Γ
  _“∧”_ _“∨”_ : Proposition Γ → Proposition Γ → Proposition Γ
  “¬”_        : Proposition Γ → Proposition Γ
```

We represent atomic propositions as elements of `Fin`{.Agda},
and our indexing scheme gives an upper bound on the number of
atomic propositions.

Next, we introduce contexts; these are simply lists of propositions.

```agda
data Ctx (Γ : Nat) : Type where
  []  : Ctx Γ
  _⨾_ : Ctx Γ → Proposition Γ → Ctx Γ

_++_ : ∀ {Γ} → Ctx Γ → Ctx Γ → Ctx Γ
ψ ++ [] = ψ
ψ ++ (θ ⨾ P) = (ψ ++ θ) ⨾ P
```

We also define a membership relation for contexts.

```agda
data _∈_ {Γ : Nat} (P : Proposition Γ) : Ctx Γ → Type where
  here  : ∀ {ψ} → P ∈ (ψ ⨾ P)
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
  ⊥-elim  : ∀ {P} → ψ ⊢ “⊥” → ψ ⊢ P
```

The rules for "and" are more or less what one would expect.

```agda
  ∧-intro  : ∀ {P Q} → ψ ⊢ P → ψ ⊢ Q → ψ ⊢ P “∧” Q
  ∧-elim-l : ∀ {P Q} → ψ ⊢ P “∧” Q → ψ ⊢ P
  ∧-elim-r : ∀ {P Q} → ψ ⊢ P “∧” Q → ψ ⊢ Q
```

However, "or" is a bit trickier, as we need to add things to our
hypotheses in the elimination rule.

```agda
  ∨-intro-l : ∀ {P Q}   → ψ ⊢ P → ψ ⊢ P “∨” Q
  ∨-intro-r : ∀ {P Q}   → ψ ⊢ Q → ψ ⊢ P “∨” Q
  ∨-elim    : ∀ {P Q R} → ψ ⊢ P “∨” Q → ψ ⨾ P ⊢ R → ψ ⨾ Q ⊢ R → ψ ⊢ R
```

Finally, we add the rules for negation. To ensure that we
are working with classical logic, we add a rule for double-negation
elimination.

```agda
  ¬-intro   : ∀ {P} → ψ ⨾ P ⊢ “⊥” → ψ ⊢ “¬” P
  ¬-elim    : ∀ {P} → ψ ⊢ “¬” P → ψ ⊢ P → ψ ⊢ “⊥”
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
<summary>
We omit the implementation of applying weakenings to the syntactic
types, since it's pretty much mechanical.
</summary>

```agda
¬weaken-suc-zero : Weakening (suc Γ) 0 → ⊥
¬weaken-suc-zero (weak σ) = ¬weaken-suc-zero σ

wk-suc : Weakening Γ Δ → Weakening Γ (suc Δ)
wk-suc done     = weak done
wk-suc (weak σ) = weak (wk-suc σ)

!wk : Weakening 0 Γ
!wk {Γ = zero}  = done
!wk {Γ = suc Γ} = wk-suc !wk

inc-prop : Proposition Γ → Proposition (suc Γ)
inc-prop (atom x)  = atom (weaken x)
inc-prop “⊤”       = “⊤”
inc-prop “⊥”       = “⊥”
inc-prop (p “∧” q) = inc-prop p “∧” inc-prop q
inc-prop (p “∨” q) = inc-prop p “∨” inc-prop q
inc-prop (“¬” p)   = “¬” (inc-prop p)

inc-ctx : Ctx Γ → Ctx (suc Γ)
inc-ctx []      = []
inc-ctx (ψ ⨾ P) = inc-ctx ψ ⨾ inc-prop P

inc-atom : P ∈ ψ → inc-prop P ∈ inc-ctx ψ
inc-atom here      = here
inc-atom (there x) = there (inc-atom x)

inc-proof : ψ ⊢ P → inc-ctx ψ ⊢ inc-prop P
inc-proof (hyp x)        = hyp (inc-atom  x)
inc-proof ⊤-intro        = ⊤-intro
inc-proof (⊥-elim p)     = ⊥-elim (inc-proof p)
inc-proof (∧-intro p q)  = ∧-intro (inc-proof p) (inc-proof q)
inc-proof (∧-elim-l p)   = ∧-elim-l (inc-proof p)
inc-proof (∧-elim-r p)   = ∧-elim-r (inc-proof p)
inc-proof (∨-intro-l p)  = ∨-intro-l (inc-proof p)
inc-proof (∨-intro-r p)  = ∨-intro-r (inc-proof p)
inc-proof (∨-elim p q r) = ∨-elim (inc-proof p) (inc-proof q) (inc-proof r)
inc-proof (¬-intro p)    = ¬-intro (inc-proof p)
inc-proof (¬-elim p q)   = ¬-elim (inc-proof p) (inc-proof q)
inc-proof (dneg-elim p)  = dneg-elim (inc-proof p)

bump-prop : Proposition Γ → Proposition (suc Γ)
bump-prop (atom x)  = atom (fsuc x)
bump-prop “⊤”       = “⊤”
bump-prop “⊥”       = “⊥”
bump-prop (p “∧” q) = bump-prop p “∧” bump-prop q
bump-prop (p “∨” q) = bump-prop p “∨” bump-prop q
bump-prop (“¬” p)   = “¬” bump-prop p

bump-ctx : Ctx Γ → Ctx (suc Γ)
bump-ctx []      = []
bump-ctx (ψ ⨾ P) = bump-ctx ψ ⨾ bump-prop P

bump-atom : P ∈ ψ → bump-prop P ∈ bump-ctx ψ
bump-atom here      = here
bump-atom (there p) = there (bump-atom p)

bump-proof : ψ ⊢ P → bump-ctx ψ ⊢ bump-prop P
bump-proof (hyp x)        = hyp (bump-atom x)
bump-proof ⊤-intro        = ⊤-intro
bump-proof (⊥-elim p)     = ⊥-elim (bump-proof p)
bump-proof (∧-intro p q)  = ∧-intro (bump-proof p) (bump-proof q)
bump-proof (∧-elim-l p)   = ∧-elim-l (bump-proof p)
bump-proof (∧-elim-r p)   = ∧-elim-r (bump-proof p)
bump-proof (∨-intro-l p)  = ∨-intro-l (bump-proof p)
bump-proof (∨-intro-r p)  = ∨-intro-r (bump-proof p)
bump-proof (∨-elim p q r) = ∨-elim (bump-proof p) (bump-proof q) (bump-proof r)
bump-proof (¬-intro p)    = ¬-intro (bump-proof p)
bump-proof (¬-elim p q)   = ¬-elim (bump-proof p) (bump-proof q)
bump-proof (dneg-elim p)  = dneg-elim (bump-proof p)

wk-atom : Weakening Γ Δ → Fin Γ → Fin Δ
wk-atom done     x = x
wk-atom (weak σ) x = wk-atom σ (weaken x)

wk-prop : Weakening Γ Δ → Proposition Γ → Proposition Δ
wk-prop done     P = P
wk-prop (weak σ) P = wk-prop σ (inc-prop P)

wk-ctx : Weakening Γ Δ → Ctx Γ → Ctx Δ
wk-ctx done     ψ = ψ
wk-ctx (weak σ) ψ = wk-ctx σ (inc-ctx ψ)

wk-proof : (σ : Weakening Γ Δ) → ψ ⊢ P → wk-ctx σ ψ ⊢ wk-prop σ P
wk-proof done     pf = pf
wk-proof (weak σ) pf = wk-proof σ (inc-proof pf)

shift-atom : Weakening Γ Δ → Fin Γ → Fin Δ
shift-atom done     i = i
shift-atom (weak σ) i = shift-atom σ (fsuc i)

shift-prop : Weakening Γ Δ → Proposition Γ → Proposition Δ
shift-prop done     p = p
shift-prop (weak σ) p = shift-prop σ (bump-prop p)

shift-ctx : Weakening Γ Δ → Ctx Γ → Ctx Δ
shift-ctx done     ψ = ψ
shift-ctx (weak σ) ψ = shift-ctx σ (bump-ctx ψ)

shift-ctx-[]
  : (σ : Weakening Γ Δ)
  → shift-ctx σ [] ≡ []
shift-ctx-[] done = refl
shift-ctx-[] (weak σ) = shift-ctx-[] σ

shift-ctx-⨾
  : (σ : Weakening Γ Δ)
  → (ψ : Ctx Γ) (P : Proposition Γ)
  → shift-ctx σ (ψ ⨾ P) ≡ shift-ctx σ ψ ⨾ shift-prop σ P
shift-ctx-⨾ done     ψ P = refl
shift-ctx-⨾ (weak σ) ψ P = shift-ctx-⨾ σ (bump-ctx ψ) (bump-prop P)

shift-prop-“¬”
  : (σ : Weakening Γ Δ)
  → (P : Proposition Γ)
  → shift-prop σ (“¬” P) ≡ “¬” (shift-prop σ P)
shift-prop-“¬” done     P = refl
shift-prop-“¬” (weak σ) P = shift-prop-“¬” σ (bump-prop P)
```
</details>

## Context inclusions

We also want to be able to modify our collection of hypotheses.  We do
this by defining a notion of context inclusion, where an inclusion
$\Gamma \to \Delta$ denotes that we can obtain every hypothesis in
$\Delta$ by dropping hypotheses from $\Gamma$. We call such context
inclusions **renamings**.

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
p      ∘rn done   = p
p      ∘rn drop q = drop (p ∘rn q)
drop p ∘rn keep q = drop (p ∘rn q)
keep p ∘rn keep q = keep (p ∘rn q)
```

We also have a renaming that drops every hypothesis, and
renamings that project out half of a context. Categorically,
these correspond to the maps into the [[terminal object]]
and maps out of the [[product]], resp.

```agda
!rn : Rename ψ []
!rn {ψ = []}    = done
!rn {ψ = ψ ⨾ x} = drop !rn

π₁-rn : Rename (ψ ++ θ) ψ
π₁-rn {θ = []}    = idrn
π₁-rn {θ = θ ⨾ P} = drop π₁-rn

π₂-rn : Rename (ψ ++ θ) θ
π₂-rn {θ = []}    = !rn
π₂-rn {θ = θ ⨾ P} = keep π₂-rn
```

Renamings act contravariantly on variables and derivations.
In categorical terms, this induces a presheaf on the category of
contexts.

```agda
rename-hyp : Rename ψ θ → P ∈ θ → P ∈ ψ
rename-hyp (drop rn) mem         = there (rename-hyp rn mem)
rename-hyp (keep rn) here        = here
rename-hyp (keep rn) (there mem) = there (rename-hyp rn mem)

rename : Rename ψ θ → θ ⊢ P → ψ ⊢ P
rename rn (hyp x)        = hyp (rename-hyp rn x)
rename rn ⊤-intro        = ⊤-intro
rename rn (⊥-elim p)     = ⊥-elim (rename rn p)
rename rn (∧-intro p q)  = ∧-intro (rename rn p) (rename rn q)
rename rn (∧-elim-l p)   = ∧-elim-l (rename rn p)
rename rn (∧-elim-r p)   = ∧-elim-r (rename rn p)
rename rn (∨-intro-l p)  = ∨-intro-l (rename rn p)
rename rn (∨-intro-r p)  = ∨-intro-r (rename rn p)
rename rn (∨-elim p q r) = ∨-elim
  (rename rn p) (rename (keep rn) q) (rename (keep rn) r)
rename rn (¬-intro p)    = ¬-intro (rename (keep rn) p)
rename rn (¬-elim p q)   = ¬-elim (rename rn p) (rename rn q)
rename rn (dneg-elim p)  = dneg-elim (rename rn p)
```

## Some elementary theorems

With those bits of structural work completed, we can focus our attention
to some theorems. First, note that we can prove the law of excluded middle.

```agda
lem : ∀ {Γ} {ψ : Ctx Γ} (P : Proposition Γ) → ψ ⊢ P “∨” (“¬” P)
lem P =
  dneg-elim                 $
  ¬-intro                   $
  ¬-elim (hyp here)         $
  ∨-intro-r                 $
  ¬-intro                   $
  ¬-elim (hyp (there here)) $
  ∨-intro-l (hyp here)
```

We also have all four De Morgan laws.

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
  ⇒-elim {Q = Q} imp p = ∨-elim imp
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
“⋀” []      = “⊤”
“⋀” (ψ ⨾ P) = “⋀” ψ “∧” P

⋀-intro : (∀ {P} → P ∈ ψ → θ ⊢ P) → θ ⊢ “⋀” ψ
⋀-intro {ψ = []}    pfs = ⊤-intro
⋀-intro {ψ = ψ ⨾ P} pfs = ∧-intro (⋀-intro (pfs ∘ there)) (pfs here)

⋀-elim : P ∈ ψ → θ ⊢ “⋀” ψ → θ ⊢ P
⋀-elim here      p = ∧-elim-r p
⋀-elim (there x) p = ⋀-elim x (∧-elim-l p)
```

We can also define an n-ary implication connective.

```agda
_“⇛”_ : Ctx Γ → Proposition Γ → Proposition Γ
[]      “⇛” P = P
(ψ ⨾ Q) “⇛” P = ψ “⇛” (Q “⇒” P)

⇛-intro : θ ++ ψ ⊢ P → θ ⊢ ψ “⇛” P
⇛-intro {ψ = []}    p = p
⇛-intro {ψ = ψ ⨾ Q} p = ⇛-intro (⇒-intro p)

⇛-uncurry : θ ⊢ ψ “⇛” P → θ ++ ψ ⊢ P
⇛-uncurry {ψ = []}    p = p
⇛-uncurry {ψ = ψ ⨾ Q} p = ⇒-uncurry (⇛-uncurry p)

⇛-elim : θ ⊢ (ψ ⨾ P) “⇛” Q → θ ⊢ P → θ ⊢ ψ “⇛” Q
⇛-elim {ψ = ψ} p q = ⇛-intro (⇒-elim (⇛-uncurry {ψ = ψ} p) (rename π₁-rn q))
```

## Semantics

The most obvious way to interpret classical logic is as operations on
booleans.

```agda
sem-prop : ∀ {Γ} → Proposition Γ → (Fin Γ → Bool) → Bool
sem-prop (atom x)  ρ = ρ x
sem-prop “⊤”       ρ = true
sem-prop “⊥”       ρ = false
sem-prop (P “∧” Q) ρ = and (sem-prop P ρ) (sem-prop Q ρ)
sem-prop (P “∨” Q) ρ = or (sem-prop P ρ) (sem-prop Q ρ)
sem-prop (“¬” P)   ρ = not (sem-prop P ρ)

sem-ctx : ∀ {Γ} → Ctx Γ → (Fin Γ → Bool) → Bool
sem-ctx ψ ρ = sem-prop (“⋀” ψ) ρ
```

<!--
```agda
instance
  ⟦⟧-Proposition : ∀ {Γ} → ⟦⟧-notation (Proposition Γ)
  ⟦⟧-Proposition {Γ = Γ} = brackets ((Fin Γ → Bool) → Bool) sem-prop

  ⟦⟧-Ctx : ∀ {Γ} → ⟦⟧-notation (Ctx Γ)
  ⟦⟧-Ctx {Γ = Γ} = brackets ((Fin Γ → Bool) → Bool) sem-ctx

  Number-Proposition : ∀ {Γ} → Number (Proposition Γ)
  Number-Proposition {Γ} .Number.Constraint k = k Data.Nat.< Γ
  Number-Proposition .Number.fromNat n        = atom (fromNat n)

opaque
  unfolding _“⇒”_
  ⇒-sem
    : ∀ {Γ} {P Q : Proposition Γ}
    → ∀ (ρ : Fin Γ → Bool) → ⟦ P “⇒” Q ⟧ ρ ≡ imp (⟦ P ⟧ ρ) (⟦ Q ⟧ ρ)
  ⇒-sem {P = P} {Q = Q} ρ =
    imp-not-or (⟦ P ⟧ ρ) (⟦ Q ⟧ ρ)
```
-->

We also define a notion of semantic entailment, wherein `ψ` semantically
entails `P` when for every assigment of variables `ρ`, if `⟦ ψ ⟧ ρ ≡
true`, then `⟦ P ⟧ ρ ≡ true`.

```agda
_⊨_ : ∀ {Γ} → Ctx Γ → Proposition Γ → Type
_⊨_ {Γ} ψ P = ∀ (ρ : Fin Γ → Bool) → ⟦ ψ ⟧ ρ ≡ true → ⟦ P ⟧ ρ ≡ true
```

## Soundness

Soundness is something that is often poorly explained in classical logic.

The traditional definition goes something like this: a logic is sound if
every _provable_ theorem `ψ ⊢ P` is _true_. This definition obscures
what is really going on: what we care about is that a provable theorem
`ψ ⊢ P` is true **in some semantics**.

For classical propositional logic, it _happens to be the case_ that we
can focus our attention on one semantics (the booleans) --- we'll see
ahead why this is the case --- so authors often conflate "true" with
"true _in this particular semantics_".

The actual statement of soundness that we will be using is the
following: if `ψ ⊢ P` is provable, then we have the semantic entailment
`ψ ⊨ P`. This follows by induction on the proof trees, and it's mostly
mechanical.

```agda
hyp-sound : ∀ {Γ} {ψ : Ctx Γ} {P : Proposition Γ} → P ∈ ψ → ψ ⊨ P
hyp-sound here      ρ hyps-true = and-reflect-true-r hyps-true
hyp-sound (there m) ρ hyps-true = hyp-sound m ρ (and-reflect-true-l hyps-true)

sound : ψ ⊢ P → ψ ⊨ P
sound (hyp x)    ρ hyps-true = hyp-sound x ρ hyps-true
sound ⊤-intro    ρ hyps-true = refl
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
sound (∨-elim p q r) ρ hyps-true with or-reflect-true (sound p ρ hyps-true)
... | inl P-true = sound q ρ (ap₂ and hyps-true P-true)
... | inr Q-true = sound r ρ (ap₂ and hyps-true Q-true)

sound (¬-intro {P = P} p) ρ hyps-true =
  Bool-elim (λ b → ⟦ P ⟧ ρ ≡ b → not b ≡ true)
    (λ P-true → sound p ρ (ap₂ and hyps-true P-true))
    (λ _ → refl)
    (⟦ P ⟧ ρ) refl
sound (¬-elim {P = P} p q) ρ hyps-true =
  absurd (not-no-fixed (sound q ρ hyps-true ∙ sym (sound p ρ hyps-true)))
sound (dneg-elim {P = P} p) ρ hyps-true =
  sym (not-involutive (⟦ P ⟧ ρ)) ∙ sound p ρ hyps-true
```

## Completeness

As mentioned earlier, we often think of classical propositional logic as
having a *single* semantics. This is largely justified by the fact that
if `ψ` semantically entails `P` in the booleans, then we can prove that
`ψ ⊢ P`! In other words, the Boolean semantics for classical
propositional logic is **complete**.

This somewhat miraculous theorem is often taken for granted.
Completeness is why truth-tables are a valid form of reasoning, but this
is hardly ever mentioned when teaching logic. As we shall soon see, this
theorem isn't exactly trivial, either.

First, let us lay out our general proof strategy. We shall start by
building a context $\hat{\rho}$ from an assignment $\rho$ that contains
only (potentially negated) atoms. If $\rho$ assigns `true` to an atom
$x$, we will add $x$ to $\hat{\rho}$. Conversely, if $\rho$ assigns
false to $x$, we add $\neg x$ to $\hat{\rho}$.

We will then show that for any assignment $\rho$, if $\sem{P} \rho$ is
true, then $\hat{\rho} \vdash P$; likewise, if $\sem{P} \rho$ is false,
then $\hat{\rho} \vdash \neg P$.

From this fact, we can deduce that $\vDash P$ entails $\vdash P$ by
repeatedly applying excluded middle to every single atom in $P$, and
applying our previous lemmas when we are done. Finally, we can transform
any sequent $\psi \vdash P$ into an equivalent sequent in a closed
context by repeatedly introducing implications, which lets us apply the
argument involving excluded middle.

With that sketch out of the way, let's dive into the details!  First, we
define a function `tabulate` that forms a context from an assignment;
this is the $\hat{\rho}$ from the proof sketch. Some variable munging is
required to make Agda happy, but it is more or less what one would
expect.

```agda
tabulate : (Fin Γ → Bool) → Ctx Γ
tabulate {Γ = zero}  ρ = []
tabulate {Γ = suc Γ} ρ =
  bump-ctx (tabulate (ρ ∘ fsuc)) ⨾ (if ρ 0 then 0 else “¬” 0)
```

Next, some small helper lemmas that let us link assignments of atoms and
proofs of those atoms. Essentially, these state that if $\rho(x)$
assigns a truth value to $x$, then we should be able to prove this under
the assumptions $\hat{\rho}$.

```agda
tabulate-atom-true
  : (x : Fin Γ)
  → (ρ : Fin Γ → Bool)
  → ρ x ≡ true
  → tabulate ρ ⊢ atom x
tabulate-atom-true {Γ = suc Γ} fzero ρ x-true with ρ 0
... | true  = hyp here
... | false = absurd (true≠false $ sym x-true)
tabulate-atom-true {Γ = suc Γ} (fsuc x) ρ x-true =
  rename (drop idrn) (bump-proof (tabulate-atom-true x (ρ ∘ fsuc) x-true))

tabulate-atom-false
  : (x : Fin Γ)
  → (ρ : Fin Γ → Bool)
  → ρ x ≡ false
  → tabulate ρ ⊢ “¬” atom x
tabulate-atom-false {Γ = suc Γ} fzero ρ x-false with ρ 0
... | false = hyp here
... | true  = absurd (true≠false x-false)
tabulate-atom-false {Γ = suc Γ} (fsuc x) ρ x-false =
  rename (drop idrn) (bump-proof (tabulate-atom-false x (ρ ∘ fsuc) x-false))
```

Now onto the key lemmas. By performing mutual induction on $P$, we can
note that if $\sem{P} \rho$ is true, then $\hat{\rho} \vdash P$ and,
conversely, that $\hat{\rho} \vdash \neg P$ if $\sem{P} \rho$ is false.

```agda
tabulate-true
  : ∀ (P : Proposition Γ) (ρ : Fin Γ → Bool)
  → ⟦ P ⟧ ρ ≡ true
  → tabulate ρ ⊢ P

tabulate-false
  : ∀ (P : Proposition Γ) (ρ : Fin Γ → Bool)
  → ⟦ P ⟧ ρ ≡ false
  → tabulate ρ ⊢ “¬” P

tabulate-true (atom x)  ρ P-true = tabulate-atom-true x ρ P-true
tabulate-true “⊤”       ρ P-true = ⊤-intro
tabulate-true “⊥”       ρ P-true = absurd (true≠false $ sym P-true)
tabulate-true (P “∧” Q) ρ P∧Q-true = ∧-intro
  (tabulate-true P ρ (and-reflect-true-l P∧Q-true))
  (tabulate-true Q ρ (and-reflect-true-r P∧Q-true))
tabulate-true (P “∨” Q) ρ P∨Q-true with or-reflect-true P∨Q-true
... | inl P-true = ∨-intro-l (tabulate-true P ρ P-true)
... | inr Q-true = ∨-intro-r (tabulate-true Q ρ Q-true)
tabulate-true (“¬” P) ρ P-true = tabulate-false P ρ (not-inj P-true)

tabulate-false (atom x)  ρ P-false = tabulate-atom-false x ρ P-false
tabulate-false “⊤”       ρ P-false = absurd (true≠false P-false)
tabulate-false “⊥”       ρ P-false = ¬-intro (hyp here)
tabulate-false (P “∧” Q) ρ P∧Q-false with and-reflect-false P∧Q-false
... | inl P-false = ¬∧-intro-l (tabulate-false P ρ P-false)
... | inr Q-false = ¬∧-intro-r (tabulate-false Q ρ Q-false)
tabulate-false (P “∨” Q) ρ P∨Q-false = ¬∨-intro
  (tabulate-false P ρ (or-reflect-false-l P∨Q-false))
  (tabulate-false Q ρ (or-reflect-false-r P∨Q-false))
tabulate-false (“¬” P) ρ P-false =
  dneg-intro (tabulate-true P ρ (not-inj P-false))
```

Next, let $P$ be a proposition and let $\rho$ be an assignment for the
first $n$ atoms in $P$. If $P$ is a tautology, then $\hat{\rho} \vdash P$.
This follows from induction on the number of atoms not assigned by $\rho$.
If $\rho$ assigns all of the atoms of $P$, then by our previous lemma we
have $\hat{\rho} \vdash P$. For the inductive step, let $x$ be a atom
not covered by $\rho$. Excluded middle lets us case on the truth value
of $x$; if it is true, then we extend $\rho$ with $x := \top$, and use
the induction hypothesis. Likewise, if $x$ is false, then we extend
$\rho$ with $x := \bot$.

We'll then show an appropriate generalisation of the completeness
theorem, which will allow us to apply induction. Specifically, we'll
show that, if $P$ is a tautology in $k+n$ atoms, and we have an
assignment $\rho$ of truth values for the first $k$ atoms in $P$, then
$\hat{\rho} \vdash P$, by induction on $n$, i.e. the number of atoms
which $\rho$ does _not_ assign.

```agda
tabulate-complete
  : ∀ {Δ Γ} (P : Proposition Γ)
  → (σ : Weakening Δ Γ) (ρ : Fin Δ → Bool)
  → [] ⊨ P → shift-ctx σ (tabulate ρ) ⊢ P
```

The base case is when we have _no_ new atoms: we can then appeal to our
previous theorem `tabulate-true`{.Agda}.

```agda
tabulate-complete P done ρ P-taut =
  tabulate-true P ρ (P-taut ρ refl)
```

For the inductive step, we have some $1+n$ new atoms, and we're free to
assume that any tautology in $k+n$ atoms is a theorem. We use this
induction hypothesis twice, once on $\rho$ extended with $x := \top$,
and once on it extended with $x := \bot$. We now have proofs that $x
\vdash P$ and $\neg x \vdash P$; but by the excluded middle (and
disjunction elimination), this suffices to prove $P$!

```agda
tabulate-complete {Γ = Γ} P (weak σ) ρ P-taut = ∨-elim
  (lem (shift-prop σ (atom 0)))
  (subst (_⊢ P)
    (shift-ctx-⨾ σ _ _)
    (tabulate-complete P σ (ρ [ 0 ≔ true ]) P-taut))
  (subst (_⊢ P)
    (shift-ctx-⨾ σ _ _ ∙ ap₂ _⨾_ refl (shift-prop-“¬” σ (atom 0)))
    (tabulate-complete P σ (ρ [ 0 ≔ false ]) P-taut))
```

If we start this with an empty assignment, we will construct a gigantic
proof, which applies excluded middle to every single atom in $P$, and
then applies the relevant introduction rules at the leaves. Despite the
obvious inefficiency of this procedure, it allows us to deduce that we
have completeness for tautologies.

```agda
taut-complete : (P : Proposition Γ) → [] ⊨ P → [] ⊢ P
taut-complete P taut =
  subst (_⊢ P) (shift-ctx-[] !wk) (tabulate-complete P !wk (λ ()) taut)
```

Finally, we note that proofs of $P_1 \to \cdots \to P_n \to Q$ yield
proofs of $P_1, \cdots, P_n \vdash Q$, and likewise for semantic
entailments.

```agda
⇛-closed : [] ⊢ ψ “⇛” P → ψ ⊢ P
⇛-closed {ψ = []}    p = p
⇛-closed {ψ = ψ ⨾ Q} p = ⇒-uncurry (⇛-closed p)

⇛-valid : ∀ (ψ : Ctx Γ) (P : Proposition Γ) → ψ ⊨ P → [] ⊨ (ψ “⇛” P)
⇛-valid []      P valid = valid
⇛-valid (ψ ⨾ Q) P valid ρ taut = ap₂ and refl
  (⇛-valid ψ (Q “⇒” P) (λ ρ' ψ-true → it ρ' ψ-true (⟦ Q ⟧ ρ') refl) ρ taut)
```

<!--
```agda
  where
  it : ∀ ρ' (ψ-true : ⟦ ψ ⟧ ρ' ≡ true) (b : Bool)
     → ⟦ Q ⟧ ρ' ≡ b
     → ⟦ Q “⇒” P ⟧ ρ' ≡ true
  it ρ' ψ-true true Q-true =
    ⇒-sem ρ'
    ∙ ap₂ imp refl (valid ρ' (ap₂ and ψ-true Q-true))
    ∙ imp-truer _
  it ρ' ψ-true false Q-false =
    ⇒-sem ρ' ∙ ap₂ imp Q-false refl
```
-->

This lets us generalize our result for tautologies to any
proposition-in-context $\psi \vDash P$!

```agda
complete : ψ ⊨ P → ψ ⊢ P
complete {ψ = ψ} {P = P} valid =
  ⇛-closed $ taut-complete (ψ “⇛” P) (⇛-valid ψ P valid)
```
