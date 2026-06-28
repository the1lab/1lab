<!--
```agda
open import 1Lab.Prelude

open import Data.Partial.Total
open import Data.Partial.Base
open import Data.Vec.Base

open import Realisability.PCA

import Realisability.Data.Pair
import Realisability.PCA.Sugar
import Realisability.Data.Sum
```
-->

```agda
module Realisability.Base {ℓA} (pca@(𝔸 , _) : PCA ℓA) where
```

<!--
```agda
open Realisability.PCA.Sugar pca
open Realisability.Data.Pair pca
open Realisability.Data.Sum pca

private variable
  ℓ ℓ' ℓ'' : Level
  X Y Z : Type ℓ'
  n : Nat
```
-->

# Realisability predicates over sets

If we have a fixed notion of computation given by a [[partial
combinatory algebra]] $\bA$, we can think of the type of functions $X
\to \bP(\bA)$ valued in the [[power set]] of $\bA$ as a type of
"nonstandard predicates over $X$", where some nonstandard predicate $P$
over $X$ assigns to each $x : X$ a set $P(x) \sube \bA$ of
*[[values|values in a pca]] that witness the truth of $P$*.

More importantly, these **realisability predicates** can be equipped
with a notion of entailment, again relative to $\bA$. Moreover, we can
define this entailment relative to a function $X \to Y$, for $P$ a
predicate over $X$ and $Q$ a predicate over $Y$.^[If we think of $X$ and
$Y$ as *contexts* for the definitions of $P$ and $Q$, then this 3-place
entailment relation is defined relative to a *substitution* $X \to Y$.]
We define the type of entailment witnesses $P \vdash_f Q$ to consist of
[[programs|values in a pca]] $\tt{r} : \bA$ which associate to
each $P$-realiser $a$ of $x$ a $Q$-realiser $\tt{r}~ \tt{a}$ of $f\, x$.

```agda
record
  [_]_⊢_ (f : X → Y) (P : X → ℙ⁺ 𝔸) (Q : Y → ℙ⁺ 𝔸)
    : Type (level-of X ⊔ level-of Y ⊔ ℓA) where

  field
    realiser : ↯⁺ 𝔸
    tracks   : ∀ {x} {a : ↯ ⌞ 𝔸 ⌟} (ah : a ∈ P x) → realiser ⋆ a ∈ Q (f x)
```

<!--
```agda
  realiser↓ : ∀ {x} {a : ↯ ⌞ 𝔸 ⌟} (ah : a ∈ P x) → ⌞ realiser ⋆ a ⌟
  realiser↓ ah = Q _ .def (tracks  ah)

private unquoteDecl eqv' = declare-record-iso eqv' (quote [_]_⊢_)

open [_]_⊢_ public

instance
  tracks-to-term : ∀ {V : Type} {P : X → ℙ⁺ 𝔸} {Q : Y → ℙ⁺ 𝔸} {f : X → Y} → To-term V ([ f ] P ⊢ Q)
  tracks-to-term = record { to = λ x → const (x .realiser) }

  tracks-to-part : ∀ {P : X → ℙ⁺ 𝔸} {Q : Y → ℙ⁺ 𝔸} {f : X → Y} → To-part ([ f ] P ⊢ Q) ⌞ 𝔸 ⌟
  tracks-to-part = record { to-part = λ x → x .realiser .fst }

private
  variable P Q R : X → ℙ⁺ 𝔸

  subst-∈ : (P : ℙ⁺ 𝔸) {x y : ↯ ⌞ 𝔸 ⌟} → x ∈ P → y ≡ x → y ∈ P
  subst-∈ P hx p = subst (_∈ P) (sym p) hx
```
-->

## Basic structural rules

We can now investigate the basic rules of this realisability logic,
which work regardless of what the chosen PCA $\bA$ is. First, we have
that entailment is reflexive (the "axiom" rule) and transitive (the
"cut" rule). These are witnessed by the identity *program* and, if
$\tt{f}$ witnesses $Q \vdash R$ and $\tt{g}$ witnesses $P \vdash Q$,
then the composition
$$
\langle x \rangle \tt{f}~ (\tt{g}~ x)
$$
witnesses $P \vdash R$.

```agda
id⊢ : [ id ] P ⊢ P
id⊢ {P = P} = record where
  realiser = val ⟨ x ⟩ x

  tracks ha = subst-∈ (P _) ha (abs-β _ []v (_ , P _ .def ha))

_∘⊢_ : ∀ {f g} → [ g ] Q ⊢ R → [ f ] P ⊢ Q → [ g ∘ f ] P ⊢ R
_∘⊢_ {R = R} {P = P} α β = record where
  realiser = val ⟨ x ⟩ α `· (β `· x)

  tracks {a = a} ha = subst-∈ (R _) (α .tracks (β .tracks ha)) $
    (val ⟨ x ⟩ α `· (β `· x)) ⋆ a ≡⟨ abs-β _ []v (a , P _ .def ha) ⟩
    α ⋆ (β ⋆ a)                   ∎
```

## Conjunction

As a representative example of logical realisability connective, we can
define the conjunction of $\bA$-predicates over a common base type.
Fixing $P, Q : X \to \bP(\bA)$, we define the set of $(P \land
Q)$-realisers for $x$ to be
$$
\{ \tt{pair}~ u~ v\ |\ u, v : \bA, u \in P(x), v \in Q(x) \}
$$
that is, a value $p : \bA$ witnesses $(P \land Q)(x)$ if it is a pair
and its first component witnesses $P(x)$ and its second component
witnesses $Q(x)$. We think of this as a *strict* definition, since it
demands the witness to be literally, syntactically, a $\tt{pair}$; we
could also have a *lazy* definition, where all we ask is that the
witness be defined and its first and second *projections* witness $P$
and $Q$ respectively, i.e. the set
$$
\{ e \ |\ \tt{fst}~ e \in P(x), \tt{snd}~ e \in Q(x) \}
$$.

```agda
_∧T_ : (P Q : X → ℙ⁺ 𝔸) → X → ℙ⁺ 𝔸
(P ∧T Q) x .mem a = elΩ $
  Σ[ u ∈ ↯ ⌞ 𝔸 ⌟ ] Σ[ v ∈ ↯ ⌞ 𝔸 ⌟ ]
    a ≡ `pair ⋆ u ⋆ v × u ∈ P x × v ∈ Q x
(P ∧T Q) x .def = rec! λ u v α rx ry →
  subst ⌞_⌟ (sym α) (`pair↓₂ (P _ .def rx) (Q _ .def ry))
```

With this strict definition, we can show that the conjunction implies
both conjuncts, and these implications are tracked by the `` `fst
``{.Agda} and `` `snd ``{.Agda} projection programs respectively.

```agda
π₁⊢ : [ id ] (P ∧T Q) ⊢ P
π₁⊢ {P = P} {Q = Q} = record where
  realiser = `fst

  tracks {a = a} = elim! λ p q α pp qq → subst-∈ (P _) pp $
    `fst ⋆ a               ≡⟨ ap (`fst ⋆_) α ⟩
    `fst ⋆ (`pair ⋆ p ⋆ q) ≡⟨ `fst-β (P _ .def pp) (Q _ .def qq) ⟩
    p                      ∎

π₂⊢ : [ id ] (P ∧T Q) ⊢ Q
π₂⊢ {P = P} {Q = Q} = record where
  realiser = `snd

  tracks {a = a} = elim! λ p q α pp qq → subst-∈ (Q _) qq $
    `snd ⋆ a               ≡⟨ ap (`snd ⋆_) α ⟩
    `snd ⋆ (`pair ⋆ p ⋆ q) ≡⟨ `snd-β (P _ .def pp) (Q _ .def qq) ⟩
    q                      ∎
```
