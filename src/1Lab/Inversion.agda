open import 1Lab.Type

module 1Lab.Inversion where

{-
Automation for inversion
=============================

Morally, the 'Inversion' typeclass equips a type 'A' with a canonical inversion
lemma that associates a list of types 'Hyps' to 'A', along with a
function 'invert : A → Hyps'. Note that Every type has a default 'Inversion'
instance that associates the empty list of types '[]'.

These instances are used to drive the auxillary 'Inversion*' typeclass.
'Inversion*' is parameterised by a list of types 'Hyps' and a type 'Goal',
and attempts to produce produce a function 'Hyps → Goal' by performing
the following actions:
- If 'Goal' is the first element of 'Hyps', then the search terminates,
and produces the projection 'fst : Goal × Hypotheses → Goal'
- Otherwise, we resolve the 'Inversion' instance 'i' associated to the head
of the list, add 'i .Hyps' to the back of the list of hypotheses, drop the head,
and continue the search.

Inversion instances
-------------------

For technical reasons, there are 3 types of inversion instances:
- 'inversion' instances: These destructure a type 'A' into a list of
hypotheses, and place these hypotheses on the back of the search queue.
- 'contradiction' instances: These derive '⊥' from 'A', and will immediately
conclude the search with 'absurd'.
- 'structural' instances: These are like 'inversion' instances, but
they place the hypotheses on the *front* of the queue rather than the
back. This allows us to optimize for types like 'Lift ⊥', which occur
pretty commonly.

Typically, users should only write 'inversion' and 'contradiction' instances.
Moreover, 'inversion' instances should never create cycles: if an
inversion instance for 'A' ends up somehow placing 'A' onto the
queue as a hypothesis, then we will run into an infinite loop.

Entry points
------------

- 'inversion : A → B':
  Performs a search for a chain of inversion lemmas that yield 'A → B'
- 'inversion-with : (Hyps : Hypotheses) → hypotheses Hyps → A → B':
  Perform a search for a chain of inversion lemmas, starting with
  a list of extra hypotheses 'hyps'.

Limitations
-------------
We only allow lists of inversion hypotheses, not telescopes. This makes
it much easier to do BFS rather than DFS.

We also use lists as queue, which is sub-optimal. A better option would
be a batched queue, but this makes managing the queue a bit more difficult.
Moreover, most inversion searches will not be particularly deep, so we
expect that this will not be an issue in practice.
-}

-- Lists of inversion hypotheses.
data Hypotheses : Typeω where
  [] : Hypotheses
  _∷_ : ∀ {ℓ} → Type ℓ → Hypotheses → Hypotheses

infixr 20 _∷_

private
  level-of-hypotheses : Hypotheses → Level
  level-of-hypotheses [] = lzero
  level-of-hypotheses (H ∷ Hs) = level-of H ⊔ level-of-hypotheses Hs

  -- We special case the singleton list of hypotheses to make writing instances nicer.
  hypotheses : (Hs : Hypotheses) → Type (level-of-hypotheses Hs)
  hypotheses [] = ⊤
  hypotheses (H ∷ []) = H
  hypotheses (H₁ ∷ (H₂ ∷ Hs)) = H₁ × hypotheses (H₂ ∷ Hs)

  _++_ : Hypotheses → Hypotheses → Hypotheses
  [] ++ Hs₂ = Hs₂
  (H ∷ Hs₁) ++ Hs₂ = H ∷ (Hs₁ ++ Hs₂)

  head : ∀ {ℓ} {H : Type ℓ} (Hyps : Hypotheses) → hypotheses (H ∷ Hyps) → H
  head [] h = h
  head (H ∷ Hs) (h , _) = h

  tail : ∀ {ℓ} {H : Type ℓ} (Hyps : Hypotheses) → hypotheses (H ∷ Hyps) → hypotheses Hyps
  tail [] h = tt
  tail (H ∷ Hs) (_ , hs) = hs

  hypotheses-++
    : ∀ (Hs₁ Hs₂ : Hypotheses) → hypotheses Hs₁ → hypotheses Hs₂ → hypotheses (Hs₁ ++ Hs₂)
  hypotheses-++ [] Hs₂ hs₁ hs₂ = hs₂
  hypotheses-++ (H ∷ []) [] hs₁ hs₂ = hs₁
  hypotheses-++ (H₁ ∷ []) (H₂ ∷ Hs₂) hs₁ hs₂ = hs₁ , hs₂
  hypotheses-++ (H₁ ∷ (H₂ ∷ Hs₁)) Hs₂ (h₁ , hs₁) hs₂ = h₁ , hypotheses-++ (H₂ ∷ Hs₁) Hs₂ hs₁ hs₂

-- Users of 'Inversion' should implement this typeclass.
data Inversion {ℓ} (A : Type ℓ) : Typeω where
  by-inversion : (Hyps : Hypotheses) → (A → hypotheses Hyps) → Inversion A
  by-contradiction : (A → ⊥) → Inversion A
  by-structural : (Hyps : Hypotheses) → (A → hypotheses Hyps) → Inversion A

with-inversion-hypotheses : ∀ {ℓ ℓ'} {A : Type ℓ} → Inversion A → Type ℓ' → Hypotheses → Hypotheses
with-inversion-hypotheses (by-inversion Inv x) Goal Hyps = Hyps ++ Inv
with-inversion-hypotheses (by-contradiction x) Goal Hyps = Goal ∷ []
with-inversion-hypotheses (by-structural Inv x) Goal Hyps = Inv ++ Hyps

-- Auxillary typeclass for driving search.
-- Users should never implement this typeclass themselves.
record Inversion* {ℓ} (Hyps  : Hypotheses) (Goal : Type ℓ) : Typeω where
  field
    inversion* : hypotheses Hyps → Goal

open Inversion*

instance
  -- Default 'Inversion' instance that adds no extra by-inversion hypotheses.
  Inversion-Default
    : ∀ {ℓ} {A : Type ℓ}
    → Inversion A
  Inversion-Default = by-inversion [] (λ _ → tt)
  {-# INCOHERENT Inversion-Default #-}

  -- Stop performing search if we've found our goal.
  Inversion*-Select
    : ∀ {ℓ} {Hyps : Hypotheses} {Goal : Type ℓ}
    → Inversion* (Goal ∷ Hyps) Goal
  Inversion*-Select {Hyps = []} .inversion* g = g
  Inversion*-Select {Hyps = H ∷ Hyps} .inversion* (g , _) = g

  -- Fallback instance for when we didn't find the goal.
  Inversion*-Push
    : ∀ {ℓ ℓ'} {Hyps : Hypotheses} {H : Type ℓ} {Goal : Type ℓ'}
    → ⦃ i : Inversion H ⦄
    → ⦃ i* : Inversion* (with-inversion-hypotheses i Goal Hyps) Goal ⦄
    → Inversion* (H ∷ Hyps) Goal
  Inversion*-Push {Hyps = Hyps} ⦃ by-inversion Inv inv ⦄ ⦃ i* ⦄ .inversion* hs =
    i* .inversion* (hypotheses-++ Hyps Inv (tail Hyps hs) (inv (head Hyps hs)))
  Inversion*-Push {Hyps = Hyps} ⦃ by-contradiction ¬h ⦄ ⦃ i* ⦄ .inversion* hs =
    absurd (¬h (head Hyps hs))
  Inversion*-Push {Hyps = Hyps} ⦃ by-structural Inv inv ⦄ ⦃ i* ⦄ .inversion* hs =
    i* .inversion* (hypotheses-++ Inv Hyps (inv (head Hyps hs)) (tail Hyps hs))
  {-# INCOHERENT Inversion*-Push #-}


{-
Useful inversion rules
======================

By default, we add structural rules for 'A × B' and 'Lift', and also
a contradiction rule for '⊥'.
-}

instance
  Inversion-⊥ : Inversion ⊥
  Inversion-⊥ = by-contradiction id

  Inversion-× : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → Inversion (A × B)
  Inversion-× {A = A} {B = B} = by-structural (A ∷ B ∷ []) id
  {-# OVERLAPPABLE Inversion-× #-}

  Inversion-Lift : ∀ {ℓ ℓ'} {A : Type ℓ} → Inversion (Lift ℓ' A)
  Inversion-Lift {A = A} = by-structural (A ∷ []) Lift.lower
  {-# OVERLAPPABLE Inversion-Lift #-}

{-
Entrypoints
===========
-}

inversion-with
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → (Hyps : Hypotheses)
  → hypotheses Hyps
  → ⦃ _ : Inversion* (A ∷ Hyps) B ⦄
  → A → B
inversion-with [] hs ⦃ i* ⦄ a = i* .inversion* a
inversion-with (H ∷ Hyps) hs ⦃ i* ⦄ a = i* .inversion* (a , hs)

inversion
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → ⦃ _ : Inversion* (A ∷ []) B ⦄
  → A → B
inversion = inversion-with [] tt
