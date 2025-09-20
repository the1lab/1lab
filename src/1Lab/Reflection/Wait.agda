open import 1Lab.Reflection
open import 1Lab.Type

module 1Lab.Reflection.Wait where

-- Generic tactic for deferring type checking of an argument until a
-- value is not blocked by a metavariable (under binders). Unfortunately
-- this incurs a performance overhead slightly more significant than
-- 'pure' blocking on the Agda compiler, since the value has to be
-- quoted for traversal.
--
-- Usage:
--
--   (a) Add a tactic argument {@(tactic locked-by v) l : Lock} to your function,
--       where 'v' is the value that you want to wait on.
--
--       Since this value will have to be quoted, it should be chosen to
--       minimize the size of the quoted representation.
--
--   (b) Wrap the arguments you want to wait on by 'Locked l'.
--
--   (c) Pattern match on the {l} argument to unblock the arguments.

data Lock : Type where lock : Lock

Locked : ∀ {ℓt} → Lock → Type ℓt → Type ℓt
Locked lock T = T

private
  bmu : Term → Maybe Blocker
  bmu (lam _ (abs _ t)) = bmu t
  bmu (pi _ (abs _ t))  = bmu t
  bmu t                 = blocking-meta t

locked-by : ∀ {ℓ} {A : Type ℓ} → A → Term → TC ⊤
locked-by {A = A} x goal = do
  `x ← quoteTC x
  case bmu `x of λ where
    (just m) → blockTC m
    nothing  → unify goal (con (quote lock) [])
