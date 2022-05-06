module 1Lab.Reflection.Variables where

open import 1Lab.Type
open import Data.Nat.Base
open import Data.Fin.Base
open import 1Lab.Reflection

--------------------------------------------------------------------------------
-- Variable Binding for Terms
--
-- Many reflection tasks will require us to construct abstract
-- syntax trees representing reified expressions, which we will
-- use to construct a normal form. This works fine up until we
-- need to start finding normal forms for equational theories
-- with some sort of commutativity. For instance, which expression
-- should we prefer: 'x + y' or 'y + x'?
--
-- The first solution we may try here is to impose some ordering on
-- `Term`, and then sort our lists. However, trying to define this
-- ordering is complex, and it's not even clear if we /can/ impose
-- a meaningful ordering.
--
-- The next solution is to try and order the variables by the
-- time they are /introduced/, which is what this module aims to do.
-- We introduce a type 'Variables', which is intended to be an abstract
-- source of variable expressions. This allows us to produce fresh
-- (already quoted) variables of type 'Fin', which can be inserted
-- into the syntax tree while it's being constructed.
-- 
-- Once the syntax trees have been completed, we can grab an
-- environment using the aptly named 'environment' function.
-- This returns a (already quoted) environment function
-- 'Fin n → A', which allows us to easily build up quoted
-- calls to our normalization functions rather easily.

-- We 🛐 the wisdom that reversing a list/vector is a type
-- error!
data Env {ℓ} (A : Type ℓ) : Nat → Type ℓ where
  [] : Env A zero
  _▷_ : ∀ {n} → Env A n → A → Env A (suc n)

record Variables {a} (A : Type a) : Type a where
  constructor mk-variables
  field
    {nvars} : Nat
    -- We store the bindings in reverse order so that it's
    -- cheap to add a new one.
    bound : Env A nvars
    variables : Term → Maybe (Fin nvars)

open Variables

private variable
  a : Level
  A : Type
  n : Nat

empty-vars : Variables A
empty-vars = mk-variables [] (λ _ → nothing)

private
  bind : Term → (Term → Maybe (Fin n)) → Term → Maybe (Fin (suc n))
  bind {n = n} tm lookup tm′ with lookup tm′ | tm term=? tm′
  ... | just ‵var | _ = just (weaken ‵var)
  ... | nothing   | true = just (from-nat n)
  ... | nothing   | false = nothing

  fin-term : Nat → Term
  fin-term zero = con (quote fzero) (unknown h∷ [])
  fin-term (suc n) = con (quote fsuc) (unknown h∷ fin-term n v∷ [])

-- Get the variable associated with a term, binding a new
-- one as need be. Note that this returns the variable
-- as a quoted term!
bind-var : Variables A → Term → TC (Term × Variables A)
bind-var vs tm with variables vs tm
... | just lvl = do
  v ← quoteTC lvl
  returnTC (v , vs)
... | nothing = do
  a ← unquoteTC tm
  let v = fin-term (nvars vs)
  let vs′ = mk-variables (bound vs ▷ a)
                         (bind tm (variables vs))
  returnTC (v , vs′) 

lookup : Env A n → Fin n → A
lookup (env ▷ x) fzero = x
lookup (env ▷ x) (fsuc i) = lookup env i

environment : Variables A → TC Term
environment vs =
  quoteTC (lookup (bound vs) ∘ opposite)
