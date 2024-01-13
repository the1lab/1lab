open import 1Lab.Reflection hiding (reverse)
open import 1Lab.Type

open import Data.Dec.Base
open import Data.Fin.Base

module 1Lab.Reflection.Variables where

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
-- This returns a (already quoted) environment 'Vec A n',
-- which allows us to easily build up quoted
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
    variables : Term → Maybe Term

open Variables

private variable
  a b : Level
  A : Type a
  n : Nat

empty-vars : Variables A
empty-vars = mk-variables [] (λ _ → nothing)

private
  bind : Term → Term → (Term → Maybe Term) → Term → Maybe Term
  bind tm tm-var lookup tm' with lookup tm' | tm ≡? tm'
  ... | just tm'-var | _     = just tm'-var
  ... | nothing      | yes _ = just tm-var
  ... | nothing      | no _  = nothing

  fin-term : Nat → Term
  fin-term zero = con (quote fzero) (unknown h∷ [])
  fin-term (suc n) = con (quote fsuc) (unknown h∷ fin-term n v∷ [])

  env-rec : (Mot : Nat → Type b) →
          (∀ {n} → Mot n → A → Mot (suc n)) →
          Mot zero →
          Env A n → Mot n
  env-rec Mot _▷*_ []* []       = []*
  env-rec Mot _▷*_ []* (xs ▷ x) = env-rec (Mot ∘ suc) _▷*_ ([]* ▷* x) xs

  reverse : Env A n → Vec A n
  reverse {A = A} env = env-rec (Vec A) (λ xs x → x ∷ xs) [] env



-- Get the variable associated with a term, binding a new
-- one as need be. Note that this returns the variable
-- as a quoted term!
bind-var : Variables A → Term → TC (Term × Variables A)
bind-var vs tm with variables vs tm
... | just v = do
  pure (v , vs)
... | nothing = do
  a ← unquoteTC tm
  let v = fin-term (nvars vs)
  let vs' = mk-variables (bound vs ▷ a)
                         (bind tm v (variables vs))
  pure (v , vs')

environment : Variables A → TC (Term × Term)
environment vs = do
  env ← quoteTC (reverse (bound vs))
  size ← quoteTC (nvars vs)
  pure (size , env)
