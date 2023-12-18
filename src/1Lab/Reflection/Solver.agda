module 1Lab.Reflection.Solver where

open import 1Lab.Prelude
open import 1Lab.Reflection
open import 1Lab.Reflection.Variables

open import Data.List.Base

private variable
  ℓ : Level
  A : Type ℓ

--------------------------------------------------------------------------------
-- Helpers

solver-failed : Term → Term → TC A
solver-failed lhs rhs =
    typeError (strErr "Could not equate the following expressions:\n  " ∷
                 termErr lhs ∷
               strErr "\nAnd\n  " ∷
                 termErr rhs ∷ [])

print-repr : Term → Term → TC A
print-repr tm repr =
  typeError $ strErr "The expression\n  " ∷
                termErr tm ∷
              strErr "\nIs represented by the expression\n  " ∷
                termErr repr ∷ []

print-var-repr : Term → Term → Term → TC A
print-var-repr tm repr env =
  typeError $ strErr "The expression\n  " ∷
                termErr tm ∷
              strErr "\nIs represented by the expression\n  " ∷
                termErr repr ∷
              strErr "\nIn the environment\n  " ∷
                termErr env ∷ []

--------------------------------------------------------------------------------
-- Simple Solvers

record SimpleSolver : Type where
  constructor simple-solver
  field
    dont-reduce : List Name
    build-expr : Term → TC Term
    invoke-solver : Term → Term → Term
    invoke-normaliser : Term → Term

module _ (solver : SimpleSolver) where
  open SimpleSolver solver

  mk-simple-solver : Term → TC ⊤
  mk-simple-solver hole =
    withNormalisation false $
    withReduceDefs (false , dont-reduce) $ do
    goal ← infer-type hole >>= reduce
    just (lhs , rhs) ← get-boundary goal
      where nothing → typeError $ strErr "Can't determine boundary: " ∷
                                  termErr goal ∷ []
    elhs ← normalise lhs >>= build-expr
    erhs ← normalise rhs >>= build-expr
    (noConstraints $ unify hole (invoke-solver elhs erhs)) <|> solver-failed elhs erhs

  mk-simple-normalise : Term → Term → TC ⊤
  mk-simple-normalise tm hole =
    withNormalisation false $
    withReduceDefs (false , dont-reduce) $ do
    e ← normalise tm >>= build-expr
    unify hole (invoke-normaliser e)

  mk-simple-repr : Term → TC ⊤
  mk-simple-repr tm =
    withNormalisation false $
    withReduceDefs (false , dont-reduce) $ do
    repr ← normalise tm >>= build-expr
    print-repr tm repr

--------------------------------------------------------------------------------
-- Solvers with Variables

record VariableSolver {ℓ} (A : Type ℓ) : Type ℓ where
  constructor var-solver
  field
    dont-reduce : List Name
    build-expr : Variables A → Term → TC (Term × Variables A)
    invoke-solver : Term → Term → Term → Term
    invoke-normaliser : Term → Term → Term

module _ {ℓ} {A : Type ℓ} (solver : VariableSolver A) where
  open VariableSolver solver

  mk-var-solver : Term → TC ⊤
  mk-var-solver hole =
    withNormalisation false $
    withReduceDefs (false , dont-reduce) $ do
    goal ← infer-type hole >>= reduce
    just (lhs , rhs) ← get-boundary goal
      where nothing → typeError $ strErr "Can't determine boundary: " ∷
                                  termErr goal ∷ []
    elhs , vs ← normalise lhs >>= build-expr empty-vars
    erhs , vs ← normalise rhs >>= build-expr vs
    size , env ← environment vs
    (noConstraints $ unify hole (invoke-solver elhs erhs env)) <|>
      typeError (strErr "Could not equate the following expressions:\n  " ∷
                   termErr elhs ∷
                 strErr "\nAnd\n  " ∷
                   termErr erhs ∷ [])

  mk-var-normalise : Term → Term → TC ⊤
  mk-var-normalise tm hole =
    withNormalisation false $
    withReduceDefs (false , dont-reduce) $ do
    e , vs ← normalise tm >>= build-expr empty-vars
    size , env ← environment vs
    soln ← reduce (invoke-normaliser e env)
    unify hole soln

  mk-var-repr : Term → TC ⊤
  mk-var-repr tm =
    withNormalisation false $
    withReduceDefs (false , dont-reduce) $ do
    repr , vs ← normalise tm >>= build-expr empty-vars
    size , env ← environment vs
    print-var-repr tm repr env
