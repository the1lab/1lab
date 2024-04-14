open import 1Lab.Reflection.Signature
open import 1Lab.Reflection
open import 1Lab.Path
open import 1Lab.Type

module 1Lab.Reflection.Copattern where

-- Create a copattern clause for a field.
make-copattern-clause : List (Arg Term) → Term → Arg Name → TC Clause
make-copattern-clause params tm (arg field-info field-name) = do
  -- Infer the type of the field with all known arguments instantiated.
  field-tp ← infer-type (def field-name (map hide params ++ argN tm ∷ []))
  -- Agda will insert implicits when defining copatterns even
  -- with 'withExpandLast true', so we need to do implicit instantiation
  -- by hand.
  -- First, we strip off all leading implicits from the field type.
  let (implicit-tele , tp) = pi-impl-view field-tp

  -- Construct the pattern portion of the clause, making sure to bind
  -- all implicit variables.
  -- Note that copattern projections are always visible.
  let pat = arg (set-visibility visible field-info) (proj field-name) ∷ tel→pats 0 implicit-tele

  -- Construct the body of the clause, making sure to instantiate
  -- all implicit arguments.
  let body = def field-name (argN tm ∷ tel→args 0 implicit-tele)

  pure $ clause implicit-tele pat body


-- Make a top-level copattern binding for a record.
make-copattern : ∀ {ℓ} {A : Type ℓ} → Bool → Name → A → TC ⊤
make-copattern declare? def-name x = do
  -- Infer the type of the provided term, and ensure that it is a record type.
  tm ← quoteTC x
  def rec-name params ← infer-type tm
    where tp → typeError ("Expected an element of a record type, yet " ∷ termErr tm ∷ " has type " ∷ termErr tp ∷ [])

  -- Construct copattern clauses for each field.
  ctor , fields ← get-record-type rec-name
  clauses ← traverse (make-copattern-clause params tm) fields

  -- Define a copattern binding, and predeclare its type if required.
  case declare? of λ where
    true → declare (argN def-name) (def rec-name params)
    false → pure tt
  define-function def-name clauses

{-
Usage:
Write the following in a module:
>  unquoteDecl copat = declare-copattern copat thing-to-be-expanded

If you wish to give the binding a type annotation, you can also use

>  copat : Your-type
>  unquoteDecl copat = declare-copattern copat thing-to-be-expanded

All features of non-recursive records are supported, including instance
fields and fields with implicit arguments.
-}

declare-copattern : ∀ {ℓ} {A : Type ℓ} → Name → A → TC ⊤
declare-copattern = make-copattern true

define-copattern : ∀ {ℓ} {A : Type ℓ} → Name → A → TC ⊤
define-copattern = make-copattern false

-- Tests
private module Test where
  -- Record type that uses all interesting features.
  record Record {ℓ} (A : Type ℓ) : Type ℓ where
    no-eta-equality
    constructor mk
    field
      ⦃ c ⦄ : A
      { f } : A → A
      const : ∀ {x} → f x ≡ c

  -- Record created via a constructor.
  via-ctor : Record Nat
  via-ctor = mk ⦃ c = 0 ⦄ {f = λ _ → 0} refl

  -- Both macros work.
  unquoteDecl copat-decl-via-ctor = declare-copattern copat-decl-via-ctor via-ctor

  copat-def-via-ctor : Record Nat
  unquoteDef copat-def-via-ctor = define-copattern copat-def-via-ctor via-ctor

  -- Record created by a function.
  module _ (r : Record Nat) where
    open Record r
    via-function : Record Nat
    via-function .c = suc c
    via-function .f = suc ∘ f
    via-function .const = ap suc const

  -- Also works when applied to the result of a function.
  unquoteDecl copat-decl-via-function = declare-copattern copat-decl-via-function (via-function via-ctor)
