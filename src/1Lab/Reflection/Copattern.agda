open import 1Lab.Reflection.Signature
open import 1Lab.Reflection.Subst
open import 1Lab.Reflection
open import 1Lab.Path
open import 1Lab.Type

module 1Lab.Reflection.Copattern where

--------------------------------------------------------------------------------
-- Macros for manipulating copattern definitions.

-- Make a top-level copattern binding for an existing record.
make-copattern : Bool → Name → Term → Term → TC ⊤
make-copattern declare? def-name tm tp = do
  -- Ensure that codomain is a record type.
  let tele , cod-tp = pi-view tp
  def rec-name params ← pure cod-tp
    where _ → typeError [ "make-copattern: codomain of " , termErr tp , " is not a record type." ]

  let inst-tm = apply-tm* tm (tel→args 0 tele)

  -- Construct copattern clauses for each field.
  ctor , fields ← get-record-type rec-name
  clauses ←
    in-context (reverse tele) $
    for fields λ  (arg field-info field-name) → do
      -- Infer the type of the field with all known arguments instantiated.
      field-tp ← infer-type (def field-name (argN inst-tm ∷ []))

      -- Agda will insert implicits when defining copatterns even
      -- with 'withExpandLast true', so we need to do implicit instantiation
      -- by hand. First, we strip off all leading implicits from the field type.
      let (implicit-tele , tp) = pi-impl-view field-tp
      let nimplicits = length implicit-tele
      let clause-tele = tele ++ implicit-tele

      -- Construct the pattern portion of the clause, making sure to bind
      -- all implicit variables. Note that copattern projections are always visible.
      let pat =
            tel→pats nimplicits tele ++
            arg (set-visibility visible field-info) (proj field-name) ∷
            tel→pats 0 implicit-tele

      -- Construct the body of the clause, making sure to apply all arguments
      -- bound outside the copattern match, and instantiate all implicit arguments.
      -- We also need to apply all of the implicit arguments to 'tm'.
      body ←
        in-context (reverse clause-tele) $
        reduce (def field-name (argN (raise nimplicits inst-tm) ∷ tel→args 0 implicit-tele))

      -- Construct the final clause.
      pure $ clause clause-tele pat body

  -- Define a copattern binding, and predeclare its type if required.
  case declare? of λ where
    true → declare (argN def-name) tp
    false → pure tt

  -- Construct the final copattern.
  define-function def-name clauses

-- Repack a record type.
-- Will also accept functions into record types like `A → Record`,
-- and will perform a pointwise repacking.
repack-record : Term → Term → TC Term
repack-record tm tp = do
  -- Ensure that codomain is a record type.
  tele , cod-tp ← pi-view <$> reduce tp
  def rec-name params ← pure cod-tp
    where _ → typeError [ "repack-record: codomain of " , termErr tp , " is not a record type." ]

  -- Instantiate the term with all telescope arguments to saturate it.
  let inst-tm = apply-tm* tm (tel→args 0 tele)

  -- Construct fields for each projection.
  ctor , fields ← get-record-type rec-name
  args ←
    in-context (reverse tele) $
    for fields λ (arg field-info field-name) →
      argN <$> reduce (def field-name (argN inst-tm ∷ []))

  -- Builld a pointwise repacking.
  pure (tel→lam tele (con ctor args))

--------------------------------------------------------------------------------
-- Usage

{-
Write the following in a module:
>  unquoteDecl copat = declare-copattern copat thing-to-be-expanded

If you wish to give the binding a type annotation, you can also use

>  copat : Your-type
>  unquoteDecl copat = declare-copattern copat thing-to-be-expanded

All features of non-recursive records are supported, including instance
fields and fields with implicit arguments.

These macros also allow you to lift functions 'A → some-record-type'
into copattern definitions. Note that Agda will generate meta for
implicits before performing quotation, so we need to explicitly
bind all implicits using a lambda before quotation!
-}

declare-copattern : ∀ {ℓ} {A : Type ℓ} → Name → A → TC ⊤
declare-copattern {A = A} nm x = do
  `x ← quoteTC x
  `A ← quoteTC A
  make-copattern true nm `x `A

define-copattern : ∀ {ℓ} {A : Type ℓ} → Name → A → TC ⊤
define-copattern {A = A} nm x = do
  `x ← quoteTC x
  `A ← quoteTC A
  make-copattern false nm `x `A

{-
There is a slight caveat with level-polymorphic defintions, as
they cannot be quoted into any `Type ℓ`. With this in mind,
we also provide a pair of macros that work over `Typeω` instead.
-}

declare-copattern-levels : ∀ {U : Typeω} → Name → U → TC ⊤
declare-copattern-levels nm A = do
  `A ← quoteωTC A
  -- Cannot quote things in type Typeω, but we can infer their type.
  `U ← infer-type `A
  make-copattern true nm `A `U

define-copattern-levels : ∀ {U : Typeω} → Name → U → TC ⊤
define-copattern-levels nm A = do
  `A ← quoteωTC A
  -- Cannot quote things in type Typeω, but we can infer their type.
  `U ← infer-type `A
  make-copattern false nm `A `U

{-
Another common pattern is that two records `r : R p` and `s : R q` may contain
the same data, but they are parameterized by different values.
The `define-eta-expansion` macro will automatically construct a function
`R p → R q` that eta-expands the first record out into a copattern definition.
-}

make-eta-expansion : Name → Maybe Name → TC Term → TC ⊤
make-eta-expansion nm lemma? make-tp = do
  tp ← make-tp
  -- Get the type of the predeclared binding.
  -- Next, grab the telescope, and use it to construct a function
  -- that simply returns the last argument with the provided
  -- lemma applied.
  let tele , _ = pi-view tp
  let tm = case lemma? of λ where
    (just lemma) → tel→lam tele (def lemma (argN (var 0 []) ∷ []))
    nothing → tel→lam tele (var 0 [])
  make-copattern false nm tm tp

define-eta-expansion : Name → TC ⊤
define-eta-expansion nm = do
  tp ← reduce =<< infer-type (def nm [])
  let tele , _ = pi-view tp
  let tm = tel→lam tele (var 0 [])
  make-copattern false nm tm tp

--------------------------------------------------------------------------------
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

  -- Test to see how we handle unused parameters.
  record Unused (n : Nat) : Type where
    field
      actual : Nat

  zero-unused-param : Unused 0
  zero-unused-param = record { actual = 0 }

  one-unused-param : ∀ {n} → Unused n
  unquoteDef one-unused-param = define-copattern one-unused-param zero-unused-param

  -- Functions into records that are universe polymorphic
  neat : ∀ {ℓ} {A : Type ℓ} → A → Record A
  neat a .Record.c = a
  neat a .Record.f _ = a
  neat a .Record.const = refl

  cool : ∀ {ℓ} {A : Type ℓ} → A → Record A
  unquoteDef cool = define-copattern-levels cool λ {ℓ} {A : Type ℓ} → neat

  -- Eta-expanders
  expander : ∀ {m n : Nat} → Unused m → Unused n
  unquoteDef expander = define-eta-expansion expander
