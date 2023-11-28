open import 1Lab.Reflection.Subst
open import 1Lab.Reflection
open import 1Lab.Path
open import 1Lab.Type

open import Data.String.Show

open import Meta.Append

module 1Lab.Reflection.Signature where

-- Look up a data type definition in the signature.
get-data-type : Name → TC (Nat × List Name)
get-data-type n = get-definition n >>= λ where
  (data-type pars cs) → pure (pars , cs)
  _ → typeError [ "get-data-type: definition " , nameErr n , " is not a data type." ]

-- Look up a record type definition in the signature.
get-record-type : Name → TC (Name × List (Arg Name))
get-record-type n = get-definition n >>= λ where
  (record-type conm fields) → pure (conm , fields)
  _ → typeError [ "get-record-type: definition " , nameErr n , " is not a record type." ]

-- Representation of a data/record constructor.
record Constructor : Type where
  constructor conhead
  field
    -- Name of the constructor itself:
    con-name      : Name

    -- Name of the data type:
    con-data      : Name

    -- Argument telescope for the constructor, with the datatype's
    -- parameters removed.
    con-arguments : Telescope

    -- Return type of the constructor.
    con-returns   : Term

  -- For the scoping of con-arguments and con-returns, we have
  --
  --    data D Δ : Type ... where
  --      c : Γ → D δ
  --
  --    becoming
  --
  --      c : ∀ {Δ} → Γ → D δ
  --
  --    in the signature. con-arguments is Δ ⊢ Γ, and con-returns is Δ, Γ ⊢ D δ.

get-type-constructors : Name → TC (List Constructor)
get-type-constructors n = datatype <|> recordtype where
  datatype = do
    (npars , cons) ← get-data-type n
    for cons λ qn → do
      (args , ty) ← pi-view <$> get-type qn
      pure (conhead qn n (drop npars args) ty)

  recordtype = do
    (c  , _)    ← get-record-type n
    (np , _)    ← pi-view <$> get-type n
    (args , ty) ← pi-view <$> get-type c
    pure ((conhead c n (drop (length np) args) ty) ∷ [])

-- Look up a constructor in the signature.
get-constructor : Name → TC Constructor
get-constructor n = get-definition n >>= λ where
  (data-cons t) → do
    (npars , cons) ← get-data-type t
    (args , ty)    ← pi-view <$> get-type n
    pure (conhead n t (drop npars args) ty)
  _ → typeError [ "get-constructor: " , nameErr n , " is not a data constructor." ]

-- If a term reduces to an application of a record type, return
-- information about that record.
get-record : Term → TC (Name × List (Arg Name))
get-record tm = reduce tm >>= λ where
  (def qn _) → get-record-type qn
  _          → typeError [ "get-record: " , termErr tm , " is not a record type." ]

-- Run a TC computation and reset the state after. If the returned value
-- makes references to metas generated in the reset computation, you'll
-- probably get __IMPOSSIBLE__s!
resetting : ∀ {ℓ} {A : Type ℓ} → TC A → TC A
resetting k = run-speculative ((_, false) <$> k)

telescope→patterns : Telescope → List (Arg Pattern)
telescope→patterns tel = go (length tel - 1) tel where
  go : Nat → Telescope → List (Arg Pattern)
  go n []                  = []
  go n ((_ , arg i _) ∷ t) = arg i (var n) ∷ go (n - 1) t

-- Get the argument telescope of something in the signature. NOTE: If
-- the Name refers to a Constructor, the returned telescope *will*
-- include the data/record parameters!
get-argument-tele : Name → TC Telescope
get-argument-tele qn = get-type qn <&> fst ∘ pi-view

record Has-constr {ℓ} (A : Type ℓ) : Type ℓ where
  field from-constr : Name → A

record Has-def {ℓ} (A : Type ℓ) : Type ℓ where
  field from-def : Name → A

instance
  Has-constr-Pattern : Has-constr Pattern
  Has-constr-Pattern = record { from-constr = con₀ }

  Has-constr-Term : Has-constr Term
  Has-constr-Term = record { from-constr = con₀ }

  Has-def-Term : Has-def Term
  Has-def-Term = record { from-def = def₀ }

  Has-constr-Name : Has-constr Name
  Has-constr-Name = record { from-constr = id }

  Has-def-Name : Has-def Name
  Has-def-Name = record { from-def = id }

macro
  -- Macro which turns a Name into its quoted Term/Pattern
  -- representation.
  --
  -- If the Name refers to a constructor, it's wrapped in con₀,
  -- otherwise it's wrapped in def₀
  --
  -- Since `it` is a macro, you can use this as `it Foo` rather than
  -- `def₀ (quote Foo)`.
  it : Name → Term → TC ⊤
  it n g = get-definition n >>= λ where
    (data-cons _) →
      unify g (def₀ (quote Has-constr.from-constr) ##ₙ def₀ (quote auto) ##ₙ lit (name n))
    _ →
      unify g (def₀ (quote Has-def.from-def) ##ₙ def₀ (quote auto) ##ₙ lit (name n))

  -- Macro which turns a *record name* into the quoted representation of
  -- its *constructor*, e.g. `constructor Σ` is `con₀ (quote _,_)`.
  `constructor : Name → Term → TC ⊤
  `constructor n g = do
    (c , _) ← get-record-type n
    unify g (it Has-constr.from-constr ##ₙ def₀ (quote auto) ##ₙ lit (name c))

_ : Path Term (`constructor Σ) (con₀ (quote _,_))
_ = refl

-- Check whether a name is defined.
is-defined : Name → TC Bool
is-defined nm = (resetting (true <$ get-type nm)) <|> pure false

-- Render a defined name as it would appear in the current scope.
--
-- This will be the "least qualified" possible concrete representation
-- for the given name, if one is available.
--
-- If the name is not defined, return the shown representation, which is
-- fully qualified.
render-name : Name → TC String
render-name def-nm = do
  d ← is-defined def-nm
  let
    fancy = formatErrorParts [ termErr (def₀ def-nm) ]
        <|> formatErrorParts [ termErr (con₀ def-nm) ]
    plain = show def-nm
  if d then fancy else pure plain

-- Generate a fresh name for a "helper function" to the given
-- definition.
-- Example: `helper-function-name (quote f) "foo"` will be `quote
-- f·foo`.
helper-function-name : Name → String → TC Name
helper-function-name def-nm suf = do
  t ← render-name def-nm
  freshName $ t <> "·" <> suf

-- Declare and optionally define a helper function for the given
-- definition; returns the generated name.
--
-- The helper is always defined with default visibility.
--
-- If the list of clauses is empty, the function will not be declared,
-- so it can be filled in later. This supports generating
-- mutually-recursive helpers.
helper-function : Name → String → Term → List Clause → TC Name
helper-function def-nm suf ty cls = do
  nm ← helper-function-name def-nm suf
  declare (argN nm) ty
  case cls of λ where
    [] → pure tt
    _  → define-function nm cls
  pure nm

private
  make-args : Nat → List (Arg Nat) → List (Arg Term)
  make-args n xs = reverse $ map (λ (arg ai i) → arg ai (var (n - i - 1) [])) xs

  class-for-param : Name → Nat → List (Arg Nat) → Term → Maybe Term
  class-for-param class n xs (agda-sort _) =
    just (def class (argN (var n (make-args n xs)) ∷ []))
  class-for-param class n xs (pi a (abs s b)) =
    pi (argH (Arg.unarg a)) ∘ abs s <$>
      class-for-param class (suc n) (arg (Arg.arg-info a) n ∷ xs) b
  class-for-param _ _ _ _ = nothing

  compute-telescope : Name → Nat → List (Arg Nat) → Telescope → Telescope → Telescope × List (Arg Term)
  compute-telescope d n xs is [] = reverse is , make-args (n + length is) xs
  compute-telescope d n xs is ((x , a) ∷ tel) =
    let
      narg = arg (Arg.arg-info a) n
      is'  = map (λ (s , arg ai t) → s , arg ai (raise 1 t)) is

      (tele , args) = case class-for-param d 0 [] (raise 1 (Arg.unarg a)) of λ where
        (just i) → compute-telescope d (1 + n) (narg ∷ xs) ((x , argI (raise (length is) i)) ∷ is') tel
        nothing  → compute-telescope d (1 + n) (narg ∷ xs) is' tel
    in ((x , argH (Arg.unarg a)) ∷ tele) , args

-- Given the name of a "class", and the name of a "data type", compute
-- the telescope, and arguments *of the data type*, for a "derived
-- instance" of that class. This is best demonstrated by example:
--
--   instance-telescope (quote Show) (quote Vec) =
--     ( {ℓ : Level} {A : Type ℓ} ⦃ _ : Show A ⦄ {n : Nat}
--     , [ ℓ , A , n ]
--     )
--
-- That is, all the parameters of the data type are bound invisibly, and
-- parameters that (end in) a type additionally have corresponding
-- instances of the class available.
instance-telescope : Name → Name → TC (Telescope × List (Arg Term))
instance-telescope class dat = do
  (tele , _) ← pi-view <$> get-type dat
  pure (compute-telescope class 0 [] [] tele)

-- Like `instance-telescope`, but instead return the complete pi-type of
-- the derived instance.
instance-type : Name → Name → TC Term
instance-type class dat = do
  (tel , vs) ← instance-telescope class dat
  pure $ unpi-view tel $ def class [ argN (def dat vs) ]
