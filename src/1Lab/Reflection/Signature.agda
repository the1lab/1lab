open import 1Lab.Reflection.Subst
open import 1Lab.Reflection
open import 1Lab.Path
open import 1Lab.Type

open import Data.String.Show

open import Meta.Append

module 1Lab.Reflection.Signature where

get-data-type : Name → TC (Nat × List Name)
get-data-type n = get-definition n >>= λ where
  (data-type pars cs) → pure (pars , cs)
  _ → typeError [ "get-data-type: definition " , nameErr n , " is not a data type." ]

get-record-type : Name → TC (Name × List (Arg Name))
get-record-type n = get-definition n >>= λ where
  (record-type conm fields) → pure (conm , fields)
  _ → typeError [ "get-record-type: definition " , nameErr n , " is not a record type." ]

record Constructor : Type where
  constructor conhead
  field
    con-name      : Name
    con-data      : Name
    con-arguments : Telescope
    con-returns   : Term

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

get-constructor : Name → TC Constructor
get-constructor n = get-definition n >>= λ where
  (data-cons t) → do
    (npars , cons) ← get-data-type t
    (args , ty)    ← pi-view <$> get-type n
    pure (conhead n t (drop npars args) ty)
  _ → typeError [ "get-constructor: " , nameErr n , " is not a data constructor." ]

get-record : Term → TC (Name × List (Arg Name))
get-record tm = reduce tm >>= λ where
  (def qn _) → get-record-type qn
  _          → typeError [ "get-record: " , termErr tm , " is not a record type." ]

resetting : ∀ {ℓ} {A : Type ℓ} → TC A → TC A
resetting k = run-speculative ((_, false) <$> k)

telescope→patterns : Telescope → List (Arg Pattern)
telescope→patterns tel = go (length tel - 1) tel where
  go : Nat → Telescope → List (Arg Pattern)
  go n []                  = []
  go n ((_ , arg i _) ∷ t) = arg i (var n) ∷ go (n - 1) t

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
  it : Name → Term → TC ⊤
  it n g = get-definition n >>= λ where
    (data-cons _) →
      unify g (def₀ (quote Has-constr.from-constr) ##ₙ def₀ (quote auto) ##ₙ lit (name n))
    _ →
      unify g (def₀ (quote Has-def.from-def) ##ₙ def₀ (quote auto) ##ₙ lit (name n))

  `constructor : Name → Term → TC ⊤
  `constructor n g = do
    (c , _) ← get-record-type n
    unify g (it Has-constr.from-constr ##ₙ def₀ (quote auto) ##ₙ lit (name c))

is-defined : Name → TC Bool
is-defined nm =
  (run-speculative do
    _ ← get-type nm
    pure (true , false))
  <|> pure false

helper-function-name : Name → String → TC Name
helper-function-name def-nm suf = do
  d ← is-defined def-nm
  let
    fancy = formatErrorParts [ termErr (def₀ def-nm) ]
        <|> formatErrorParts [ termErr (con₀ def-nm) ]
    plain = show def-nm
  t ← if d then fancy else pure plain
  freshName $ t <> "·" <> suf

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

instance-telescope : Name → Name → TC (Telescope × List (Arg Term))
instance-telescope class dat = do
  (tele , _) ← pi-view <$> get-type dat
  pure (compute-telescope class 0 [] [] tele)

instance-type : Name → Name → TC Term
instance-type class dat = do
  (tel , vs) ← instance-telescope class dat
  pure $ unpi-view tel $ def class [ argN (def dat vs) ]
