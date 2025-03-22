open import 1Lab.Reflection.Signature
open import 1Lab.Reflection.Subst
open import 1Lab.Reflection
open import 1Lab.Type.Sigma
open import 1Lab.Type.Pi
open import 1Lab.HLevel
open import 1Lab.Path
open import 1Lab.Type

open import Data.Nat.Base

open import Meta.Append

module 1Lab.Reflection.Induction where

-- H-Level instances must be in scope for the macro to work properly
open import 1Lab.HLevel.Closure public

open import Data.Maybe.Base using (nothing; just) public

{-
A macro for generating induction principles for (higher, indexed) inductive types.

We support inductive types in the form presented in "Pattern Matching Without K"
by Cockx et al, section 3.1, with the addition of higher inductive types.
Reusing the terminology from that paper, the idea is to translate the constructors
of a data type into corresponding *methods* along with spines that tell us how to
apply them to build the eliminator's clauses.

When generating an eliminator into (n-2)-types, we automatically omit the methods that
follow from h-level (i.e. those corresponding to constructors with at least n
nested `PathP`s).

Due to limitations of the reflection interface, path constructors between composites
are not supported.

See 1Lab.Reflection.Induction.Examples for examples.
-}

pi-view-path : Term → Telescope
pi-view-path (pi x (abs n y)) = (n , x) ∷ pi-view-path y
pi-view-path (def (quote PathP) (_ h∷ lam _ (abs n y) v∷ _ v∷ _ v∷ [])) =
  (n , argN (quoteTerm I)) ∷ pi-view-path y
pi-view-path _ = []

Replacements = List (Term × Term)

subst-replacements : Subst → Replacements → Replacements
subst-replacements s = map (×-map (applyS s) (applyS s))

instance
  Has-subst-Replacements : Has-subst Replacements
  Has-subst-Replacements = record { applyS = subst-replacements }

record Elim-options : Type where
  field
    -- Whether to generate an induction principle or a recursion principle.
    -- (P : D → Type ℓ) vs (P : Type ℓ)
    induction : Bool

    -- If `just n`, assume the motive has hlevel n and omit methods accordingly.
    into-hlevel : Maybe Nat

    -- Hide the motive argument in the eliminator's type?
    -- (P : D → Type ℓ) vs. {P : D → Type ℓ}
    hide-motive : Bool

    -- Hide the indices in the motive's type?
    -- (P : (is : Ξ) → D is → Type ℓ) vs. (P : {is : Ξ} → D is → Type ℓ)
    hide-indices : Bool

    -- Hide non-inductive hypotheses in method types?
    -- (Psup : (x : A) (f : B x → W A B) (Pf : ∀ b → P (f b)) → P (sup x f))
    -- vs.
    -- (Psup : {x : A} {f : B x → W A B} (Pf : ∀ b → P (f b)) → P (sup x f))
    -- Arguments hidden in the constructor's type are always hidden.
    hide-cons-args : Bool

private
 module Induction
  (opts : Elim-options)
  (D : Name) (pars : Nat) (ixTel : Telescope) (cs : List Name)
  where

  open Elim-options opts

  -- Given a term c : T, produce a replacement c↑ : T↑ (see below).
  -- The Replacements argument maps constructors and variables to their
  -- lifted version.
  {-# TERMINATING #-}
  replace : Replacements → Term → Maybe Term
  replace* : Replacements → Args → Args

  lookupR : Term → Replacements → Maybe Term
  lookupR t [] = nothing
  lookupR t@(con c _) ((con c' _ , r) ∷ rs) with c ≡? c'
  ... | yes _ = just r
  ... | no  _ = lookupR t rs
  lookupR t@(var i _) ((var i' _ , r) ∷ rs) with i ≡? i'
  ... | yes _ = just r
  ... | no  _ = lookupR t rs
  lookupR t (_ ∷ rs) = lookupR t rs

  replace rs (lam v (abs n t)) = lam v ∘ abs n <$> replace (raise 1 rs) t
  replace rs t@(con c args) = lookupR t rs <&> λ r →
    apply-tm* r (replace* rs (drop pars args))
  replace rs t@(var i args) = lookupR t rs <&> λ r →
    apply-tm* r (replace* rs args)
  replace rs _ = nothing

  replace* rs [] = []
  replace* rs (arg ai t ∷ as) with replace rs t
  ... | just t' = hide-if hide-cons-args (arg ai t) ∷ arg ai t' ∷ replace* rs as
  ... | nothing = arg ai t ∷ replace* rs as

  {-
  The main part of the algorithm: computes the method associated to a constructor.

  In detail, given
    a motive `P : (is : Ξ) → D ps is → Type ℓ`
    a term `c : T = Δ → D ps is`
  produces
    the "lifted" type `T↑ = Δ↑ → P is (c ρ)`
      where `Δ↑ ⊢ ρ : Δ` is an embedding
      where types of the form `S = Φ → D ps is` in Δ are replaced recursively with `{S}, S↑` in Δ↑
      (this only occurs with a recursion depth of 1 due to strict positivity)
    and a spine α such that
      rec : Π P, Δ ⊢ α : Δ↑
      where Π P = (is : Ξ) → (d : D ps is) → P is d
  or nothing if T doesn't end in `D ps`.

  Example: W A B
    sup : (a : A) (f : B a → W A B) → W A B
      f : B a → W A B
      display f = ((b : B a) → P (f b))
                , (_ : Π P, b : B a ⊢ b : B a)
    display sup = ((a : A) {f : B a → W A B} (pf : ∀ b → P (f b)) → P (sup a f))
                , (rec : Π P, a : A, f : B a → W A B ⊢ a, {f}, (λ b → rec (f b)))
  -}
  {-# TERMINATING #-}
  display
    : (depth : Nat)
    → (ps : Args) -- D's parameters
    → (P : Term)
    → (rs : Replacements) -- a list of replacements from terms to their lifted version,
                          -- used for correcting path boundaries
    → (rec : Term) -- a variable for explicit recursion
    → (α : Args) -- accumulator for the spine
    → (c : Term) (T : Term)
    → Maybe (Term × Args) -- (T↑ , α)
  display depth ps P rs rec α c (pi (arg ai x) (abs n y)) = do
    let
      ps = raise 1 ps
      P = raise 1 P
      rs = raise 1 rs
      rec = raise 1 rec
      α = raise 1 α
      c = raise 1 c
      base =
        let
          c = c <#> arg ai (var 0 [])
          α = α ∷r hide-if hide-cons-args (arg ai (var 0 []))
        in display depth ps P rs rec α c y <&> ×-map₁ λ y →
          pi (hide-if hide-cons-args (arg ai x)) (abs n y)
    suc depth-1 ← pure depth
      where _ → base
    just (h , α') ← pure (display depth-1 ps P rs unknown [] (var 0 []) (raise 1 x))
      where _ → base
    let
      ps = raise 1 ps
      P = raise 1 P
      rs = (var 1 [] , var 0 []) ∷ raise 1 rs
      c = raise 1 c <#> arg ai (var 1 [])
      hTel = pi-view-path h
      l = tel→lam hTel (apply-tm* (raise (length hTel) rec)
        (infer-tel ixTel ∷r argN (var (length hTel) α')))
      α = α ++ [ hide-if hide-cons-args (arg ai (var 0 [])) , argN l ]
      y = raise 1 y
    display depth ps P rs rec α c y <&> ×-map₁ λ y →
      pi (hide-if hide-cons-args (arg ai x)) (abs n (pi (argN h) (abs ("P" <> n) y)))
  display depth ps P rs rec α c (def (quote PathP) (_ h∷ lam v (abs n y) v∷ l v∷ r v∷ [])) = do
    l ← replace rs l
    r ← replace rs r
    let
      ps = raise 1 ps
      P = raise 1 P
      rs = raise 1 rs
      rec = raise 1 rec
      α = raise 1 α ∷r argN (var 0 [])
      c = raise 1 c <#> argN (var 0 [])
    display depth ps P rs rec α c y <&> ×-map₁ λ y →
      def (quote PathP) (unknown h∷ lam v (abs n y) v∷ l v∷ r v∷ [])
  display depth ps P rs rec α c (def D' args) = do
    yes _ ← pure (D ≡? D')
      where _ → nothing
    let ps' , is = split-at pars args
    yes _ ← pure (ps ≡? ps')
      where _ → nothing
    let Pc = apply-tm* P (if induction then hide-if hide-indices is ++ c v∷ [] else [])
    pure (Pc , α)
  display depth ps P rs rec α c _ = nothing

  try-hlevel : Term → TC (Maybe Term)
  try-hlevel T =
    (do
      maybe→alt into-hlevel
      m ← new-meta T
      unify m $ def (quote centre) $
        def (quote hlevel) (unknown h∷ T h∷ lit (nat 0) v∷ []) v∷ []
      pure (just m))
    <|> pure nothing

  ×-map₁₂ : ∀ {A B C : Type} → (A → A) → (B → B) → A × B × C → A × B × C
  ×-map₁₂ f g (a , b , c) = (f a , g b , c)

  -- Loop over D's constructors and build the method telescope, constructor
  -- replacements and spines to apply them to.
  methods : Args → Term → TC (Telescope × List Args × Replacements)
  methods ps P = go ps P [] cs where
    go : Args → Term → Replacements → List Name → TC _
    go ps P rs [] = pure ([] , [] , rs)
    go ps P rs (c ∷ cs) = do
      let c' = con c (hide ps)
      cT ← flip pi-applyTC ps =<< normalise =<< get-type c
      just (methodT , α) ← pure (display 1 ps P rs (var 0 []) [] c' cT)
        where _ → typeError [ "The type of constructor " , nameErr c , " is not supported" ]
      try-hlevel methodT >>= λ where
        (just m) → do
          -- The type of the method is solvable by hlevel (i.e. contractible):
          -- we can omit that type from the telescope and replace the method with
          -- a call to `hlevel 0 .centre`.
          let rs = (c' , m) ∷ rs
          go ps P rs cs <&> ×-map₁₂ id (α ∷_)
        nothing → do
          -- Otherwise, add m : T to the telescope and replace the corresponding
          -- constructor with m henceforth.
          method ← ("P" <>_) <$> render-name c
          q ← get-con-quantity c
          let argC = arg (arginfo visible (modality relevant q))
          let
            ps = raise 1 ps
            P = raise 1 P
            rs = (c' , var 0 []) ∷ raise 1 rs
          extend-context method (argC methodT) (go ps P rs cs) <&>
            ×-map₁₂ ((method , argC methodT) ∷_) (α ∷_)

make-elim-with : Elim-options → Name → Name → TC ⊤
make-elim-with opts elim D = work-on-types $ withNormalisation true do
  DT ← get-type D >>= normalise -- D : (ps : Γ) (is : Ξ) → Type _
  data-type pars cs ← get-definition D
    where _ → typeError [ "not a data type: " , nameErr D ]
  let
    open Elim-options opts
    DTTel , _ = pi-view DT
    parTel , ixTel = split-at pars DTTel
    parTelH = hide parTel
    ixTel = hide-if hide-indices ixTel
    DTel = ixTel ∷r ("" , argN (def D (tel→args 0 DTTel))) -- (is : Ξ) (_ : D ps is)
    DTel = raise 1 DTel
    PTel = if induction then id else λ _ → []
    argP = if hide-motive then argH else argN
    motiveTel = ("ℓ" , argH (quoteTerm Level))
              -- P : DTel → Type ℓ
              ∷ ("P" , argP (unpi-view (PTel DTel) (agda-sort (set (var (length (PTel DTel)) [])))))
              ∷ []
    DTel = raise 1 DTel
    -- We want to take is-hlevel as an argument, but we need to work in a context
    -- with an H-Level instance in scope.
    -- (d : DTel) → is-hlevel (P d) n
    hlevelTel = maybe→alt into-hlevel <&> λ n → "h" , argN
      (unpi-view (PTel DTel)
        (def (quote is-hlevel) (var (length (PTel DTel)) (tel→args 0 (PTel DTel))
          v∷ lit (nat n) v∷ [])))
    -- {d : DTel} {k : Nat} → H-Level (P d) (n + k)
    H-LevelTel = maybe→alt into-hlevel <&> λ n → "h" , argI
      (unpi-view (hide (PTel DTel)) (pi (argH (quoteTerm Nat)) (abs "k"
        (def (quote H-Level) (var (length (PTel DTel) + 1) (tel→args 1 (PTel DTel)) v∷
          def (quote _+_) (lit (nat n) v∷ var 0 [] v∷ []) v∷ [])))))
    ps = tel→args (length motiveTel + length hlevelTel) parTel
    P = var (length hlevelTel) []
    module I = Induction opts D pars ixTel cs
  methodTel , αs , rs ← in-context (reverse (parTelH ++ motiveTel ++ H-LevelTel)) (I.methods ps P)
  let
    baseTel = parTelH ++ motiveTel ++ hlevelTel ++ methodTel
    DTel = raise (length hlevelTel + length methodTel) DTel
    P = raise (length methodTel + length DTel) P
    Pd = apply-tm* P (tel→args 0 (PTel DTel))
    -- ∀ (ps : Γ) {ℓ} {P} (h : ∀ d → is-hlevel (P d) n)? (ms : methodTel) (d : DTel) → P d
    elimT = unpi-view (baseTel ++ DTel) Pd
  elimT' ← just <$> get-type elim <|> nothing <$ declare (argN elim) elimT
  for elimT' (unify elimT) -- Give a nicer error if the types don't match
  let
    ixTel = raise (length motiveTel + length hlevelTel + length methodTel) ixTel
    ps = raise (length methodTel + length ixTel) ps
    rs = raise (length ixTel) rs
  -- The replacements are in the H-Level context, so we substitute them back into
  -- our context using basic-instance.
  let
    h = length methodTel + length ixTel
    rs = Maybe-rec (λ n → applyS (inplaceS h
      (tel→lam (hide (PTel DTel))
        (def (quote basic-instance) (lit (nat n) v∷
          var (h + length (PTel DTel)) (tel→args 0 (PTel DTel)) v∷ [])))))
      id into-hlevel rs
  clauses ← in-context (reverse (baseTel ++ ixTel)) do
    let getClause = λ (c , α) → do
      cT ← flip pi-applyTC ps =<< normalise =<< get-type c
      let
        cTel = pi-view-path cT
        pats = tel→pats (length cTel) (baseTel ++ ixTel) ∷r argN (con c (tel→pats 0 cTel))
        rec = def elim (tel→args (length ixTel + length cTel) baseTel)
        α = applyS (singletonS (length cTel) rec) α
      just m ← pure (I.replace rs (con c (hide ps)))
        where _ → typeError []
      let m = apply-tm* (raise (length cTel) m) α
      pure (clause (baseTel ++ ixTel ++ cTel) pats m)
    traverse getClause (zip cs αs)
  define-function elim clauses

default-elim = record
  { induction = true
  ; into-hlevel = nothing
  ; hide-motive = true
  ; hide-indices = true
  ; hide-cons-args = false
  }

default-elim-visible = record
  { induction = true
  ; into-hlevel = nothing
  ; hide-motive = false
  ; hide-indices = false
  ; hide-cons-args = false
  }

default-rec = record default-elim { induction = false }
default-rec-visible = record default-elim-visible { induction = false }

_into_ : Elim-options → Nat → Elim-options
opts into n = record opts { into-hlevel = just n }

make-elim make-rec : Name → Name → TC ⊤
make-elim = make-elim-with default-elim
make-rec = make-elim-with default-rec

make-elim-n make-rec-n : Nat → Name → Name → TC ⊤
make-elim-n n = make-elim-with (default-elim into n)
make-rec-n n = make-elim-with (default-rec into n)
