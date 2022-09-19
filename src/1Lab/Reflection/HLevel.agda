{-# OPTIONS -vtactic.hlevel:10 #-}
open import 1Lab.HLevel.Retracts
open import 1Lab.HLevel.Universe
open import 1Lab.Prim.Data.Nat
open import 1Lab.Reflection
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type
open import Data.List

module 1Lab.Reflection.HLevel where

{-
Tactic for generating readable h-level proofs automatically.

Over the instance resolution mechanism, this supports arbitrary-ish
hints for how to decompose goals and push obligations inwards. These are
used for all the basic type formers (and also lists, since we need lists
for this module).

Additionally, it handles ∣ A ∣ properly.

Falls back to instance search when no hints apply.
-}


-- | Argument specifications for decompositions.
data Arg-spec : Type where
  `level-minus  : (n : Nat) → Arg-spec
  -- ^ Insert the level we're solving for minus the given offset (note
  -- that this is the wonky subtraction operation, "monus") at this
  -- argument position

  `search-under : (n : Nat) → Arg-spec
  -- ^ Recursively search for an h-level witness under @n@ visible
  -- lambdas

  `meta         : Arg-spec
  -- ^ Insert a meta at this argument position

-- Common patterns: Keep the level, search in the current scope.
pattern `search = `search-under 0
pattern `level = `level-minus 0

-- | A specification for how to decompose the type @T@ into
-- sub-components for establishing an h-level result.
data Decomposition {ℓ} (T : Type ℓ) : Type where
  decomp : (h-level-lemma : Name) (arguments : List Arg-spec) → Decomposition T
  -- To prove that T has a given h-level, we can invoke the
  -- @h-level-lemma@ with the specified @arguments@.

private
  -- Throw an empty type error to try another alternative, stating the
  -- purpose of backtracking for debugging:
  backtrack : ∀ {ℓ} {A : Type ℓ} → String → TC A
  backtrack note = do
    debugPrint "tactic.hlevel" 10 $ strErr "Backtracking search... " ∷ strErr note ∷ []
    typeError []

  hlevel-types : List Name
  hlevel-types = quote is-hlevel ∷ quote is-prop ∷ quote is-contr ∷ []

  blockOn : Term → TC ⊤
  blockOn (meta m _) = do
    debugPrint "tactic.hlevel" 10 $
      strErr "type under consideration is meta, blocking to avoid problems on reload" ∷ []
    blockOnMeta m
  blockOn _ = pure tt

  -- | Infer the type of the goal and make sure that it is of the form
  -- @is-hlevel A n@.
  decompose-is-hlevel : Term → TC (Term × Term)
  decompose-is-hlevel goal = do
    ty ← dontReduceDefs hlevel-types $ inferType goal >>= reduce
    def (quote is-hlevel) (_ ∷ ty v∷ lv v∷ []) ← pure ty
      where
        def (quote is-prop) (_ ∷ ty v∷ []) → do
          blockOn ty
          pure (ty , (con (quote suc) (con (quote zero) [] v∷ [])))

        def (quote is-contr) (_ ∷ ty v∷ []) → do
          blockOn ty
          pure (ty , (con (quote zero) []))

        _ → backtrack "goal type isn't is-hlevel"

    -- To support having bare hlevel! in the source file, we need to
    -- block decomposition on having a rigid-ish type at the
    -- top-level. Otherwise the first hint that matches will get
    -- matched endlessly until we run out of fuel!
    blockOn ty
    blockOn lv
    lv′ ← normalise lv
    pure (ty , lv′)

  -- Step: Treat the type as being an n-Type, i.e., a projection of the
  -- form ∣ A ∣, where A : n-Type ℓ n.
  treat-as-n-type : Term → TC ⊤
  treat-as-n-type goal = do
    (ty , lv) ← decompose-is-hlevel goal
    debugPrint "tactic.hlevel" 10 $
      strErr "Attempting to treat as " ∷ termErr lv ∷ strErr "-Type: " ∷ termErr ty ∷ []

    -- Reduce to whnf to find the ∣_∣ application
    def (quote ∣_∣) (_ ∷ _ ∷ it v∷ []) ← reduce ty
      where _ → backtrack "thing isn't application of ∣_∣"

    -- and infer the actual level. we'll need it in a second.
    def (quote n-Type) (ell v∷ lv′t v∷ []) ← (inferType it >>= reduce)
      where _ → backtrack "type of thing isn't n-Type"
    lv ← unquoteTC lv
    lv′ ← normalise lv′t >>= unquoteTC

    debugPrint "tactic.hlevel" 10 $
      strErr "... but it's actually a(n) " ∷ termErr lv′t ∷ strErr "-Type" ∷ []

    -- Note that if A is an n-type, then it's also a k+n type for any n;
    -- so if we want (k+n) type, it suffices to have an n-type, and we
    -- can lift the type across.
    let
      go : Bool → Bool → TC ⊤
      go = λ where
        -- If the levels are actually the same then we're fine and we
        -- don't need to lift anything.
        true _ → unify goal $ def (quote is-tr) (it v∷ [])

        -- Otherwise we compute the difference (as an actual numeral,
        -- hence reducing away) and use @is-hlevel+@ to lift the result.
        false true → do
          let diff = lv - lv′
          offset ← quoteTC diff >>= reduce
          let lift = def (quote is-hlevel-+) $ lv′t v∷ offset v∷ (def (quote is-tr) (it v∷ [])) v∷ []
          debugPrint "tactic.hlevel" 10 $
            strErr "... but that's fine, because we can lift it using\n " ∷
            termErr lift ∷ []
          unify goal lift

        -- Try, try again.
        false false → backtrack "no way of raising it"

    go (lv′ == lv) (lv′ < lv)

    commitTC

  -- Fall back to Agda's instance search mechanism:
  use-instance-search : Term → TC ⊤
  use-instance-search goal = runSpeculative $ do
    (ty , lv) ← decompose-is-hlevel goal
    solved@(meta mv _) ←
      newMeta (def (quote H-Level) (ty v∷ lv v∷ [])) where _ → backtrack "impossible"
    instances ← getInstances mv

    t ← quoteTC instances
    debugPrint "tactic.hlevel" 10 $
      strErr "Using instance search for\n" ∷ termErr ty ∷
      strErr "\nFound candidates\n " ∷ termErr t ∷ []

    let
      go : List Term → TC (⊤ × Bool)
      go = λ where
        (x ∷ []) → do
          -- Note that we need to do this garbage to get rid of the meta
          -- before we can actually use the instance:
          unify solved x
          unify goal (def (quote H-Level.has-hlevel)
            (unknown h0∷ ty h0∷ lv h0∷ x v∷ []))
          pure (tt , true)
        _ → backtrack "wrong number of instances"
    go instances

  -- Main loop for the tactic:
  {-# TERMINATING #-}
  search : Term → Nat → Term → TC ⊤
  -- Give up if we're out of fuel:
  search _     zero    goal = unify goal unknown
  -- Actual main loop: try using the hints database, try treating the
  -- goal as an n-type, fall back to instance search.
  search level (suc n) goal =
    use-hints <|> treat-as-n-type goal <|> use-instance-search goal
    where
      -- Get rid of any invisible binders in the term
      remove-invisible : Term → Term → TC Term
      remove-invisible
        (lam _ (abs _ t))
        (pi (arg (arginfo invisible _) _) (abs _ ret))
        = remove-invisible t ret
      remove-invisible inner _ = pure inner

      -- Wrap a term in n visible lambdas
      wrap-lams : Nat → Term → Term
      wrap-lams zero r = r
      wrap-lams (suc x) r = lam visible $ abs "a" $ wrap-lams x r

      -- Compute a continuation which extends the context by n unknown
      -- variables
      extend-n : ∀ {ℓ} → Nat → TC ((A : Type ℓ) → TC A → TC A)
      extend-n zero = pure λ _ x → x
      extend-n (suc n) = do
        rest ← extend-n n
        mv ← newMeta unknown
        let domain = arg (arginfo visible (modality relevant quantity-ω)) mv
        pure λ a k → extendContext "a" domain $ rest a $ k

      -- Given a list of argument specs, actually unify the goal with
      -- the solution of decomposition, and call a continuation to
      -- perform any outstanding searches.
      gen-args
        : Name              -- ^ The h-level lemma
        → List Arg-spec     -- ^ The argument specifications
        → List (Arg Term)   -- ^ Accumulator: computed arguments (in reverse order)
        → TC ⊤              -- ^ Accumulator: what do we need to do after unifying the goal with the lemma?
        → TC ⊤              -- ^ Returns nada
      gen-args defn [] accum cont = do
        debugPrint "tactic.hlevel" 10 $
          strErr "Decomposition solution: " ∷ termErr (def defn (reverse accum)) ∷ []
        unify goal (def defn (reverse accum))
        cont

      gen-args defn (x ∷ args) accum cont with x
      -- If we have to insert the level minus some offset, then we need
      -- to do the computation:
      ... | `level-minus n = do
        level′ ← unquoteTC level
        level′′ ← quoteTC (level′ - n) >>= reduce
        -- Reduce otherwise we get Number.fromNat as the term
        gen-args defn args (level′′ v∷ accum) cont

      -- Insert a metavariable:
      ... | `meta = gen-args defn args (unknown v∷ accum) cont

      ... | `search-under under = do
        -- Create a new metavariable with n free variables of
        -- indeterminate type..
        gounder ← extend-n {lzero} under
        mv ← gounder Term $ newMeta unknown
        -- wrap the argument metavariable in n lambdas..
        gen-args defn args (wrap-lams under mv v∷ accum) $ do
          cont
          -- and go back under those indeterminates to search for a
          -- solution.
          gounder ⊤ $ search level n mv

      -- Try all the candidate hints in order.
      use-decomp-hints : (Term × Term) → Term → List Term → TC (⊤ × Bool)
      use-decomp-hints (goal-ty , lv) solved (c1 ∷ cs) = do
        ty ← inferType c1
        c1′ ← reduce c1
        (remove-invisible c1′ ty >>= λ where

          -- If we have an actual decomp constructor, then we can try
          -- using its argument specification to construct a little
          -- h-level lemma
          (con (quote decomp) (_ ∷ _ ∷ nm v∷ argspec v∷ [])) → do
            debugPrint "tactic.hlevel" 10 $ strErr "Using " ∷ termErr nm ∷ strErr " decomposition for: " ∷ termErr goal ∷ []
            nm′ ← unquoteTC nm
            argsp ← unquoteTC argspec
            gen-args nm′ argsp [] (returnTC tt)
            unify solved c1
            pure (tt , true)

          -- If we didn't get this then backtrack.
          _ → backtrack "non-canonical hint")
          -- If we didn't manage to get the hint to work for any reason,
          -- try again with the other hints.
          <|> use-decomp-hints (goal-ty , lv) solved cs

      use-decomp-hints _ _ [] = backtrack "ran out of hints"

      use-hints : TC ⊤
      use-hints = runSpeculative $ do
        (ty , lv) ← decompose-is-hlevel goal

        pure ty >>= λ where
          (meta m _) → do
            debugPrint "tactic.hlevel" 10 $
              strErr "Type under is-hlevel is metavariable, blocking to avoid infinite loop" ∷ []
            blockOnMeta m
          _ → pure tt

        -- Create a meta of type Decomposition to find any possible hints..
        solved@(meta mv _) ← newMeta (def (quote Decomposition) (ty v∷ []))
          where _ → typeError (termErr ty ∷ [])
        instances ← getInstances mv

        t ← quoteTC instances
        debugPrint "tactic.hlevel" 10 $
          strErr "Finding decompositions for\n" ∷
          termErr ty ∷
          strErr "\nFound candidates\n " ∷
          termErr t ∷ []

        -- And try using the hints.
        use-decomp-hints (ty , lv) solved instances

  hlevel-tactic-worker : Term → TC ⊤
  hlevel-tactic-worker goal = do
    ty ← dontReduceDefs hlevel-types $ inferType goal >>= reduce
    (ty , lv) ← decompose-is-hlevel goal <|>
      typeError
        ( strErr "hlevel tactic: goal type is not of the form ``is-hlevel A n'':\n"
        ∷ termErr ty
        ∷ [])

    -- 10 units of fuel isn't too many but it's enough for any realistic
    -- use-case.
    search lv 10 goal


-- Entry point to the macro:
macro hlevel! = hlevel-tactic-worker

el! : ∀ {ℓ} (A : Type ℓ) {n} {@(tactic hlevel-tactic-worker) hl : is-hlevel A n} → n-Type ℓ n
el! A {hl = hl} = el A hl

-- Set up the common hints:
instance
  decomp-lift : ∀ {ℓ ℓ′} {T : Type ℓ} → Decomposition (Lift ℓ′ T)
  decomp-lift = decomp (quote Lift-is-hlevel) (`level ∷ `search ∷ [])

  -- Non-dependent Π and Σ for readability first:
  decomp-fun : ∀ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′} → Decomposition (A → B)
  decomp-fun = decomp (quote fun-is-hlevel) (`level ∷ `search ∷ [])

  decomp-prod : ∀ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′} → Decomposition (A × B)
  decomp-prod = decomp (quote ×-is-hlevel) (`level ∷ `search ∷ `search ∷ [])

  -- Dependent type formers:
  decomp-pi : ∀ {ℓ ℓ′} {A : Type ℓ} {B : A → Type ℓ′} → Decomposition (∀ a → B a)
  decomp-pi = decomp (quote Π-is-hlevel) (`level ∷ `search-under 1 ∷ [])

  decomp-sigma : ∀ {ℓ ℓ′} {A : Type ℓ} {B : A → Type ℓ′} → Decomposition (Σ A B)
  decomp-sigma = decomp (quote Σ-is-hlevel) (`level ∷ `search ∷ `search-under 1 ∷ [])

  -- Path decomposition rules we have in scope:
  decomp-path : ∀ {ℓ} {A : Type ℓ} {a b : A} → Decomposition (a ≡ b)
  decomp-path = decomp (quote Path-is-hlevel) (`level ∷ `search ∷ [])

  decomp-path′ : ∀ {ℓ} {A : Type ℓ} {a b : A} → Decomposition (a ≡ b)
  decomp-path′ = decomp (quote Path-is-hlevel') (`level ∷ `search ∷ `meta ∷ `meta ∷ [])

  decomp-univalence : ∀ {ℓ} {A B : Type ℓ} → Decomposition (A ≡ B)
  decomp-univalence = decomp (quote ≡-is-hlevel) (`level ∷ `search ∷ `search ∷ [] )

  -- This doesn't really fit the theme but we have it handy so we might
  -- as well, right?
  decomp-list : ∀ {ℓ} {A : Type ℓ} → Decomposition (List A)
  decomp-list = decomp (quote ListPath.List-is-hlevel) (`level-minus 2 ∷ `search ∷ [])

private module _ {ℓ ℓ′} {A : n-Type ℓ 2} {B : ∣ A ∣ → n-Type ℓ′ 2} where
  p : is-hlevel (∀ (a : ∣ A ∣) → ∣ A ∣ ≡ ∣ A ∣) 2
  p = hlevel!
