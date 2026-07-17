{-# OPTIONS --allow-unsolved-metas #-}
open import 1Lab.Reflection
open import 1Lab.Path
open import 1Lab.Type

open import Data.Maybe.Base

open import Prim.Data.Nat

module 1Lab.Reflection.Marker where

-- The marker. The marker is literally just the identity function, but
-- written surrounding rather than prefix. Unlike literally the identity
-- function, however, the marker is marked NOINLINE, so it will not
-- disappear without reduction.
⌜_⌝ : ∀ {ℓ} {A : Type ℓ} → A → A
⌜ x ⌝ = x
{-# NOINLINE ⌜_⌝ #-}

-- A placeholder for terms that should be turned into metavariables when
-- abstracting.
-- This can be used with apd! to mark terms on which the type of a
-- marker depends, as long as the path that ¿? replaces can be inferred
-- from the type of the argument to apd!.
¿? : ∀ {ℓ} {A : Type ℓ} {x : A} → A
¿? {x = x} = x
{-# NOINLINE ¿? #-}

-- Abstract over the marked term(s). All marked terms refer to the same
-- variable, so e.g.
--
--  abstract-marker (quoteTerm (f ⌜ x ⌝ (λ _ → ⌜ x ⌝)))
--
-- is (λ e → f e (λ _ → e)). The resulting term is open in precisely one
-- variable: that variable is what substitutes the marked terms.
abstract-marker : Nat → Term → Maybe Term
abstract-marker base = go 0 where
  go  : Nat → Term → Maybe Term
  go* : Nat → List (Arg Term) → Maybe (List (Arg Term))

  go k (var j args) = var j' <$> go* k args where
    j' : Nat
    j' with j < k
    ... | false = base + j
    ... | true = j
  go k (con c args) = con c <$> go* k args
  go k (def f args) with f
  ... | quote ⌜_⌝ = pure (var k [])
  -- ^ This is the first interesting case. Any application of the marker
  -- gets replaced with the 'k'th variable. Initially k = 0, so this is
  -- the variable bound by the lambda. But as we encounter further
  -- binders, we must increment this, since the marked term gets farther
  -- and farther away in the context.
  ... | quote ¿? = pure unknown
  ... | x = def f <$> go* k args
  go k (lam v (abs x t)) = lam v ∘ abs x <$> go (suc k) t
  go k (pat-lam cs args) = nothing
  go k (pi (arg i a) (abs x t)) = do
    t ← go (suc k) t
    a ← go k a
    pure (pi (arg i a) (abs x t))
  go k (agda-sort s) with s
  ... | type t = agda-sort ∘ type <$> go k t
  ... | lit n = pure (agda-sort (lit n))
  ... | prop t = agda-sort ∘ prop <$> go k t
  ... | propLit n = pure (agda-sort (propLit n))
  ... | inf n = pure (agda-sort (inf n))
  ... | unknown = pure (agda-sort unknown)
  go k (lit l) = pure (lit l)
  go k (meta m args) = meta m <$> go* k args
  go k unknown = pure unknown

  go* k [] = pure []
  go* k (arg i x ∷ xs) = do
    x ← go k x
    xs ← go* k xs
    pure (arg i x ∷ xs)

private
  -- We need this weird record (instead of a Σ-type) for two reasons.
  -- One is universe levels. The second is that, if we're elaborating a
  -- pre-existing
  --
  --   ap! p
  --
  -- (and supposing ap! had type {it : Σ Type _} → it .fst → x ≡ y), we
  -- will elaborate p against it .fst *before* running the ap-worker
  -- tactic, which very helpfully solves it := ? , [type of p] and
  -- prevents the tactic from firing. So we also need it to be
  -- no-eta-equality.
  record ap-data {ℓ} {A : Type ℓ} (x y : A) : Typeω where
    no-eta-equality ; pattern ; constructor mkapdata
    field
      ℓ-mark : Level
      mark   : Type ℓ-mark
      from   : mark → x ≡ y

  ap-worker : ∀ {ℓ} {A : Type ℓ} (x : A) → Term → TC ⊤
  ap-worker x goal = withNormalisation false do
    `x ← wait-for-type =<< quoteTC x
    case abstract-marker 1 `x of λ where
      (just l) → do
        debugPrint "tactic.marked-ap" 10
          [ "original  " , termErr `x , "\n"
          , "abstracted" , termErr (lam visible (abs "x" l))
          ]
        unify goal (con (quote mkapdata) (unknown v∷ unknown v∷ def (quote ap) (lam visible (abs "x" l) v∷ []) v∷ []))
      nothing → typeError [ "Failed to abstract over marker in term" , termErr `x ]

  open ap-data

  ap!-wrapper : ∀ {ℓ} {A : Type ℓ} {x y : A} {@(tactic ap-worker x) it : ap-data x y} → it .mark → x ≡ y
  ap!-wrapper {it = mkapdata _ _ f} = f

  ap¡-wrapper : ∀ {ℓ} {A : Type ℓ} {x y : A} {@(tactic ap-worker y) it : ap-data x y} → it .mark → x ≡ y
  ap¡-wrapper {it = mkapdata _ _ f} = f

macro
  -- Generalised ap. Automatically generates the function to apply to by
  -- abstracting over any markers in the LEFT ENDPOINT of the path. Use
  -- with _≡⟨_⟩_.
  ap! : Term → TC ⊤
  ap! g = unify g (def (quote ap!-wrapper) [])

  -- Generalised ap. Automatically generates the function to apply to by
  -- abstracting over any markers in the RIGHT ENDPOINT of the path. Use
  -- with _≡˘⟨_⟩_.
  ap¡ : Term → TC ⊤
  ap¡ g = unify g (def (quote ap¡-wrapper) [])

module _ {ℓ} {A : Type ℓ} {x y : A} {p : x ≡ y} {f : A → (A → A) → A} where
  private
    q : f x (λ y → x) ≡ f y (λ z → y)
    q =
      f ⌜ x ⌝ (λ _ → ⌜ x ⌝) ≡⟨ ap! p ⟩
      f y (λ _ → y)         ∎

    r : f y (λ _ → y) ≡ f x (λ _ → x)
    r =
      f ⌜ y ⌝ (λ _ → ⌜ y ⌝) ≡˘⟨ ap¡ p ⟩
      f x (λ _ → x)         ∎

private
  -- In addition to supporting ¿? to mark explicit problematic
  -- dependencies, we also remove all implicit arguments when
  -- abstracting over the path.
  censor  : Term → Term
  censor* : List (Arg Term) → List (Arg Term)

  censor (var x args)             = var x (censor* args)
  censor (con c args)             = con c (censor* args)
  censor (def f args)             = def f (censor* args)
  censor (lam v (abs n tm))       = lam v (abs n (censor tm))
  censor (pat-lam cs args)        = pat-lam cs (censor* args)
  censor (pi (arg i x) (abs n y)) = pi (arg i (censor x)) (abs n (censor y))
  censor (agda-sort s)            = agda-sort s
  censor (lit l)                  = lit l
  censor (meta m args)            = unknown
  censor unknown                  = unknown

  censor* [] = []
  censor* (t v∷ ts) = censor t v∷ censor* ts
  censor* (t h∷ ts) = censor* ts
  censor* (t i∷ ts) = censor* ts

  macro
    apd-worker : ∀ {ℓ} {A : Type ℓ} → A → Term → Term → TC ⊤
    apd-worker endpoint what goal = withNormalisation false do
      `endpoint ← wait-for-type =<< quoteTC endpoint
      case abstract-marker 2 (censor `endpoint) of λ where
        (just l) → do
          let fn = lam visible (abs "i" (lam visible (abs "x" l)))
          debugPrint "tactic.marked-ap" 10
            [ "original  " , termErr `endpoint , "\n"
            , "abstracted" , termErr fn
            ]
          unify goal (def₀ (quote apd) ##ₙ fn ##ₙ what)
        nothing → typeError [ "apd!: Failed to abstract over marker in term\n  " , termErr `endpoint ]

  -- The entry point for apd! can't use tactic arguments to have the
  -- elaborator propagate the endpoint; it's just too circular.
  --
  -- To prevent a performance blowup from quoting the entire type of the
  -- goal, we take it apart by unifying against metavariables and
  -- deferring to a different macro. The second macro application acts
  -- like a "fence" for the blockTC primitive.
  apd-wrapper : Bool → Term → Term → TC ⊤
  apd-wrapper right what goal = do
    meta Tmv T ← new-meta' $ pi (argN (quoteTerm I))
      (abs "i" (def (quote Type) (unknown v∷ [])))

    l ← new-meta (T ##ₙ quoteTerm i0)
    r ← new-meta (T ##ₙ quoteTerm i1)

    g' ← check-type goal (def₀ (quote PathP) ##ₙ T ##ₙ l ##ₙ r)

    unify goal (def₀ (quote apd-worker) ##ₙ (if right then r else l) ##ₙ what)

macro
  -- Generalised apd. Automatically generates the function to apply to
  -- by abstracting over any markers in the LEFT ENDPOINT of the path.
  -- Use with _≡[]⟨_⟩_.
  apd! : Term → Term → TC ⊤
  apd! = apd-wrapper false

  -- Generalised apd. Automatically generates the function to apply to
  -- by abstracting over any markers in the RIGHT ENDPOINT of the path.
  -- Use with _≡[]˘⟨_⟩_.
  apd¡ : Term → Term → TC ⊤
  apd¡ = apd-wrapper true

module
  _ {ℓ ℓ' ℓ''} {A : Type ℓ} {x y : A} {p : x ≡ y} {B : A → Type ℓ'}
    {α : B x} {β : B y} (q : PathP (λ i → B (p i)) α β)
    {C : (x : A) → B x → Type ℓ''}
    (f : {x : A} (y : B x) → C x y)
    (g : (x : A) (y : B x) → C x y)
  where

  -- test that needs 'censor'
  _ : PathP (λ i → C (p i) (q i)) (f ⌜ α ⌝) (f β)
  _ = apd! q

  -- test that needs an explicit placeholder
  _ : PathP (λ i → C (p i) (q i)) (g ¿? ⌜ α ⌝) (g y β)
  _ = apd! q

  -- test that the tactic works with goals.
  -- this needs --quote-metas
  _ : PathP (λ i → C (p i) (q i)) (f ⌜ α ⌝) (f β)
  _ = apd! {!   !}
