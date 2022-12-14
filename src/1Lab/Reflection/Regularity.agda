{-# OPTIONS --allow-unsolved-metas #-}
open import 1Lab.Reflection.HLevel
open import 1Lab.Reflection.Subst
open import 1Lab.Reflection
open import 1Lab.Path
open import 1Lab.Type

module 1Lab.Reflection.Regularity where

{-
A tactic for reducing "transport refl x" in other-wise normal terms. The
implementation is actually surprisingly simple: A term of the form (e.g.)

    transport refl (f (transport refl x))

is already a blueprint for how to normalise it. We simply have to turn it into

    λ i → transport-refl (f (transport-refl x i)) i

The implementation presents itself: Raise the original term, and look
through to find reflexive transports. These can be replaced by an
application of transport-refl.
-}

private
  -- Ahem, not transport-refl, but a tiny tiny wrapper around it. The
  -- reason we have 'regular' is to mark terms we're *leaving*: The
  -- translation proceeds inside out, so to have a way to stop, we mark
  -- terms we have already visited entirely using `regular`.
  regular : ∀ {ℓ} {A : Type ℓ} (x : A) → transport refl x ≡ x
  regular x = transport-refl x

  -- And we have a double composition operator that doesn't use the
  -- fancy hcomp syntax in its definition. This has better type
  -- inference for one of the macros since it guarantees that the base
  -- (q i) is independent of j without any reduction.
  double-comp
    : ∀ {ℓ} {A : Type ℓ} {w z : A} (x y : A)
    → w ≡ x → x ≡ y → y ≡ z
    → w ≡ z
  double-comp x y p q r i = primHComp
    (λ { j (i = i0) → p (~ j) ; j (i = i1) → r j }) (q i)

  -- The regularity tactic can operate in two modes: `precise` will work
  -- with the type-checker to identify which `transp`s are along refl,
  -- and which should be preserved. The `fast` mode says YOLO and
  -- assumes that **every** application of `transp` is one that would
  -- reduce by regularity. Needless to say, only use `fast` when you're
  -- sure that's the case (e.g. the fibres of a displayed category over
  -- Sets)
  data Regularity-precision : Type where
    precise fast : Regularity-precision
  -- As the name implies, `precise` is `precise`, while `fast` is
  -- `fast`. The reason is that `fast` will avoid traversing many of the
  -- terms involved in a `transp`: It doesn't care about the level, it
  -- doesn't care about the line, and it doesn't care about the
  -- cofibration.

  -- The core of the tactic is this triad of mutually recursive
  -- functions. In all three of them, the `Nat` argument indicates how
  -- many binders we've gone under: it is the dimension variable we
  -- abstracted over at the start.
  refl-transport : Nat → Term → TC Term
  -- ^ Determines whether an application of `transp` is a case of
  -- regularity, and if so, replaces it by `regular`. Precondition: its
  -- subterms must already be reduced.
  go  : Regularity-precision → Nat → Term → TC Term
  -- ^ Reduces all the subterms, and finds applications of `transp` to
  -- hand off to `refl-transport`.
  go* : Regularity-precision → Nat → List (Arg Term) → TC (List (Arg Term))
  -- ^ Isn't the termination checker just lovely?

  refl-transport n tm′@(def (quote transp) (ℓ h∷ Al v∷ phi v∷ x v∷ [])) =
    -- This match might make you wonder: Can't Al be a line of
    -- functions, so that the transport will have more arguments? No:
    -- The term is in normal form.
    (do
      -- The way we check for regularity is simple: The line must have
      -- been reduced to an abstraction, and it must unify with refl. We
      -- use backtracking to fall back to the case where the transport
      -- was legitimately interesting!
      debugPrint "tactic.regularity:" 10 $ "Checking regularity of " ∷ termErr Al ∷ []
      lam visible (abs v Ab) ← pure Al
        where _ → typeError []
      unify-loudly Al (def (quote refl) [])
      unify phi (con (quote i0) [])
      let tm′ = def (quote regular) (x v∷ var n [] v∷ [])
      pure tm′) <|>
    (do
      debugPrint "tactic.regularity" 10 $ "NOT a (transport refl): " ∷ termErr tm′ ∷ []
      pure tm′)
  refl-transport _ tm′ = pure tm′

  -- Boring term traversal.
  go pre n (var x args) = var x <$> go* pre n args
  go pre n (con c args) = con c <$> go* pre n args
  go fast n (def (quote transp) (_ ∷ _ ∷ _ ∷ x v∷ [])) = do
    x ← go fast n x
    pure $ def (quote regular) (x v∷ var n [] v∷ [])
  go pre n (def f args) = do
    as ← go* pre n args
    refl-transport n (def f as)
  go pre k (lam v (abs n b)) = lam v ∘ abs n <$> go pre (suc k) b
  go pre n (pat-lam cs args) = typeError $ "regularity: Can not deal with pattern lambdas"
  go pre n (pi (arg i a) (abs nm b)) = do
    a ← go pre n a
    b ← go pre (suc n) b
    pure (pi (arg i a) (abs nm b))
  go pre n (agda-sort s) = pure (agda-sort s)
  go pre n (lit l) = pure (lit l)
  go pre n (meta x args) = meta x <$> go* pre n args
  go pre n unknown = pure unknown

  go* pre n [] = pure []
  go* pre n (arg i a ∷ as) = do
    a ← go pre n a
    (arg i a ∷_) <$> go* pre n as

  -- To turn a term into a regularity path, given a level of precision,
  -- all we have to do is raise the term by one, do the procedure above,
  -- then wrap it in a lambda. Nice!
  to-regularity-path : Regularity-precision → Term → TC Term
  to-regularity-path pre tm = do
    tm ← maybe→alt (raise 1 tm) <?> "Failed to raise term in regularity tactic"
    -- Since we'll be comparing terms, Agda really wants them to be
    -- well-scoped. Since we shifted eeeverything up by one, we have to
    -- grow the context, too.
    tm ← runSpeculative $ extendContext "i" (argN (quoteTerm I)) do
      tm ← go pre 0 tm
      pure (tm , false)
    pure $ lam visible $ abs "i" $ tm

  -- Extend a path x ≡ y to a path x′ ≡ y′, where x′ --> x and y′ --> y
  -- under the given regularity precision. Shorthand for composing
  --    regularity! ∙ p ∙ sym regularity!.
  regular!-worker :
    ∀ {ℓ} {A : Type ℓ} {x y : A}
    → Regularity-precision
    → x ≡ y
    → Term
    → TC ⊤
  regular!-worker {x = x} {y} pre p goal = do
    gt ← inferType goal
    `x ← quoteTC x
    `y ← quoteTC y
    `p ← quoteTC p
    just (_ , l , r) ← unapply-path =<< inferType goal
      where _ → typeError []
    l ← normalise =<< wait-for-type l
    r ← normalise =<< wait-for-type r
    reg ← to-regularity-path pre l
    reg′ ← to-regularity-path pre r
    unify-loudly goal $ def (quote double-comp) $
         `x v∷ `y v∷ reg
      v∷ `p
      v∷ def (quote sym) (reg′ v∷ [])
      v∷ []

module Regularity where
  open Regularity-precision public
  -- The reflection interface: Regularity.reduce! will, well, reduce a
  -- term. The tactic is robust enough to grow terms, if you invert the
  -- path, as well. There's a lot of blocking involved in making this
  -- work.
  macro
    reduce! : Term → TC ⊤
    reduce! goal = do
      just (_ , l , r) ← unapply-path =<< inferType goal
        where _ → typeError []
      reg ← to-regularity-path precise =<< (wait-for-type =<< normalise l)
      unify-loudly goal reg

    -- We then have wrappers that reduce on one side, and expand on the
    -- other, depending on how precise you want the reduction to be.
    precise! : ∀ {ℓ} {A : Type ℓ} {x y : A} → x ≡ y → Term → TC ⊤
    fast! : ∀ {ℓ} {A : Type ℓ} {x y : A} → x ≡ y → Term → TC ⊤

    precise! p goal = regular!-worker precise p goal
    fast! p goal = regular!-worker fast p goal

    -- For debugging purposes, this macro will take a term and output
    -- its (transport refl)-normal form, according to the given level of
    -- precision.
    reduct : Regularity-precision → Term → Term → TC ⊤
    reduct pres tm _ = do
      orig ← wait-for-type =<< normalise tm
      tm ← to-regularity-path pres orig
      red ← maybe→alt (apply-tm tm (argN (con (quote i1) []))) >>= normalise
      `pres ← quoteTC pres
      typeError $
        "The term\n\n  " ∷ termErr orig ∷ "\n\nreduces modulo " ∷ termErr `pres ∷ " regularity to\n\n  "
        ∷ termErr red
        ∷ "\n"

-- Test cases.
module
  _ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′} (f g : A → B) (x : A)
    (a-loop : (i : I) → Type ℓ [ (i ∨ ~ i) ↦ (λ ._ → A) ])
  where private

  p : (h : ∀ x → f x ≡ g x)
    → transport (λ i → A → B)
        (λ x → transport refl (transport refl (f (transport refl x)))) ≡ g
  p h = Regularity.reduce! ∙ funext h

  q : transport refl (transp (λ i → outS (a-loop i)) i0 x) ≡ transp (λ i → outS (a-loop i)) i0 x
  q = Regularity.reduce!

  -- Imprecise/fast reduction: According to it, the normal form of the
  -- transport below is refl. That's.. not the case, at least we don't
  -- know so. Precise regularity handles it, though.
  q′ : ⊤
  q′ = {! Regularity.reduct Regularity.fast (transp (λ i → outS (a-loop i)) i0 x) !}

  r : (h : ∀ x → f x ≡ g x) → transport refl (f x) ≡ transport refl (g x)
  r h = Regularity.precise! (h x)

  s : (h : ∀ x → f x ≡ g x) → transport refl (g x) ≡ transport refl (f x)
  s h = sym $ Regularity.fast! (h x)
