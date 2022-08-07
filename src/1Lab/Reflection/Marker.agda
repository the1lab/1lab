module 1Lab.Reflection.Marker where

open import 1Lab.Reflection
open import 1Lab.Type
open import 1Lab.Path

-- The marker. The marker is literally just the identity function, but
-- written surrounding rather than prefix. Unlike literally the identity
-- function, however, the marker is marked NOINLINE, so it will not
-- disappear without reduction.
⌜_⌝ : ∀ {ℓ} {A : Type ℓ} → A → A
⌜ x ⌝ = x
{-# NOINLINE ⌜_⌝ #-}

-- Abstract over the marked term(s). All marked terms refer to the same
-- variable, so e.g.
--
--  abstract-marker (quoteTerm (f ⌜ x ⌝ (λ _ → ⌜ x ⌝)))
--
-- is (λ e → f e (λ _ → e)). The resulting term is open in precisely one
-- variable: that variable is what substitutes the marked terms.
abstract-marker : Term → TC Term
abstract-marker = go 0 where
  go : Nat → Term → TC Term
  go* : Nat → List (Arg Term) → TC (List (Arg Term))

  go k (var j args) = go* k args >>= returnTC ∘ var (suc (k + j))
  go k (con c args) = go* k args >>= returnTC ∘ con c
  go k (def f args) with f
  ... | quote ⌜_⌝ = returnTC (var k [])
  -- ^ This is the one interesting case. Any application of the marker
  -- gets replaced with the 'k'th variable. Initially k = 0, so this is
  -- the variable bound by the lambda. But as we encounter further
  -- binders, we must increment this, since the marked term gets farther
  -- and farther away in the context.
  ... | x = go* k args >>= returnTC ∘ def f
  go k (lam v (abs x t)) = go (suc k) t >>= returnTC ∘ lam v ∘ abs x
  go k (pat-lam cs args) =
    typeError (strErr "Can not abstract over marker in term containing pattern lambdas" ∷ [])
  go k (pi (arg i a) (abs x t)) = do
    t ← go (suc k) t
    a ← go k a
    returnTC (pi (arg i a) (abs x t))
  go k (agda-sort s) with s
  ... | set t = go k t >>= returnTC ∘ agda-sort ∘ set
  ... | lit n = returnTC (agda-sort (lit n))
  ... | prop t = go k t >>= returnTC ∘ agda-sort ∘ prop
  ... | propLit n = returnTC (agda-sort (propLit n))
  ... | inf n = returnTC (agda-sort (inf n))
  ... | unknown = returnTC (agda-sort unknown)
  go k (lit l) = returnTC (lit l)
  go k (meta m args) = go* k args >>= returnTC ∘ meta m
  go k unknown = returnTC unknown

  go* k [] = returnTC []
  go* k (arg i x ∷ xs) = do
    x ← go k x
    xs ← go* k xs
    returnTC (arg i x ∷ xs)

macro
  -- Generalised ap. Automatically generates the function to apply to by
  -- abstracting over any markers in the LEFT ENDPOINT of the path. Use
  -- with _≡⟨_⟩_.
  ap! : ∀ {ℓ} {A : Type ℓ} {x y : A} → x ≡ y → Term → TC ⊤
  ap! path goal = do
    goalt ← inferType goal
    just (l , r) ← get-boundary goalt
      where nothing → typeError (strErr "ap!: Goal type " ∷
                                 termErr goalt ∷
                                 strErr " is not a path type" ∷ [])
    l′ ← abstract-marker l
    path′ ← quoteTC path
    unify goal (def (quote ap) (lam visible (abs "x" l′) v∷ path′ v∷ []))

  -- Generalised ap. Automatically generates the function to apply to by
  -- abstracting over any markers in the RIGHT ENDPOINT of the path. Use
  -- with _≡˘⟨_⟩_.
  ap¡ : ∀ {ℓ} {A : Type ℓ} {x y : A} → x ≡ y → Term → TC ⊤
  ap¡ path goal = do
    goalt ← inferType goal
    just (l , r) ← get-boundary goalt
      where nothing → typeError (strErr "ap¡: Goal type " ∷
                                 termErr goalt ∷
                                 strErr " is not a path type" ∷ [])
    r′ ← abstract-marker r
    path′ ← quoteTC path
    unify goal $
      def (quote ap) (lam visible (abs "x" r′) v∷ path′ v∷ [])

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
