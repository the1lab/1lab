open import 1Lab.Reflection
open import 1Lab.Type

open import Data.Maybe.Base

open import Meta.Foldable

open import Prim.Data.Nat

module 1Lab.Reflection.Subst where

data Subst : Type where
  ids        : Subst
  _∷_        : Term → Subst → Subst
  wk         : Nat → Subst → Subst
  lift       : Nat → Subst → Subst
  strengthen : Nat → Subst → Subst

infixr 20 _∷_

wkS : Nat → Subst → Subst
wkS zero ρ = ρ
wkS n (wk x ρ) = wk (n + x) ρ
wkS n ρ        = wk n ρ

liftS : Nat → Subst → Subst
liftS zero ρ       = ρ
liftS n ids        = ids
liftS n (lift k ρ) = lift (n + k) ρ
liftS n ρ          = lift n ρ

_++#_ : List Term → Subst → Subst
x ++# ρ = foldr (_∷_) ρ x
infix 15 _++#_

raiseS : Nat → Subst
raiseS n = wk n ids

raise-fromS : Nat → Nat → Subst
raise-fromS n k = liftS n $ raiseS k

--            Γ, Δ ⊢ u : A
-- ---------------------------------
-- Γ, Δ ⊢ singletonS |Δ| u : Γ, A, Δ
singletonS : Nat → Term → Subst
singletonS n u = map (λ i → var i []) (count n) ++# u ∷ raiseS n

--           Γ, A, Δ ⊢ u : A
-- ----------------------------------
-- Γ, A, Δ ⊢ inplaceS |Δ| u : Γ, A, Δ
inplaceS : Nat → Term → Subst
inplaceS n u = map (λ i → var i []) (count n) ++# u ∷ raiseS (suc n)

record Has-subst {ℓ} (A : Type ℓ) : Type (lsuc ℓ) where
  field applyS : Subst → A → A

open Has-subst ⦃ ... ⦄ using (applyS) public

raise : ∀ {ℓ} {A : Type ℓ} ⦃ _ : Has-subst A ⦄ → Nat → A → A
raise n = applyS (raiseS n)

raise* : ∀ {ℓ} {A : Type ℓ} ⦃ _ : Has-subst A ⦄ → Nat → List A → List A
raise* n = map (raise n)

applyS* : ∀ {ℓ} {A : Type ℓ} ⦃ _ : Has-subst A ⦄ → Subst → List A → List A
applyS* ρ = map (applyS ρ)

instance
  Has-subst-Arg : ∀ {ℓ} {A : Type ℓ} ⦃ _ : Has-subst A ⦄ → Has-subst (Arg A)
  Has-subst-Arg .Has-subst.applyS ρ (arg ai x) = arg ai (applyS ρ x)

{-# TERMINATING #-}
subst-clause : Subst → Clause → Clause
subst-tm     : Subst → Term → Term
subst-tm*    : Subst → List (Arg Term) → List (Arg Term)
apply-tm     : Term → Arg Term → Term
subst-tel    : Subst → Telescope → Telescope

instance
  Has-subst-Term : Has-subst Term
  Has-subst-Term = record { applyS = subst-tm }

  Has-subst-Clause : Has-subst Clause
  Has-subst-Clause = record { applyS = subst-clause }

  Has-subst-Args : Has-subst (List (Arg Term))
  Has-subst-Args = record { applyS = subst-tm* }

  Has-subst-Telescope : Has-subst Telescope
  Has-subst-Telescope = record { applyS = subst-tel }

  Has-subst-Abs : ∀ {ℓ} {A : Type ℓ} ⦃ _ : Has-subst A ⦄ → Has-subst (Abs A)
  Has-subst-Abs = record { applyS = λ rho (abs nm a) → abs nm (applyS (liftS 1 rho) a) }

subst-tm* ρ []             = []
subst-tm* ρ (arg ι x ∷ ls) = arg ι (subst-tm ρ x) ∷ subst-tm* ρ ls

apply-tm* : Term → List (Arg Term) → Term
apply-tm* tm []       = tm
apply-tm* tm (x ∷ xs) = apply-tm* (apply-tm tm x) xs

lookup-tm : (σ : Subst) (i : Nat) → Term
lookup-tm ids i = var i []
lookup-tm (wk n ids) i = var (i + n) []
lookup-tm (wk n ρ) i = raise n (lookup-tm ρ i)
lookup-tm (x ∷ ρ) i with (i == 0)
… | true  = x
… | false = lookup-tm ρ (i - 1)
lookup-tm (strengthen n ρ) i with (i < n)
… | true  = unknown
… | false = lookup-tm ρ (i - n)
lookup-tm (lift n σ) i with (i < n)
… | true  = var i []
… | false = raise n (lookup-tm σ (i - n))

apply-tm (var x args)      argu = var x (args ++ argu ∷ [])
apply-tm (con c args)      argu = con c (args ++ argu ∷ [])
apply-tm (def f args)      argu = def f (args ++ argu ∷ [])
apply-tm (lam v (abs n t)) (arg _ argu) = subst-tm (argu ∷ ids) t
apply-tm (pat-lam cs args) argu = pat-lam cs (args ++ argu ∷ [])
apply-tm (pi a b)          argu = pi a b
apply-tm (agda-sort s)     argu = agda-sort s
apply-tm (lit l)           argu = lit l
apply-tm (meta x args)     argu = meta x (args ++ argu ∷ [])
apply-tm unknown           argu = unknown

subst-tm ids tm = tm
subst-tm ρ (var i args)      = apply-tm* (lookup-tm ρ i) (subst-tm* ρ args)
subst-tm ρ (con c args)      = con c $ subst-tm* ρ args
subst-tm ρ (def f args)      = def f $ subst-tm* ρ args
subst-tm ρ (meta x args)     = meta x $ subst-tm* ρ args
subst-tm ρ (pat-lam cs args) = pat-lam (map (subst-clause ρ) cs) (subst-tm* ρ args)
subst-tm ρ (lam v (abs n b)) = lam v (abs n (subst-tm (liftS 1 ρ) b))
subst-tm ρ (pi (arg ι a) (abs n b)) = pi (arg ι (subst-tm ρ a)) (abs n (subst-tm (liftS 1 ρ) b))
subst-tm ρ (lit l) = (lit l)
subst-tm ρ unknown = unknown
subst-tm ρ (agda-sort s) with s
… | set t     = agda-sort (set (subst-tm ρ t))
… | lit n     = agda-sort (lit n)
… | prop t    = agda-sort (prop (subst-tm ρ t))
… | propLit n = agda-sort (propLit n)
… | inf n     = agda-sort (inf n)
… | unknown   = unknown

subst-tel ρ []                    = []
subst-tel ρ ((x , arg ai t) ∷ xs) = (x , arg ai (subst-tm ρ t)) ∷ subst-tel (liftS 1 ρ) xs

subst-clause σ (clause tel ps t)      = clause (subst-tel σ tel) ps (subst-tm (liftS (length tel) σ) t)
subst-clause σ (absurd-clause tel ps) = absurd-clause (subst-tel σ tel) ps

apply-abs : ∀ {ℓ} {A : Type ℓ} ⦃ _ : Has-subst A ⦄ → Abs A → Term → A
apply-abs (abs _ x) a = applyS (a ∷ ids) x

_<#>_ : Term → Arg Term → Term
f <#> x = apply-tm f x

infixl 7 _<#>_

pi-apply : Term → List (Arg Term) → Maybe Term
pi-apply ty as = go ty as ids where
  go : Term → List (Arg Term) → Subst → Maybe Term
  go (pi (arg _ x) (abs n y)) (arg _ a ∷ as) s = go y as (a ∷ s)
  go _ (_ ∷ as) s = nothing
  go t [] s = just (subst-tm s t)

pi-applyTC : Term → List (Arg Term) → TC Term
pi-applyTC f x with pi-apply f x
pi-applyTC f x | just r  = pure r
pi-applyTC f _ | nothing =
  typeError [ "Failed to apply type " , termErr f ]
