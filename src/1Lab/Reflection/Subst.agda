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

singletonS : Nat → Term → Subst
singletonS n u = map (λ i → var i []) (count (n - 1)) ++# u ∷ (raiseS n)
  where
    count : Nat → List Nat
    count zero = []
    count (suc n) = 0 ∷ map suc (count n)

{-# TERMINATING #-}
subst-clause : Subst → Clause → Clause
subst-tm     : Subst → Term → Term
subst-tm*    : Subst → List (Arg Term) → List (Arg Term)
apply-tm     : Term → Arg Term → Term

raise : Nat → Term → Term
raise n = subst-tm (raiseS n)

subst-tm* ρ []             = []
subst-tm* ρ (arg ι x ∷ ls) = arg ι (subst-tm ρ x) ∷ subst-tm* ρ ls

apply-tm* : Term → List (Arg Term) → Term
apply-tm* tm []       = tm
apply-tm* tm (x ∷ xs) = apply-tm* (apply-tm tm x) xs

lookup-tm : (σ : Subst) (i : Nat) → Term
lookup-tm ids i = var i []
lookup-tm (wk n ids) i = var (i + n) []
lookup-tm (wk n ρ) i = subst-tm (raiseS n) (lookup-tm ρ i)
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
subst-tm ρ (pi (arg ι a) (abs n b)) = pi (arg ι (subst-tm ρ a)) (abs n (subst-tm (liftS 1 ρ)  b))
subst-tm ρ (lit l) = (lit l)
subst-tm ρ unknown = unknown
subst-tm ρ (agda-sort s) with s
… | set t     = agda-sort (set (subst-tm ρ t))
… | lit n     = agda-sort (lit n)
… | prop t    = agda-sort (prop (subst-tm ρ t))
… | propLit n = agda-sort (propLit n)
… | inf n     = agda-sort (inf n)
… | unknown   = unknown

subst-clause σ (clause tel ps t)      = clause tel ps (subst-tm (wkS (length tel) σ) t)
subst-clause σ (absurd-clause tel ps) = absurd-clause tel ps

_<#>_ : Term → Arg Term → Term
f <#> x = apply-tm f x

infixl 7 _<#>_
