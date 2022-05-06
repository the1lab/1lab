```agda
module Data.Nat.Solver where

open import 1Lab.Type
open import 1Lab.Path
open import 1Lab.HLevel
open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.List
open import Data.Bool

open import 1Lab.Reflection
```

# The Nat Solver

```agda

data Bag {a} (A : Type a) : Type a where
  ∅ : Bag A
  [_] : A → Bag A
  _∪_ : Bag A → Bag A → Bag A
  comm : ∀ xs ys → xs ∪ ys ≡ ys ∪ xs
  squash : is-set (Bag A)
```

```agda
data Expr : Type where
  ‵_   : Nat → Expr 
  ‵0   : Expr
  ‵1+_ : Expr → Expr
  _‵+_ : Expr → Expr → Expr
  _‵*_ : Expr → Expr → Expr

data Value : Type
data Frame : Type

data Value where
  v0 : Value
  vsuc : Value → Value
  vneu : Nat → List Frame → Value

data Frame where
  kplus : Value → Frame
  ktimes : Value → Frame
```

## Evaluation

```agda
do-plus : Value → Value → Value
do-plus v₁ v0 = v₁
do-plus v₁ (vsuc v₂) = vsuc (do-plus v₁ v₂)
do-plus v₁ (vneu hd spine) = vneu hd (kplus v₁ ∷ spine)

do-times : Value → Value → Value
do-times v₁ v0 = v0
do-times v₁ (vsuc v₂) = do-plus v₁ (do-times v₁ v₂)
do-times v₁ (vneu hd spine) = vneu hd (ktimes v₁ ∷ spine)

eval : Expr → Value
eval (‵ x) = vneu x []
eval ‵0 = v0
eval (‵1+ e) = vsuc (eval e)
eval (e₁ ‵+ e₂) = do-plus (eval e₁) (eval e₂)
eval (e₁ ‵* e₂) = do-times (eval e₁) (eval e₂)
```

## Quoting

```
enact-frames : List Frame → Expr → Expr
↑_ : Value → Expr

enact-frames [] e = e
enact-frames (kplus v ∷ spine) e = (↑ v) ‵+ (enact-frames spine e)
enact-frames (ktimes v ∷ spine) e = (↑ v) ‵* (enact-frames spine e)

↑ v0 = ‵0
↑ vsuc v = ‵1+ (↑ v)
↑ vneu hd spine = enact-frames spine (‵ hd)

nf : Expr → Expr
nf e = ↑ (eval e)
```

## Soundness

```agda
embed : Expr → Nat
embed (‵ x) = x
embed ‵0 = 0
embed (‵1+ e) = suc (embed e)
embed (e₁ ‵+ e₂) = embed e₁ + embed e₂
embed (e₁ ‵* e₂) = embed e₁ * embed e₂

do-plus-sound : ∀ v₁ v₂ → embed (↑ do-plus v₁ v₂) ≡ embed (↑ v₁) + embed (↑ v₂)
do-plus-sound v₁ v0 = sym (+-zeror (embed (↑ v₁))) 
do-plus-sound v₁ (vsuc v₂) =
  suc (embed (↑ do-plus v₁ v₂))     ≡⟨ ap suc (do-plus-sound v₁ v₂) ⟩
  suc (embed (↑ v₁) + embed (↑ v₂)) ≡˘⟨ +-sucr (embed (↑ v₁)) (embed (↑ v₂)) ⟩
  embed (↑ v₁) + suc (embed (↑ v₂)) ∎
do-plus-sound v₁ (vneu hd spine) = refl

do-times-sound : ∀ v₁ v₂ → embed (↑ do-times v₁ v₂) ≡ embed (↑ v₁) * embed (↑ v₂)
do-times-sound v₁ v0 = sym (*-zeror (embed (↑ v₁)))
do-times-sound v₁ (vsuc v₂) =
  embed (↑ do-plus v₁ (do-times v₁ v₂))      ≡⟨ do-plus-sound v₁ (do-times v₁ v₂) ⟩
  embed (↑ v₁) + embed (↑ do-times v₁ v₂)    ≡⟨ ap (embed (↑ v₁) +_) (do-times-sound v₁ v₂) ⟩
  embed (↑ v₁) + embed (↑ v₁) * embed (↑ v₂) ≡˘⟨ *-sucr (embed (↑ v₁)) (embed (↑ v₂)) ⟩
  embed (↑ v₁) * suc (embed (↑ v₂)) ∎
do-times-sound v₁ (vneu hd spine) = refl

sound : ∀ e → embed (nf e) ≡ embed e
sound (‵ x) = refl
sound ‵0 = refl
sound (‵1+ e) = ap suc (sound e)
sound (e₁ ‵+ e₂) =
  embed (↑ do-plus (eval e₁) (eval e₂)) ≡⟨ do-plus-sound (eval e₁) (eval e₂) ⟩
  embed (↑ eval e₁) + embed (↑ eval e₂) ≡⟨ ap₂ _+_ (sound e₁) (sound e₂) ⟩
  embed (e₁ ‵+ e₂) ∎
sound (e₁ ‵* e₂) =
  embed (↑ do-times (eval e₁) (eval e₂)) ≡⟨ do-times-sound (eval e₁) (eval e₂) ⟩
  embed (↑ eval e₁) * embed (↑ eval e₂)  ≡⟨ ap₂ _*_ (sound e₁) (sound e₂) ⟩
  embed e₁ * embed e₂ ∎

solution : ∀ e₁ e₂ → (embed (nf e₁) ≡ embed (nf e₂)) → embed e₁ ≡ embed e₂
solution e₁ e₂ p = sym (sound e₁) ∙ p ∙ sound e₂
```

## Unification

```agda
```


## Reflection
```agda
private  
  is-zero : Name → Bool
  is-zero = _name=? (quote zero)

  is-suc : Name → Bool
  is-suc = _name=? (quote suc)

  is-+ : Name → Bool
  is-+ = _name=? (quote _+_)

  is-* : Name → Bool
  is-* = _name=? (quote _*_)

  -- [TODO: Reed M, 06/05/2022] Factor out the recursion
  build-expr : Term → Term
  build-expr-args : List (Arg Term) → List (Arg Term)

  build-expr (def x as) with is-+ x | is-* x
  ... | _     | true  = con (quote _‵*_) (build-expr-args as)
  ... | true  | false = con (quote _‵+_) (build-expr-args as)
  ... | false | false = con (quote ‵_) (def x as v∷ [])
  build-expr (con x as) with is-zero x | is-suc x
  ... | _     | true  = con (quote ‵1+_) (build-expr-args as)
  ... | true  | false = con (quote ‵0) []
  -- NOTE: This should never really happen, but it's nicer than
  -- having to involve TC.
  ... | false | false = con (quote ‵_) (def x as v∷ [])
  build-expr x = con (quote ‵_) (x v∷ [])

  build-expr-args [] = []
  build-expr-args (arg i tm ∷ tms) = arg i (build-expr tm) ∷ build-expr-args tms

  getBoundary : Term → TC (Maybe (Term × Term))
  getBoundary tm@(def (quote PathP) (_ h∷ T v∷ x v∷ y v∷ [])) = do
    unify tm (def (quote _≡_) (x v∷ y v∷ []))
    returnTC (just (x , y))
  getBoundary _ = returnTC nothing

solve-macro : Term → TC ⊤
solve-macro hole =
  withNormalisation true do
  goal ← inferType hole >>= normalise

  just (lhs , rhs) ← getBoundary goal
    where nothing → typeError (strErr "Can't solve: " ∷ termErr goal ∷ [])
  unify hole (def (quote solution) (build-expr lhs v∷ build-expr rhs v∷ def (quote refl) [] v∷ []))

simplify-macro : Nat → Term → TC ⊤
simplify-macro n hole = do
  tm ← quoteTC n
  unify hole (def (quote embed) (def (quote nf) (build-expr tm v∷ []) v∷ []))

macro
  solve : Term → TC ⊤
  solve = solve-macro

  simplify : Nat → Term → TC ⊤
  simplify n = simplify-macro n
```

## Demo
```agda
private
  test : Nat → Nat → Nat
  test x y = suc (suc (x + y))
```

