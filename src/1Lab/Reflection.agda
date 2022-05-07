open import 1Lab.Type.Sigma
open import 1Lab.Equiv
open import 1Lab.Type
open import Data.Bool
open import Data.List

module 1Lab.Reflection where

open import Agda.Builtin.List public
open import Agda.Builtin.String public
open import Agda.Builtin.Maybe public
open import Agda.Builtin.Reflection
  renaming ( bindTC to _>>=_
           ; catchTC to infixl 8 _<|>_
           )
  hiding (Type)
  public

_>>_ : ∀ {a b} {A : Type a} {B : Type b} → TC A → TC B → TC B
f >> g = f >>= λ _ → g

Fun : ∀ {ℓ ℓ'} → Type ℓ → Type ℓ' → Type (ℓ ⊔ ℓ')
Fun A B = A → B

idfun : ∀ {ℓ} (A : Type ℓ) → A → A
idfun A x = x

equivFun : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → A ≃ B → A → B
equivFun (f , e) = f

equivInv : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → A ≃ B → B → A
equivInv (f , e) = equiv→inverse e

equivSec : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (e : A ≃ B)
         → _
equivSec (f , e) = equiv→section e

equivRet : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (e : A ≃ B)
         → _
equivRet (f , e) = equiv→retraction e

newMeta : Term → TC Term
newMeta = checkType unknown

varg : {ℓ : _} {A : Type ℓ} → A → Arg A
varg = arg (arg-info visible (modality relevant quantity-ω))

vlam : String → Term → Term
vlam nam body = lam visible (abs nam body)

pattern _v∷_ t xs = arg (arg-info visible (modality relevant quantity-ω)) t ∷ xs
pattern _h∷_ t xs = arg (arg-info hidden (modality relevant quantity-ω)) t ∷ xs

infixr 30 _v∷_ _h∷_

“_↦_” : Term → Term → Term
“_↦_” x y = def (quote Fun) (x v∷ y v∷ [])

“Type” : Term → Term
“Type” l = def (quote Type) (l v∷ [])

tApply : Term → List (Arg Term) → Term
tApply t l = def (quote id) (t v∷ l)

tStrMap : Term → Term → Term
tStrMap A f = def (quote Σ-map₂) (f v∷ A v∷ [])

tStrProj : Term → Name → Term
tStrProj A sfield = tStrMap A (def sfield [])

data Vec {ℓ} (A : Type ℓ) : Nat → Type ℓ where
  [] : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

makeVarsFrom : {n : Nat} → Nat → Vec Term n
makeVarsFrom {zero} k = []
makeVarsFrom {suc n} k = var (n + k) [] ∷ (makeVarsFrom k)

iter : ∀ {ℓ} {A : Type ℓ} → Nat → (A → A) → A → A
iter zero f = id
iter (suc n) f = f ∘ iter n f

getName : Term → Maybe Name
getName (def x _) = just x
getName (con x _) = just x
getName _ = nothing

_name=?_ : Name → Name → Bool
x name=? y = primQNameEquality x y

findName : Term → TC Name
findName (def nm _) = returnTC nm
findName (lam hidden (abs _ t)) = findName t
findName (meta m _) = blockOnMeta m
findName t = typeError (strErr "The projections in a field descriptor must be record selectors: " ∷ termErr t ∷ [])

_visibility=?_ : Visibility → Visibility → Bool
visible visibility=? visible = true
hidden visibility=? hidden = true
instance′ visibility=? instance′ = true
_ visibility=? _ = false

-- [TODO: Reed M, 06/05/2022] We don't actually use any fancy modalities
-- anywhere AFAICT, so let's ignore those.
_arginfo=?_ : ArgInfo → ArgInfo → Bool
arg-info v₁ m₁ arginfo=? arg-info v₂ m₂ = (v₁ visibility=? v₂)

arg=? : ∀ {a} {A : Type a} → (A → A → Bool) → Arg A → Arg A → Bool
arg=? eq=? (arg i₁ x) (arg i₂ y) = and (i₁ arginfo=? i₂) (eq=? x y)

-- We want to compare terms up to α-equivalence, so we ignore binder
-- names.
abs=? : ∀ {a} {A : Type a} → (A → A → Bool) → Abs A → Abs A → Bool
abs=? eq=? (abs _ x) (abs _ y) = eq=? x y 

{-# TERMINATING #-}
-- [TODO: Reed M, 06/05/2022] Finish this

_term=?_ : Term → Term → Bool
var nm₁ args₁ term=? var nm₂ args₂ = and (nm₁ == nm₂) (all=? (arg=? _term=?_) args₁ args₂)
con c₁ args₁ term=? con c₂ args₂ = and (c₁ name=? c₂) (all=? (arg=? _term=?_) args₁ args₂)
def f₁ args₁ term=? def f₂ args₂ = and (f₁ name=? f₂) (all=? (arg=? _term=?_) args₁ args₂)
lam v₁ t₁ term=? lam v₂ t₂ = and (v₁ visibility=? v₂) (abs=? _term=?_ t₁ t₂)
pat-lam cs₁ args₁ term=? pat-lam cs₂ args₂ = false
pi a₁ b₁ term=? pi a₂ b₂ = and (arg=? _term=?_ a₁ a₂) (abs=? _term=?_ b₁ b₂)
agda-sort s term=? t₂ = false
lit l term=? t₂ = false
meta x x₁ term=? t₂ = false
unknown term=? t₂ = false
_ term=? _ = false

debug! : ∀ {ℓ} {A : Type ℓ} → Term → TC A
debug! tm = typeError (strErr "[DEBUG]: " ∷ termErr tm ∷ [])
