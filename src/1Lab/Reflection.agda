open import 1Lab.Type.Sigma
open import 1Lab.Equiv
open import 1Lab.Type

module 1Lab.Reflection where

open import Agda.Builtin.List public
open import Agda.Builtin.String public
open import Agda.Builtin.Reflection
  renaming ( bindTC to _>>=_
           ; catchTC to infixl 8 _<|>_
           )
  hiding (Type)
  public

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
