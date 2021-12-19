open import 1Lab.Univalence.SIP
open import 1Lab.Reflection
open import 1Lab.Type.Sigma
open import 1Lab.Univalence
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

module 1Lab.Univalence.SIP.Auto where

open import Agda.Builtin.Reflection
  renaming ( bindTC to _>>=_
           ; catchTC to infixr 8 _<|>_
           )
  hiding (Type)

private
  getShape : Term → TC (Term × Term × Term)
  getShape (def (quote Structure) (arg _ ℓ₁ ∷ arg _ ℓ₂ ∷ _ ∷ arg _ shape ∷ _)) =
    reduce shape >>= λ where
      shep → returnTC (ℓ₁ , ℓ₂ , shep)
  getShape shape =  
    typeError (termErr shape
             ∷ strErr " is not a saturated application of Structure"
             ∷ [])

private
  constantShape : ∀ {ℓ'} (ℓ : Level) (A : Type ℓ') → (Type ℓ → Type ℓ')
  constantShape _ A _ = A

  pointedShape : (ℓ : Level) → Type ℓ → Type ℓ
  pointedShape _ X = X

  productShape : ∀ {ℓ₀ ℓ₁} (ℓ : Level)
    → (Type ℓ → Type ℓ₀) → (Type ℓ → Type ℓ₁) → Type ℓ → Type (ℓ₀ ⊔ ℓ₁)
  productShape _ A₀ A₁ X = A₀ X × A₁ X

  functionShape :  ∀ {ℓ₀ ℓ₁} (ℓ : Level)
    → (Type ℓ → Type ℓ₀) → (Type ℓ → Type ℓ₁) → Type ℓ → Type (ℓ₀ ⊔ ℓ₁)
  functionShape _ A₀ A₁ X = A₀ X → A₁ X

parseShape : Nat → Term → Term → Term → TC Term
parseShape zero “ℓ₁” “ℓ₂” “shape” =
  typeError (strErr "ran out of fuel!" ∷ [])

parseShape (suc fuel) “ℓ₁” “ℓ₂” “shape” =
  parseConstant
  <|> parsePointed
  <|> parseProduct
  <|> parseFunction
  <|> typeError (termErr “shape” ∷ strErr " is not of a known univalent structure shape!" ∷ [])
  where
    parseConstant : TC Term
    parseConstant =
      newMeta (def (quote Type) (varg “ℓ₂” ∷ [])) >>= λ ty →
      unify “shape” (def (quote constantShape) (“ℓ₁” v∷ ty v∷ [])) >>= λ _ →
      returnTC (con (quote s-const) (ty v∷ []))

    parsePointed : TC Term
    parsePointed =
      unify “shape” (def (quote pointedShape) (“ℓ₁” v∷ [])) >>= λ _ →
      unify “ℓ₁” “ℓ₂” >>= λ _ → 
      returnTC (con (quote s∙) [])

    parseProduct : TC Term
    parseProduct =
      newMeta (quoteTerm Level) >>= λ ℓ0 →
      newMeta (quoteTerm Level) >>= λ ℓ1 →
      newMeta (“ “Type” “ℓ₁” ↦ “Type” ℓ0 ”) >>= λ A₀ →
      newMeta (“ “Type” “ℓ₁” ↦ “Type” ℓ1 ”) >>= λ A₁ →
      unify “shape” (def (quote productShape) (“ℓ₁” v∷ A₀ v∷ A₁ v∷ [])) >>= λ _ →
      parseShape fuel “ℓ₁” ℓ0 A₀ >>= λ d₀ →
      parseShape fuel “ℓ₁” ℓ1 A₁ >>= λ d₁ →
      returnTC (con (quote _s×_) (d₀ v∷ d₁ v∷ []))

    parseFunction : TC Term
    parseFunction =
      newMeta (quoteTerm Level) >>= λ ℓ0 →
      newMeta (quoteTerm Level) >>= λ ℓ1 →
      newMeta (“ “Type” “ℓ₁” ↦ “Type” ℓ0 ”) >>= λ A₀ →
      newMeta (“ “Type” “ℓ₁” ↦ “Type” ℓ1 ”) >>= λ A₁ →
      unify “shape” (def (quote functionShape) (“ℓ₁” v∷ A₀ v∷ A₁ v∷ [])) >>= λ _ →
      parseShape fuel “ℓ₁” ℓ0 A₀ >>= λ d₀ →
      parseShape fuel “ℓ₁” ℓ1 A₁ >>= λ d₁ →
      unify “ℓ₂” (def (quote _⊔_) (ℓ0 v∷ ℓ1 v∷ [])) >>= λ _ →
      returnTC (con (quote _s→_) (d₀ v∷ d₁ v∷ []))

macro
  autoStructure : Term → TC ⊤
  autoStructure goal = do
    type ← inferType goal
    (l1 , l2 , shape) ← getShape type
    desc ← parseShape 100 l1 l2 shape
    unify goal (def (quote tm→Structure) (desc v∷ []))

  autoUnivalentStr : Term → Term → TC ⊤
  autoUnivalentStr str goal = do
    str ← inferType str
    (l1 , l2 , shape) ← getShape str
    desc ← parseShape 100 l1 l2 shape
    unify goal (def (quote tm→Structure-univalent) (desc v∷ []))
