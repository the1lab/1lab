open import 1Lab.Path
open import 1Lab.Type

module 1Lab.Rewrite where

data _≡rw_ {ℓ} {A : Type ℓ} (x : A) : A → SSet ℓ where
  idrw : x ≡rw x

{-# BUILTIN REWRITE _≡rw_ #-}

postulate
  make-rewrite : ∀ {ℓ} {A : Type ℓ} {x y : A} → Path A x y → x ≡rw y
