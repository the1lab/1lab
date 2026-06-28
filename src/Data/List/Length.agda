open import 1Lab.Path
open import 1Lab.Type

open import Data.Maybe.Base
open import Data.List.Base
open import Data.Dec.Base
open import Data.Fin.Base
open import Data.Nat.Base as Nat
open import Data.Id.Base
open import Data.Irr

open import Meta.Idiom

module Data.List.Length where

private variable
  ℓ : Level
  A B C : Type ℓ
  xs ys : List A
  n k : Nat

data Length {ℓ} {A : Type ℓ} : List A → Nat → Type ℓ where
  zero : Length [] zero
  suc  : ∀ {x xs n} → Length xs n → Length (x ∷ xs) (suc n)

instance
  Length-zero : Length {A = A} [] zero
  Length-zero = zero

  Length-suc : ∀ {x} → ⦃ Length xs n ⦄ → Length (x ∷ xs) (suc n)
  Length-suc ⦃ l ⦄ = suc l

  Length-length : ∀ {xs : List A} → Length xs (length xs)
  Length-length {xs = []} = zero
  Length-length {xs = x ∷ xs} = suc Length-length
  {-# INCOHERENT Length-length #-}

  Length-dec : ∀ {xs : List A} → Dec (Length xs n)
  Length-dec {n = zero} {xs = []} =  yes $ Length-zero
  Length-dec {n = suc n} {xs = x ∷ xs} =  caseᵈ Length xs n of λ where
    (yes l) → yes $ Length-suc ⦃ l ⦄
    (no ¬l) → no λ { (suc l) → ¬l l }
  Length-dec {n = suc n} {xs = []} = no λ ()
  Length-dec {n = zero} {xs = x ∷ xs} = no λ ()


len-uncons : ∀ {xs n x} → Length {A = A} (x ∷ xs) (suc n) → Length xs n
len-uncons (suc l) = l

has-lengthᵢ : ∀ {xs : List A} {n : Nat} → Length xs n → length xs ≡ᵢ n
has-lengthᵢ {xs = []} {n = zero} len = reflᵢ
has-lengthᵢ {xs = x ∷ xs} {n = suc n} len = apᵢ suc $ has-lengthᵢ $ len-uncons len

has-length : ∀ {xs : List A} {n : Nat} → Irr (Length xs n) → length xs ≡ n
has-length l = Id≃path.to $ has-lengthᵢ (recover l)

len-++ : Length xs n → Length ys k → Length (xs ++ ys) (n + k)
len-++ zero l' = l'
len-++ (suc l) l' = Length-suc ⦃ len-++ l l' ⦄

len-tabulate : ∀ {n} → (v : Fin n → A) → Length (tabulate v) n
len-tabulate {n = zero} v = zero
len-tabulate {n = suc _} v = suc (len-tabulate $ v ∘ fsuc)

len-map : ∀ {f : A → B} → Length xs n → Length (f <$> xs) n
len-map {xs = []} {n = zero} _ = zero
len-map {xs = x ∷ xs} {n = suc n} (suc l) = suc $ len-map l

len-zip-with
  : {f : A → B → C} → Length xs n → Length ys n → Length (zip-with f xs ys) n
len-zip-with {xs = []} zero _ = zero
len-zip-with {xs = _ ∷ _} {ys = []} _ zero =  zero 
len-zip-with {xs = x ∷ xs} {ys =  x₁ ∷ ys} (suc l) (suc l') = suc $ len-zip-with l l'

len-zip : Length xs n → Length ys n → Length (zip xs ys) n
len-zip = len-zip-with
