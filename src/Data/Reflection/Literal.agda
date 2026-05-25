open import 1Lab.Path.IdentitySystem
open import 1Lab.Path
open import 1Lab.Type

open import Data.Reflection.Meta
open import Data.Reflection.Name
open import Data.String.Base
open import Data.Float.Base
open import Data.Char.Base
open import Data.Dec.Base
open import Data.Nat.Base
open import Data.Id.Base

module Data.Reflection.Literal where

data Literal : Type where
  nat    : (n : Nat)    → Literal
  float  : (x : Float)  → Literal
  char   : (c : Char)   → Literal
  string : (s : String) → Literal
  name   : (x : Name)   → Literal
  meta   : (x : Meta)   → Literal

{-# BUILTIN AGDALITERAL   Literal #-}
{-# BUILTIN AGDALITNAT    nat     #-}
{-# BUILTIN AGDALITFLOAT  float   #-}
{-# BUILTIN AGDALITCHAR   char    #-}
{-# BUILTIN AGDALITSTRING string  #-}
{-# BUILTIN AGDALITQNAME  name    #-}
{-# BUILTIN AGDALITMETA   meta    #-}

instance
  Discrete-Literal : Discrete Literal
  Discrete-Literal = Discreteᵢ→discrete λ where
    (nat n) (nat n₁) → case n ≡ᵢ? n₁ of λ where
      (yes reflᵢ) → yes reflᵢ
      (no ¬p) → no λ { reflᵢ → ¬p reflᵢ }
    (float x) (float x₁) → case x ≡ᵢ? x₁ of λ where
      (yes reflᵢ) → yes reflᵢ
      (no ¬p) → no λ { reflᵢ → ¬p reflᵢ }
    (char c) (char c₁) → case c ≡ᵢ? c₁ of λ where
      (yes reflᵢ) → yes reflᵢ
      (no ¬p) → no λ { reflᵢ → ¬p reflᵢ }
    (string s) (string s₁) → case s ≡ᵢ? s₁ of λ where
      (yes reflᵢ) → yes reflᵢ
      (no ¬p) → no λ { reflᵢ → ¬p reflᵢ }
    (name x) (name x₁) → case x ≡ᵢ? x₁ of λ where
      (yes reflᵢ) → yes reflᵢ
      (no ¬p) → no λ { reflᵢ → ¬p reflᵢ }
    (meta x) (meta x₁) → case x ≡ᵢ? x₁ of λ where
      (yes reflᵢ) → yes reflᵢ
      (no ¬p) → no λ { reflᵢ → ¬p reflᵢ }

    (nat n) (float x)   → no (λ ())
    (nat n) (char c)    → no (λ ())
    (nat n) (string s)  → no (λ ())
    (nat n) (name x)    → no (λ ())
    (nat n) (meta x)    → no (λ ())

    (float x) (nat n)    → no (λ ())
    (float x) (char c)   → no (λ ())
    (float x) (string s) → no (λ ())
    (float x) (name x₁)  → no (λ ())
    (float x) (meta x₁)  → no (λ ())

    (char c) (nat n)    → no (λ ())
    (char c) (float x)  → no (λ ())
    (char c) (string s) → no (λ ())
    (char c) (name x)   → no (λ ())
    (char c) (meta x)   → no (λ ())

    (string s) (nat n)     → no (λ ())
    (string s) (float x)   → no (λ ())
    (string s) (char c)    → no (λ ())
    (string s) (name x)    → no (λ ())
    (string s) (meta x)    → no (λ ())

    (name x) (nat n)    → no (λ ())
    (name x) (float x₁) → no (λ ())
    (name x) (char c)   → no (λ ())
    (name x) (string s) → no (λ ())
    (name x) (meta x₁)  → no (λ ())

    (meta x) (nat n)    → no (λ ())
    (meta x) (float x₁) → no (λ ())
    (meta x) (char c)   → no (λ ())
    (meta x) (string s) → no (λ ())
    (meta x) (name x₁)  → no (λ ())
