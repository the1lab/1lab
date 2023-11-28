<!--
```agda
open import 1Lab.Type

open import Data.String.Base
open import Data.Float.Base
open import Data.Char.Base
open import Data.List.Base
open import Data.Word.Base

open import Meta.Append
```
-->

```agda
module Data.String.Show where
```

# The Show class

```agda
record Show {ℓ} (A : Type ℓ) : Type ℓ where
  field
    -- Convert a value into a string suitable for printing.
    show      : A → String

    -- Convert a value into a string, when this value appears as the
    -- second component in a pair.
    show-snd : A → String

open Show ⦃ ... ⦄ public

default-show : ∀ {ℓ} {A : Type ℓ} → (A → String) → Show A
default-show s = record { show = s ; show-snd = s }

private module P where primitive
  primShowChar       : Char   → String
  primShowString     : String → String
  primShowNat        : Nat    → String
  primShowFloat      : Float  → String

instance
  Show-Word64 : Show Word64
  Show-Word64 = default-show λ x → P.primShowNat (word64→nat x)

  Show-Nat : Show Nat
  Show-Nat = default-show P.primShowNat

  Show-String : Show String
  Show-String = default-show P.primShowString

  Show-Char : Show Char
  Show-Char = default-show P.primShowChar

  Show-Float : Show Float
  Show-Float = default-show P.primShowFloat

instance
  Show-Σ
    : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
    → ⦃ _ : Show A ⦄ ⦃ _ : ∀ {x} → Show (B x) ⦄
    → Show (Σ A B)
  Show-Σ .show (x , y) = "(" <> show x <> " , " <> show-snd y <> ")"
  Show-Σ .show-snd (x , y) = show x <> " , " <> show-snd y

  Show-List : ∀ {ℓ} {A : Type ℓ} ⦃ _ : Show A ⦄ → Show (List A)
  Show-List {A = A} = default-show λ xs → "[" <> go xs <> "]" where
    go : List A → String
    go []       = ""
    go (x ∷ []) = show x
    go (x ∷ xs) = show x <> " , " <> go xs
```
