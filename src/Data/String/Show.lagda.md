<!--
```agda
open import 1Lab.Type

open import Data.Reflection.Fixity
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
record ShowS : Type where
  constructor showS
  field
    unshowS : String → String

instance
  From-string-ShowS : From-string ShowS
  From-string-ShowS .From-string.Constraint _ = ⊤
  From-string-ShowS .from-string s = showS (s <>_)

  Append-ShowS : Append ShowS
  Append-ShowS .Append.mempty                     = showS id
  Append-ShowS .Append._<>_ (showS k1) (showS k2) = showS (k1 ∘ k2)

record Show {ℓ} (A : Type ℓ) : Type ℓ where
  field
    -- Convert a value into a difference-string, using the given
    -- precedence to determine whether or not parentheses are necessary.
    shows-prec : Precedence → A → ShowS

    -- Convert a value into a string suitable for printing.
    show      : A → String

open Show ⦃ ... ⦄ public

default-show : ∀ {ℓ} {A : Type ℓ} → (A → String) → Show A
default-show s = record
  { shows-prec = λ _ x → from-string (s x)
  ; show       = s
  }

show-parens : Bool → ShowS → ShowS
show-parens true  x = "(" <> x <> ")"
show-parens false x = x

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
```
