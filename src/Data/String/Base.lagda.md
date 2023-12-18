<!--
```agda
open import 1Lab.Type

open import Data.Maybe.Base
open import Data.Char.Base
open import Data.List.Base
open import Data.Dec.Base
open import Data.Id.Base

open import Meta.Append
```
-->

```agda
module Data.String.Base where
```

# Primitive: Characters and strings

We bind the big list of Agda primitives for interacting with characters
and strings.

```agda
postulate String : Type
{-# BUILTIN STRING String #-}

private module P where primitive
  primStringUncons   : String → Maybe (Char × String)
  primStringToList   : String → List Char
  primStringFromList : List Char → String
  primStringAppend   : String → String → String
  primStringToListInjective : ∀ a b → primStringToList a ≡ᵢ primStringToList b → a ≡ᵢ b
```

```agda
open P public renaming
  ( primStringUncons   to uncons-string
  ; primStringToList   to string→list
  ; primStringFromList to list→string
  )
  hiding ( primStringAppend ; primStringToListInjective )
```

```agda
record From-string {a} (A : Type a) : Type (lsuc a) where
  field
    Constraint  : String → Type a
    from-string : (s : String) {{_ : Constraint s}} → A

open From-string {{...}} public using (from-string)

{-# DISPLAY From-string.from-string _ s = from-string s #-}
{-# BUILTIN FROMSTRING from-string #-}

instance
  From-string-String : From-string String
  From-string-String .From-string.Constraint _ = ⊤
  From-string-String .from-string s = s

  Append-String : Append String
  Append-String ._<>_   = P.primStringAppend
  Append-String .mempty = ""

{-# DISPLAY P.primStringAppend x y = x <> y #-}

instance
  Discrete-String : Discrete String
  Discrete-String = Discrete-inj' _ (P.primStringToListInjective _ _)
```
