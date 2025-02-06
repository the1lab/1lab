<!--
```agda
open import 1Lab.Prelude

open import Cat.Instances.Shape.Terminal
open import Cat.Univalent
open import Cat.Bi.Base

import Cat.Reasoning
```
-->

```agda
module Cat.Bi.Instances.Terminal where
```

# The Terminal Bicategory

The **terminal bicategory** is the category with a single object, and a trivial
category of morphisms.

```agda
open Prebicategory

⊤Catᵇ : Prebicategory lzero lzero lzero
⊤Catᵇ .Ob = ⊤
⊤Catᵇ .Hom x x₁ = ⊤Cat
⊤Catᵇ .Prebicategory.id = tt
⊤Catᵇ .compose = !F
⊤Catᵇ .unitor-l = path→iso !F-unique₂
⊤Catᵇ .unitor-r = path→iso !F-unique₂
⊤Catᵇ .associator = path→iso !F-unique₂
⊤Catᵇ .triangle _ _ = refl
⊤Catᵇ .pentagon _ _ _ _ = refl
```
