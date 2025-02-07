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

# The terminal bicategory {defines="terminal-bicategory"}

The **terminal bicategory** is the [[bicategory]] with a single object, and a trivial
category of morphisms.

```agda
open Prebicategory

⊤Bicat : Prebicategory lzero lzero lzero
⊤Bicat .Ob = ⊤
⊤Bicat .Hom _ _ = ⊤Cat
⊤Bicat .Prebicategory.id = tt
⊤Bicat .compose = !F
⊤Bicat .unitor-l = path→iso !F-unique₂
⊤Bicat .unitor-r = path→iso !F-unique₂
⊤Bicat .associator = path→iso !F-unique₂
⊤Bicat .triangle _ _ = refl
⊤Bicat .pentagon _ _ _ _ = refl
```
