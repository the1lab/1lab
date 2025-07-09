<!--
```agda
open import 1Lab.Prelude

open import Homotopy.Pushout
```
-->

```agda
module Homotopy.Join where
```

# The join of types {defines="join-of-types"}

<!--
```agda
private variable
  ℓ ℓ' : Level
  X Y Z : Type ℓ
```
-->

The **join** of two types $A$ and $B$ is the pushout under the diagram
$$A \ot (A \times B) \to B$$.

```agda
_∗_ : Type ℓ → Type ℓ' → Type (ℓ ⊔ ℓ')
A ∗ B = Pushout (A × B) fst snd

pattern join x y i = glue (x , y) i
```

<!--
```agda
open Homotopy.Pushout using (inl ; inr) public
```
-->
