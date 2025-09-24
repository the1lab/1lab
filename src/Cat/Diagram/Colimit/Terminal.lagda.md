<!--
```agda
open import Cat.Diagram.Limit.Initial
open import Cat.Diagram.Colimit.Base
open import Cat.Diagram.Limit.Base
open import Cat.Diagram.Terminal
open import Cat.Diagram.Duals
open import Cat.Morphism
open import Cat.Prelude

import Cat.Reasoning as Cat

open make-is-colimit
open Terminal
```
-->

```agda
module Cat.Diagram.Colimit.Terminal {o ℓ} {C : Precategory o ℓ} where
```

# Terminal objects as colimits

This module provides a characterisation of [[terminal objects]] as
[[*colimits*]] rather than as [[limits]]. Namely, while an terminal
object is the limit of the empty diagram, it is the *co*limit of the
identity functor, considered as a diagram.

Proving this consists of reversing the arrows in the proof that
[[initial objects are limits]].

```agda
Id-colimit→Terminal : Colimit (Id {C = C}) → Terminal C
Id-colimit→Terminal L = Coinitial→terminal
  $ Id-limit→Initial
  $ natural-iso→limit (path→iso Id^op≡Id)
  $ Colimit→Co-limit L

Terminal→Id-colimit : Terminal C → Colimit (Id {C = C})
Terminal→Id-colimit terminal = Co-limit→Colimit
  $ natural-iso→limit (path→iso (sym Id^op≡Id))
  $ Initial→Id-limit
  $ Terminal→Coinitial terminal
```
