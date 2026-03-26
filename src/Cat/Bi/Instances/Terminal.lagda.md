<!--
```agda
open import Cat.Instances.Shape.Terminal
open import Cat.Functor.Closed
open import Cat.Bi.Solver
open import Cat.Bi.Base
open import Cat.Prelude

import Cat.Bi.Reasoning as Br
import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Bi.Instances.Terminal where
```

# The terminal bicategory {defines="terminal-bicategory"}

The **terminal bicategory** is the [[bicategory]] with a single object, and a trivial
category of morphisms.

<!--
```agda
private
  variable
    o h ℓ : Level
    C : Prebicategory o h ℓ

  module Pb = Prebicategory
  module Pf = Pseudofunctor
  module Lf = Lax-functor

  open _=>_
```
-->

```agda
⊤Bicat : Prebicategory lzero lzero lzero
⊤Bicat .Pb.Ob               = ⊤
⊤Bicat .Pb.Hom _ _          = ⊤Cat
⊤Bicat .Pb.id               = tt
⊤Bicat .Pb.compose          = Curry !F
⊤Bicat .Pb.unitor-l         = path→iso !F-unique₂
⊤Bicat .Pb.unitor-r         = path→iso !F-unique₂
⊤Bicat .Pb.associator       = path→iso !F-unique₂
⊤Bicat .Pb.triangle _ _     = refl
⊤Bicat .Pb.pentagon _ _ _ _ = refl
```

There is a (unique) pseudofunctor from any bicategory $\bf{C}$ into the
terminal bicategory.

```agda
!P : Pseudofunctor C ⊤Bicat
!P .Pf.lax .Lf.P₀ _ = tt
!P .Pf.lax .Lf.P₁   = !F
!P .Pf.lax .Lf.compositor .η _              = tt
!P .Pf.lax .Lf.compositor .is-natural _ _ _ = refl
!P .Pf.lax .Lf.unitor        = tt
!P .Pf.lax .Lf.hexagon _ _ _ = refl
!P .Pf.lax .Lf.right-unit _  = refl
!P .Pf.lax .Lf.left-unit _   = refl
!P .Pf.unitor-inv       = ⊤Cat-is-pregroupoid _
!P .Pf.compositor-inv _ = ⊤Cat-is-pregroupoid _
```

Conversely, pseudofunctors $\top \to \bf{C}$ are determined by their
behaviour on a single object.

```agda
module _ (X : Prebicategory.Ob C) where
  open Prebicategory C
  private module CH {A} {B} = Cr (Hom A B)

  !ConstP : Pseudofunctor ⊤Bicat C
  !ConstP .Pf.lax .Lf.P₀ _ = X
  !ConstP .Pf.lax .Lf.P₁   = !Const id
  !ConstP .Pf.lax .Lf.compositor .η _              = λ← id
  !ConstP .Pf.lax .Lf.compositor .is-natural _ _ _ =
    CH.cdr (compose.◆-id) ∙ CH.id-comm
  !ConstP .Pf.lax .Lf.unitor        = Hom.id
  !ConstP .Pf.lax .Lf.hexagon _ _ _ = bicat! C
  !ConstP .Pf.lax .Lf.right-unit _  = bicat! C
  !ConstP .Pf.lax .Lf.left-unit _   = bicat! C
  !ConstP .Pf.unitor-inv       = CH.id-invertible
  !ConstP .Pf.compositor-inv _ = CH.iso→invertible (Br.λ≅ C CH.Iso⁻¹)
```
