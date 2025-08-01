<!--
```agda
open import Cat.Diagram.Colimit.Base
open import Cat.Functor.Naturality
open import Cat.Functor.Properties
open import Cat.Diagram.Initial
open import Cat.Functor.Adjoint
open import Cat.Functor.Compose
open import Cat.Instances.Comma
open import Cat.Functor.Base
open import Cat.Prelude hiding (J)

import Cat.Functor.Reasoning.FullyFaithful as FFR
import Cat.Functor.Reasoning as Func
import Cat.Natural.Reasoning
import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Functor.Adjoint.Colimit where
```
<!--
```agda
private variable
  o ℓ : Level
  C D J : Precategory o ℓ
module _ (U : Functor C D) (ff : is-fully-faithful U) {diagram : Functor J C} (colim : Colimit {C = D} (U F∘ diagram)) where
  open Colimit colim
  private
    module C = Precategory C
    module D = Cr D
    module U = FFR U ff
    module diagram = Functor diagram
    module colim = make-is-colimit (unmake-colimit (Colimit.has-colimit colim))
  open make-is-colimit
```
-->

### Free objects and colimits


```agda
  module _ (ob : Free-object U coapex) where
    open module ob = Free-object ob
    free-object→make-is-colimit : make-is-colimit diagram free
    free-object→make-is-colimit .ψ j = U.from (unit D.∘ colim.ψ j)
    free-object→make-is-colimit .commutes {x} {y} f = U.ipushr (colim.commutes f)
    free-object→make-is-colimit .universal {x} eta p = fold $ colim.universal (U.₁ ⊙ eta) (U.collapse ⊙ p)
    free-object→make-is-colimit .factors {j} eta p =
      fold (colim.universal _ _) C.∘ U.from (unit D.∘ colim.ψ j) ≡⟨ U.pouncer (D.pulll ob.commute) ⟩
      U.from (colim.universal _ _ D.∘ colim.ψ j)                 ≡⟨ U.fromn't (colim.factors (U.₁ ⊙ eta) (U.collapse ⊙ p)) ⟩
      eta j                                                      ∎
    free-object→make-is-colimit .unique {y} eta p other p' =
      ob.unique {y} other $ colim.unique (U.₁ ⊙ eta) (U.collapse ⊙ p) (U.₁ other D.∘ unit) λ j → sym (D.assoc _ _ _) ∙ U.unwhackr (p' j)

    free-object→is-colimit : is-colimit diagram free _
    free-object→is-colimit = to-is-colimit free-object→make-is-colimit

    free-object→colimit : Colimit diagram
    free-object→colimit = to-colimit free-object→is-colimit
```
