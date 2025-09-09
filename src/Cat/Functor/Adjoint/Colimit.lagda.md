<!--
```agda
open import Cat.Diagram.Colimit.Base
open import Cat.Functor.Properties
open import Cat.Functor.Adjoint
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Functor.Reasoning.FullyFaithful as FFR
import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Functor.Adjoint.Colimit {o ℓ o' ℓ' o'' ℓ''}
  {C : Precategory o ℓ} {D : Precategory o'  ℓ'} {J : Precategory o'' ℓ''}
  (F : Functor C D) (ff : is-fully-faithful F) {diagram : Functor J C}
  (colim : Colimit {C = D} (F F∘ diagram))
  (ob : Free-object F (Colimit.coapex colim)) where
```
<!--
```agda
open Colimit colim
private
  module C = Precategory C
  module D = Cr D
  module F = FFR F ff
  module diagram = Functor diagram
  module colim = make-is-colimit (unmake-colimit (Colimit.has-colimit colim))
  open module ob = Free-object ob
open make-is-colimit
```
-->

### Free objects and colimits

Suppose that $F:\cC\to\cD$ and we have colimit with coapex $c$ of the
diagram $G:\cJ\to\cC$ composed with $F$ in $\cD$. If there is an
adjunction $L\dashv F$ then we have a colimit of the diagram $L\circ
F\circ G$ in $C$ as [[left adjoints preserve colimits]]. Furthermore, if
$F$ is fully faithful (which is to say this is the data of a
[[reflective subcategory]]) then $L(c)$ is a colimit of $G$.


Now, what if we don't have such an adjunction, and merely a [[free
object]] for the coapex relative to $F$? Free objects are effectively a
partial left adjoint, and thus should likewise be "cocontinuous".
Indeed, if $F$ is fully faithful, and we have a free object on our
coapex relative to $F$ then it is a colimit of $G$.

```agda
free-object→make-is-colimit : make-is-colimit diagram free
free-object→make-is-colimit = record where
  ψ j = F.from (unit D.∘ colim.ψ j)
  universal {x} eta p = fold $ colim.universal (F.₁ ⊙ eta) (F.collapse ⊙ p)

  commutes {x} {y} f = F.ipushr (colim.commutes f)
  factors {j} eta p =
    fold (colim.universal _ _) C.∘ F.from (unit D.∘ colim.ψ j) ≡⟨ F.pouncer (D.pulll ob.commute) ⟩
    F.from (colim.universal _ _ D.∘ colim.ψ j)                 ≡⟨ F.fromn't (colim.factors (F.₁ ⊙ eta) (F.collapse ⊙ p)) ⟩
    eta j                                                      ∎
  unique {y} eta p other p' = ob.unique {y} other $
    colim.unique (F.₁ ⊙ eta) (F.collapse ⊙ p) (F.₁ other D.∘ unit)
      λ j → sym (D.assoc _ _ _) ∙ F.unwhackr (p' j)

free-object→is-colimit : is-colimit diagram free _
free-object→is-colimit = to-is-colimit free-object→make-is-colimit

free-object→colimit : Colimit diagram
free-object→colimit = to-colimit free-object→is-colimit
```
