<!--
```agda
open import Cat.Instances.Shape.Terminal
open import Cat.Functor.Adjoint.Cofree
open import Cat.Diagram.Colimit.Base
open import Cat.Diagram.Limit.Base
open import Cat.Instances.Functor
open import Cat.Functor.Constant
open import Cat.Functor.Adjoint
open import Cat.Diagram.Duals
open import Cat.Prelude hiding (J)

import Cat.Functor.Reasoning
import Cat.Reasoning
```
-->

```agda
module Cat.Functor.Adjoint.ConstD {o ℓ} {C : Precategory o ℓ}  where
```
<!--
```agda
open _=>_
private
  variable
    o' ℓ' : Level
    J D : Precategory o' ℓ'
    F G : Functor J C
  open module C = Cat.Reasoning C

```
-->

# (Partial) adjoints to the diagonal functor

Suppose that $x$ is a free object with respect to $\Delta_\cCJ$ and $F$,
then $x$ is a colimit of $F$.

```agda
Δfree→colim : Free-object ConstD F → Colimit F
Δfree→colim {F} free-ob = to-colimit $ to-is-colimit $ record where
  open module free = Free-object free-ob
  ψ = unit .η
  commutes {j} {k} f = unit .is-natural _ _ f ∙ idl _
  universal {x} eta commutes = fold {x} (NT eta λ j k f → commutes f ∙ sym (idl _))
  factors {j} eta p = commute {f = NT eta λ x y f → p f ∙ sym (idl _)} ηₚ j
  unique eta p other commutes = unique other $ ext commutes

colim→Δfree : Colimit F → Free-object ConstD F
colim→Δfree {F} colim = record where
  open module colim = Colimit colim using (coapex; cocone)
  open make-is-colimit (unmake-colimit colim.has-colimit)
  free = coapex
  unit = cocone
  fold eta = universal (eta .η) λ f → eta .is-natural _ _ f ∙ idl _
  commute {x} {nt} = ext λ j → factors (nt .η) λ _ → nt .is-natural _ _ _ ∙ idl _
  unique {x} {nt} g p = unique (nt .η) (λ _ → nt .is-natural _ _ _ ∙ idl _) g λ j → p ηₚ  j

Δcofree→lim : Cofree-object ConstD F → Limit F
lim→Δcofree : Limit F → Cofree-object ConstD F
```

<!--
```agda
-- this is better worked out explicitly
Δcofree→lim {F} cofree-ob = to-limit $ to-is-limit $ record where
  open module cofree = Cofree-object cofree-ob
  ψ = counit .η
  commutes {j} {k} f = (sym $ counit .is-natural _ _ f) ∙ idr _
  universal {x} eta commutes = unfold {x} $ NT eta λ j k f → idr _ ∙ sym (commutes f)
  factors {j} eta p = commute {f = NT eta λ j k f → idr _ ∙ sym (p f) } ηₚ j
  unique eta p other commutes = unique other $ ext commutes

lim→Δcofree {F} lim = record where
  open Limit lim using (apex; cone)
  open make-is-limit (unmake-limit (Limit.has-limit lim))
  cofree = apex
  counit = cone
  unfold eta = universal (eta .η) λ f → sym (eta .is-natural _ _ f) ∙ idr _
  commute {x} {nt} = ext λ j → factors (nt .η) λ _ → sym (nt .is-natural _ _ _) ∙ idr _
  unique {x} {nt} g p = unique (nt .η) (λ _ → sym (nt .is-natural _ _ _) ∙ idr _) g λ j → p ηₚ  j
```
-->

## The (Co)limit functor

Any functor which is a right (resp: left) colimit to $\Delta_J$ computes
as (co)limits.

```agda
Δadj→has-colimits-of-shape : ∀ {J : Precategory o' ℓ'} {Colim} → (Colim ⊣ ConstD {C = C} {J = J}) → ∀ (F : Functor J C) → Colimit F
Δadj→has-colimits-of-shape has-adj = Δfree→colim ⊙ left-adjoint→free-objects has-adj

Δadj→has-limits-of-shape : ∀ {J : Precategory o' ℓ'} {Lim} → (ConstD {C = C} {J = J} ⊣ Lim) → ∀ (F : Functor J C) → Limit F
Δadj→has-limits-of-shape has-adj = Δcofree→lim ⊙ right-adjoint→cofree-objects has-adj
```

Thus, any category which has adjoints to its generalized diagonal
functor $\Delta_J$ for any $J$ is (co)complete.

```agda
has-Δadjs→is-cocomplete : ∀ {o' ℓ'} → ({J : Precategory o' ℓ'} → Σ[ Colim ∈ Functor _ C ] Colim ⊣ ConstD {C = C} {J = J}) → is-cocomplete o' ℓ' C
has-Δadjs→is-cocomplete adjs = Δadj→has-colimits-of-shape (adjs .snd)

has-Δadjs→is-complete : ∀ {o' ℓ'} → ({J : Precategory o' ℓ'} → Σ[ Lim ∈ Functor _ C ] ConstD {C = C} {J = J} ⊣ Lim) → is-complete o' ℓ' C
has-Δadjs→is-complete adjs = Δadj→has-limits-of-shape (adjs .snd)
```
