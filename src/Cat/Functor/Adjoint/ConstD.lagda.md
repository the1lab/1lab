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
const-free→colim : Free-object ConstD F → Colimit F
const-free→colim {F} free-ob = to-colimit $ to-is-colimit $ record where
  open module free = Free-object free-ob
  ψ = unit .η
  universal {x} eta commutes = fold {x} (NT eta λ j k f → commutes f ∙ sym (idl _))

  commutes {j} {k} f = unit .is-natural _ _ f ∙ idl _
  factors {j} eta p = commute {f = NT eta λ x y f → p f ∙ sym (idl _)} ηₚ j
  unique eta p other commutes = unique other $ ext commutes

colim→const-free : Colimit F → Free-object ConstD F
colim→const-free {F} colim = record where
  open module colim = Colimit colim using (coapex; cocone)
  open make-is-colimit (unmake-colimit colim.has-colimit)
  free = coapex
  unit = cocone
  fold eta = universal (eta .η) λ f → eta .is-natural _ _ f ∙ idl _

  commute {x} {nt} = ext λ j → factors (nt .η) λ _ → nt .is-natural _ _ _ ∙ idl _
  unique {x} {nt} g p = unique (nt .η) (λ _ → nt .is-natural _ _ _ ∙ idl _) g
    λ j → p ηₚ  j

const-cofree→lim : Cofree-object ConstD F → Limit F
lim→const-cofree : Limit F → Cofree-object ConstD F
```

<!--
```agda
-- this is better worked out explicitly
const-cofree→lim {F} cofree-ob = to-limit $ to-is-limit $ record where
  open module cofree = Cofree-object cofree-ob
  ψ = counit .η
  universal {x} eta commutes = unfold {x} $ NT eta λ j k f → idr _ ∙ sym (commutes f)

  commutes {j} {k} f = (sym $ counit .is-natural _ _ f) ∙ idr _
  factors {j} eta p = commute {f = NT eta λ j k f → idr _ ∙ sym (p f) } ηₚ j
  unique eta p other commutes = unique other $ ext commutes

lim→const-cofree {F} lim = record where
  open Limit lim using (apex; cone)
  open make-is-limit (unmake-limit (Limit.has-limit lim))
  cofree = apex
  counit = cone
  unfold eta = universal (eta .η) λ f → sym (eta .is-natural _ _ f) ∙ idr _

  commute {x} {nt} = ext λ j → factors (nt .η) λ _ → sym (nt .is-natural _ _ _)
    ∙ idr _
  unique {x} {nt} g p = unique (nt .η) (λ _ → sym (nt .is-natural _ _ _) ∙ idr _) g
    λ j → p ηₚ  j
```
-->

## The (Co)limit functor

Any functor which is a right (resp: left) colimit to $\Delta_J$ computes
as (co)limits.

```agda
const-adj→has-colimits-of-shape
  : ∀ {J : Precategory o' ℓ'} {Colim} → (Colim ⊣ ConstD {C = C} {J = J})
  → (F : Functor J C) → Colimit F
const-adj→has-colimits-of-shape has-adj =
  const-free→colim ⊙ left-adjoint→free-objects has-adj

const-adj→has-limits-of-shape
  : ∀ {J : Precategory o' ℓ'} {Lim} → (ConstD {C = C} {J = J} ⊣ Lim)
  → (F : Functor J C) → Limit F
const-adj→has-limits-of-shape has-adj =
  const-cofree→lim ⊙ right-adjoint→cofree-objects has-adj
```

Thus, any category which has adjoints to its generalized diagonal
functor $\Delta_J$ for any $J$ is (co)complete.

```agda
has-const-adjs→is-cocomplete : ∀ {o' ℓ'} → ({J : Precategory o' ℓ'} → Σ[ Colim ∈ Functor _ C ] Colim ⊣ ConstD {C = C} {J = J}) → is-cocomplete o' ℓ' C
has-const-adjs→is-cocomplete adjs = const-adj→has-colimits-of-shape (adjs .snd)

has-const-adjs→is-complete : ∀ {o' ℓ'} → ({J : Precategory o' ℓ'} → Σ[ Lim ∈ Functor _ C ] ConstD {C = C} {J = J} ⊣ Lim) → is-complete o' ℓ' C
has-const-adjs→is-complete adjs = const-adj→has-limits-of-shape (adjs .snd)
```
