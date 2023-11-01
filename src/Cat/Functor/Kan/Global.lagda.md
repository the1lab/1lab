<!--
```agda
open import Cat.Functor.Adjoint.Hom
open import Cat.Instances.Functor
open import Cat.Instances.Product
open import Cat.Functor.Kan.Base
open import Cat.Functor.Adjoint
open import Cat.Functor.Compose
open import Cat.Prelude

import Cat.Reasoning

open Functor
open _=>_
open Lan
```
-->

```agda
module Cat.Functor.Kan.Global
```

<!--
```agda
  {o ℓ o' ℓ' o'' ℓ''}
  {C : Precategory o ℓ}
  {C' : Precategory o' ℓ'}
  {D : Precategory o'' ℓ''}
  (p : Functor C C')
  where
```
-->

# Global Kan extensions

Recall that a [[left Kan extension]] of $F : C \to D$ along $p : C \to C'$
is a universal solution $\Lan_p(F)$ to extending $F$ to a functor $C'
\to D$. In particularly happy cases (e.g. when $C$ is [small] and $D$ is
[cocomplete]), the left Kan extension $\Lan_p(F)$ along $p$ exists for
**any** $F$; When this happens, the assignment $F \mapsto \Lan_p(F)$
extends to a functor, which we call a **global Kan extension**.

[small]: 1Lab.intro.html#universes-and-size-issues
[cocomplete]: Cat.Diagram.Colimit.Base.html#cocompleteness

<!--
```agda
private
  module D = Cat.Reasoning D
  module C = Cat.Reasoning C
  module C' = Cat.Reasoning C'
```
-->

```agda
module _ (has-lan : (G : Functor C D) → Lan p G) where
  Lan-functor : Functor Cat[ C , D ] Cat[ C' , D ]
  Lan-functor .F₀ G = has-lan G .Ext
  Lan-functor .F₁ {x} {y} θ =
    has-lan x .σ (has-lan y .eta ∘nt θ)
  Lan-functor .F-id {x} = has-lan x .σ-uniq (ext λ _ → D.id-comm)
  Lan-functor .F-∘ {x} {y} {z} f g =
    has-lan x .σ-uniq $ ext λ a → sym $
        D.pullr   (has-lan x .σ-comm ηₚ a)
      ∙ D.extendl (has-lan y .σ-comm ηₚ a)
```

Functoriality follows, essentially, from the fact that left Kan
extensions are universal: we can map between them in a functorial way
using only the defining natural transformations in the diagram, without
appealing to the details of a particular computation. Moreover, the left
Kan extension functor _itself_ has a universal property: it is a left
adjoint to the [precomposition] functor $- \circ p$.

[precomposition]: Cat.Functor.Compose.html

```agda
  Lan⊣precompose : Lan-functor ⊣ precompose p
  Lan⊣precompose = hom-iso→adjoints f (is-iso→is-equiv eqv) natural where
    f : ∀ {x : Functor C D} {y : Functor C' D} → has-lan x .Ext => y → x => y F∘ p
    f {x} {y} θ = (θ ◂ p) ∘nt has-lan x .eta

    open is-iso

    eqv : ∀ {x} {y} → is-iso (f {x} {y})
    eqv {x} {y} .inv θ = has-lan _ .σ θ
    eqv {x} {y} .rinv θ = has-lan x .σ-comm
    eqv {x} {y} .linv θ = has-lan _ .σ-uniq refl

    natural : hom-iso-natural {L = Lan-functor} {precompose p} f
    natural {b = b} g h x = ext λ a →
      D.pullr (D.pullr (has-lan _ .σ-comm ηₚ a))
      ∙ ap₂ D._∘_ refl (D.pushr refl)
```

And, since adjoints are unique, if $- \circ p$ has any [[left adjoint]],
then its values generate Kan extensions:

```agda
adjoint-precompose→Lan
  : (F : Functor Cat[ C , D ] Cat[ C' , D ])
  → (adj : F ⊣ precompose p)
  → (G : Functor C D)
  → is-lan p G (F .F₀ G) (adj ._⊣_.unit .η G)
adjoint-precompose→Lan F adj G = extn where
  open Lan
  open is-lan
  module adj = _⊣_ adj

  extn : is-lan p G _ _
  extn .σ α = R-adjunct adj α
  extn .σ-comm {M = M} {α = α} = ext λ a →
      D.pullr   (sym (adj.unit .is-natural _ _ _) ηₚ a)
    ∙ D.cancell (adj.zag ηₚ a)
  extn .σ-uniq x = Equiv.injective (_ , L-adjunct-is-equiv adj)
    (L-R-adjunct adj _ ∙ x)
```

This in turn implies that [adjoints are Kan extensions].

[adjoints are Kan extensions]: Cat.Functor.Kan.Adjoint.html
