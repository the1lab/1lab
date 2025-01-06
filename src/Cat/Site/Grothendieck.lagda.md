<!--
```agda
open import Cat.Diagram.Sieve
open import Cat.Prelude

import Cat.Site.Closure as Cl
import Cat.Site.Base as Site

open Site using (Coverage ; covers ; cover)
open Cl using (_∋_)
```
-->

```agda
module Cat.Site.Grothendieck where
```

# Grothendieck sites {defines="grothendieck-site grothendieck-coverage"}

A **Grothendieck topology** $J$ on a category $\cC$ is function
assigning to each $U : \cC$ a predicate $J(U)$ on the [[sieves]] on $U$,
satisfying the [[closure properties of sites]]. Every topology generates
a coverage (where the space of sieves that cover $U$ is the total space
of $J(U)$), and, conversely, every site can be [saturated] to give a
topology.

[saturated]: Cat.Site.Closure.html#saturating-sites

```agda
record Topology {o ℓ} (C : Precategory o ℓ) ℓs : Type (o ⊔ ℓ ⊔ lsuc ℓs) where
  open Precategory C
  field
    covering : (U : ⌞ C ⌟) (R : Sieve C U) → Type ℓs

  _◀_ : (U : ⌞ C ⌟) (R : Sieve C U) → Type ℓs
  _◀_ = covering

  field
    has-is-prop : ∀ {U} {R : Sieve C U} → is-prop (U ◀ R)

    stable
      : ∀ {U V} (h : Hom V U) {R : Sieve C U} (hr : U ◀ R)
      → V ◀ (pullback h R)

    maximal
      : ∀ {U} {R : Sieve C U} → id ∈ R → U ◀ R

    local :
      ∀ {U} {R : Sieve C U} (hr : U ◀ R) {S : Sieve C U}
      → (∀ {V} (f : Hom V U) (hf : f ∈ R) → V ◀ pullback f S)
      → U ◀ S
```

The main interest in defining this notion is that if we *start* with a
topology $J$, demote it to a coverage $J_c$, and then saturate this
coverage, we obtain a topology identical to the one we started with.
Since many notions in sheaf theory speak of sieves belonging to the
saturation of a coverage, if we know that we started with a topology,
then we know that we truly haven't added any "new" coverings.

```agda
  from-topology : Coverage C _
  from-topology .covers U = ∫ₚ (U ◀_)
  from-topology .cover = fst
  from-topology .Site.stable (R , P) f = inc ((pullback f R , stable f P) , λ h x → x)

  unsaturate : ∀ {U} {R : Sieve C U} → from-topology ∋ R → U ◀ R
  unsaturate = go where
    go : ∀ {U} {R : Sieve C U} → from-topology ∋ R → U ◀ R
    go (Cl.inc (_ , α)) = α
    go (Cl.max x) = maximal x
    go (Cl.local s p) = local (go s) λ f h → go (p f h)
    go (Cl.pull h x) = stable h (go x)
    go (Cl.squash x y i) = has-is-prop (go x) (go y) i
```

<!--
```agda
open Topology using (covering ; has-is-prop ; stable ; maximal ; local) public

module _ {o h ℓs} {C : Precategory o h} where instance
  Membership-Topology : ∀ {U} → Membership (Sieve C U) (Topology C ℓs) ℓs
  Membership-Topology = record { _∈_ = λ S T → T .covering _ S }

  Funlike-Topology : Funlike (Topology C ℓs) ⌞ C ⌟ λ U → Sieve C U → Type ℓs
  Funlike-Topology .Funlike._#_ T = T .covering

Closure-topology : ∀ {o h ℓs} {C : Precategory o h} → Coverage C ℓs → Topology C (o ⊔ h ⊔ ℓs)
Closure-topology J .covering _ R = J ∋ R
Closure-topology J .has-is-prop = hlevel 1
Closure-topology J .stable = Cl.pull
Closure-topology J .maximal = Cl.max
Closure-topology J .local = Cl.local
```
-->
