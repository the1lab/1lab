<!--
```agda
open import Cat.Instances.Slice
open import Cat.Diagram.Sieve
open import Cat.Site.Base
open import Cat.Prelude

open import Meta.Brackets

import Cat.Reasoning as Cat

open Precategory using (Hom)
open /-Obj
```
-->

```agda
module Cat.Site.Constructions where
```

# Constructing sites

This module collects miscellaneous helpers for constructing [[sites]].
The first thing we observe is that we can form a coverage by considering
a pullback-stable *predicate*, rather than pullback-stable *families*.
This is the usual fibration/family dichotomy.

```agda
from-stable-property
  : ∀ {o ℓ ℓj} {C : Precategory o ℓ}
  → (P : ∀ {U} → Sieve C U → Type ℓj)
  → (∀ {U V} (f : C .Precategory.Hom V U) (s : Sieve C U) → P s → P (pullback f s))
  → Coverage C (o ⊔ ℓ ⊔ ℓj)
from-stable-property P stab .covers U = Σ[ s ∈ Sieve _ U ] P s
from-stable-property P stab .cover = fst
from-stable-property P stab .stable (S , ps) f = pure
  ((pullback f S , stab f S ps) , λ g hf → hf)
```

<!--
```agda
module _ {o ℓ} (C : Precategory o ℓ) where
  open Cover
```
-->

In a similar vein, we can generalise from families of *sieves* to
families of *families*, since every family generates a sieve. We call a
presentation of a `Coverage`{.Agda} in terms of families-of-families a
family of `Coverings`{.Agda}, since Agda forces us to differentiate the
names.

```agda
  record Coverings ℓi ℓc : Type (o ⊔ ℓ ⊔ lsuc (ℓi ⊔ ℓc)) where
    field
      covers : ⌞ C ⌟ → Type ℓi
      family : ∀ {U} → covers U → Cover C U ℓc
```

The definition of the stability property can be simplified slightly, by
quantifying over the family rather than over the sieve it generates.

```agda
      stable
        : ∀ {U V} (S : covers U) (f : C .Hom V U) → ∃[ R ∈ covers V ]
          (∀ i → family R .map i ∈ pullback f ⟦ family S ⟧)
```

<!--
```agda
  open Coverings public

module _ {o ℓ} {C : Precategory o ℓ} where
  open Cat C
```
-->

It's not very complicated to show that this simplified stability
property implies the literal stability property for the generated
sieves.

```agda
  from-families : ∀ {ℓi ℓf} → Coverings C ℓi ℓf → Coverage C ℓi
  from-families cov .covers  = cov .covers
  from-families cov .cover S = ⟦ cov .family S ⟧
  from-families cov .stable S f = do
    (R , incl) ← cov .stable S f
    let
      incl' : ⟦ cov .family R ⟧ ⊆ pullback f ⟦ _ ⟧
      incl' {W} = elim! λ g r h p → do
        (s , i , q) ← incl r
        pure (s , i ∘ h , extendl q ∙ ap (f ∘_) p)
    pure (R , incl')
```
