<!--
```agda
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Univalence.Reasoning
import Cat.Displayed.Univalence
import Cat.Displayed.Reasoning as Dr
import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Displayed.Cartesian.Identity
  {o ℓ o' ℓ'} {B : Precategory o ℓ} (E : Displayed B o' ℓ')
  where
```

# Identity of cartesian lifts

<!--
```agda
private
  module B = Cr B

open Cat.Displayed.Univalence.Reasoning E
open Cat.Displayed.Univalence E
open Dr E

module _ {a b b'} (e-cat : is-category-displayed) (f : B.Hom a b) where
```
-->

In this module, we prove that [[Cartesian lifts]] in a [[displayed
univalent category]] form a [[proposition]].

We already know that Cartesian lifts are unique up to a vertical
isomorphism, so all that remains is to apply univalence and check
that this isomorphism fits into a commuting triangle with the two
lifts.

```agda
  Cartesian-lift-is-prop : is-prop (Cartesian-lift E f b')
  Cartesian-lift-is-prop l1 l2 = Cartesian-lift-path E obp pres where
    module l1 = Cartesian-lift l1
    module l2 = Cartesian-lift l2

    im = cartesian-domain-unique E l1.cartesian l2.cartesian

    obp : l1.x' ≡ l2.x'
    obp = ≅↓-identity-system e-cat .to-path im

    pres : PathP (λ i → Hom[ f ] (obp i) b') l1.lifting l2.lifting
    pres = Hom[]-pathp-refll-iso e-cat (B.idr f) im l1.lifting l2.lifting
      (to-pathp[]⁻ (l1.commutes B.id _))
```
