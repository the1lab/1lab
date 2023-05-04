<!--
```agda
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Univalence.Reasoning
import Cat.Displayed.Univalence
import Cat.Displayed.Reasoning as Dr
import Cat.Displayed.Morphism
import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Displayed.Cartesian.Identity
  {o ℓ o′ ℓ′} {B : Precategory o ℓ} (E : Displayed B o′ ℓ′)
  where
```

# Identity of Cartesian lifts

In this module, we prove that Cartesian morphisms are unique up to
_vertical_ isomorphism, which, if the displayed category is univalent
(regardless of univalence of the base), can be strengthened to show that
the type of Cartesian lifts for a given "corner" is a proposition.

<!--
```agda
private
  module B = Cr B

open Cat.Displayed.Univalence.Reasoning E
open Cat.Displayed.Univalence E
open Cat.Displayed.Morphism E
open Dr E
open _≅[_]_
```
-->

We'll first observe that if we have two witnesses that $f'$ is a
Cartesian morphism over $f$, then the fact that both provide _unique_
solutions to factorisation problems imply that these must be the same
solution. Therefore, since the other components are paths, a morphism
can be Cartesian in at most one way.

```agda
module _ {a b a′ b′} (f : B.Hom a b) {f′ : Hom[ f ] a′ b′}
         (c₁ c₂ : is-cartesian E f f′)
  where

  private
    module c1 = is-cartesian c₁
    module c2 = is-cartesian c₂

  open is-cartesian

  private
    univ : ∀ {u u′} (m : B.Hom u a) (h′ : Hom[ f B.∘ m ] u′ b′)
          → c1.universal m h′ ≡ c2.universal m h′
    univ m h′ = c2.unique (c1.universal m h′) (c1.commutes m h′)

  Cartesian-is-prop : c₁ ≡ c₂
  Cartesian-is-prop i .universal m h′ = univ m h′ i
  Cartesian-is-prop i .commutes m h′ =
    is-prop→pathp (λ i → Hom[ f B.∘ m ]-set _ b′ (f′ ∘′ univ m h′ i) h′)
      (c1.commutes m h′)
      (c2.commutes m h′) i
  Cartesian-is-prop i .unique {h′ = h′} m′ p =
    is-prop→pathp (λ i → Hom[ _ ]-set _ a′ m′ (univ _ h′ i))
      (c1.unique m′ p) (c2.unique m′ p) i
```

Unsurprisingly, that's the easier half of the proof. Another quarter of
the proof is `cartesian-domain-unique`{.Agda}, which is ~~in another
castle~~ defined in another module. By the construction there, the
isomorphism sends $f_1$ to $f_2$!

<!--
```agda
module _ {a b a₁′ a₂′ b′} (f : B.Hom a b) {f₁′ : Hom[ f ] a₁′ b′}
         {f₂′ : Hom[ f ] a₂′ b′} (c₁ : is-cartesian E f f₁′) (c₂ : is-cartesian E f f₂′)
  where
  private
    module c1 = is-cartesian c₁
    module c2 = is-cartesian c₂
```
-->

```agda
  cartesian-map-uniquep
    : (p : f B.∘ B.id ≡ f) → f₁′ ∘′ cartesian-domain-unique E c₁ c₂ .from′ ≡[ p ] f₂′
  cartesian-map-uniquep p = to-pathp⁻ $
    c1.commutes B.id _ ∙ reindex (sym (B.idr f)) (sym p)
```

<!--
```agda
module _ {a b b′} (f : B.Hom a b) (l1 l2 : Cartesian-lift E f b′) where
  open Cartesian-lift

  private
    module l1 = Cartesian-lift l1
    module l2 = Cartesian-lift l2
```
-->

Having established that being Cartesian is a property of a morphism,
that any pair of Cartesian lifts for the same $f : a \to b$ and $b'
\liesover b$ have isomorphic domains, and that this isomorphism sends
the first morphism to the second, all that remains is putting this
together into a tidy proof: If $\cE$ is univalent, the space of
Cartesian lifts for $(f, b')$ is a proposition.

```agda
  Cartesian-lift-is-prop : is-category-displayed → l1 ≡ l2
  Cartesian-lift-is-prop e-cat = p where
    im = cartesian-domain-unique E l1.cartesian l2.cartesian

    obp : l1.x′ ≡ l2.x′
    obp = ≅↓-identity-system e-cat .to-path im

    pres : PathP (λ i → Hom[ f ] (obp i) b′) l1.lifting l2.lifting
    pres = Hom[]-pathp-refll-iso e-cat (B.idr f) im l1.lifting l2.lifting
      (cartesian-map-uniquep f l1.cartesian l2.cartesian (B.idr f))

    p : l1 ≡ l2
    p i .x′        = obp i
    p i .lifting   = pres i
    p i .cartesian =
      is-prop→pathp (λ i → Cartesian-is-prop {a′ = obp i} f {f′ = pres i})
        l1.cartesian l2.cartesian i
```
