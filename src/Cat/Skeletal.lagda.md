<!--
```agda
open import Cat.Strict
open import Cat.Instances.Discrete
open import Cat.Prelude

open import Homotopy.Space.Circle

import Cat.Reasoning

open Cat.Reasoning using (Isomorphism ; id-iso)
open Precategory using (Ob)
```
-->

```agda
module Cat.Skeletal where
```

# Skeletal Precategories

A precategory $\cC$ is skeletal if all of its isomorphisms are
automorphisms, or in other words, if there is *any* isomorphism
$X \cong Y$, then $X$ and $Y$ are equal. We can encode this condition
by requiring that the propositional truncation of isomorphisms in $\cC$
is an [identity system].

[identity system]: 1Lab.Path.IdentitySystem.html

```agda
is-skeletal : ∀ {o ℓ} → Precategory o ℓ → Type (o ⊔ ℓ)
is-skeletal C =
  is-identity-system (λ x y → ∥ Isomorphism C x y ∥) (λ x → inc (id-iso C))
```

Note that this is distinct from [univalence], which states that
*untruncated* isomorphisms form an identity system. Univalence is a much
more useful condition in practice; very few interesting categories are 
skeletal. In fact, we only define skeletal categories to show that other
conditions imply it, and therefore should be discounted.

[univalence]: Cat.Univalent.html

<!--
```agda
module _ {o ℓ} (C : Precategory o ℓ) where
```
-->

One reason skeletality rules out a lot of interesting categories is that
it implies that the category is [strict].

[strict]: Cat.Strict.html

```agda
  skeletal→strict : is-skeletal C → is-strict C
  skeletal→strict skel = identity-system→hlevel 1 skel (λ _ _ → squash)
```

Furthermore, skeletality does *not* imply univalence, as $\cC$ may have
non-trivial automorphisms. See [here] for an example of such a precategory.

[here]: Cat.Instances.Shape.Involution.html

In general, the "correct" notion of skeletal in HoTT are [gaunt] categories.
