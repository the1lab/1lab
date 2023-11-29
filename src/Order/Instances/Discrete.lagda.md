<!--
```agda
open import Cat.Displayed.Univalence.Thin
open import Cat.Displayed.Total
open import Cat.Functor.Adjoint
open import Cat.Prelude

open import Order.Diagram.Lub
open import Order.Base

import Order.Reasoning as Poset
```
-->

```agda
module Order.Instances.Discrete where
```

# Discrete Orders

Every set $A$ can be turned into a [[poset]] by defining $x \le y$ to
be $x = y$.

```agda
Disc : ∀ {ℓ} → Set ℓ → Poset ℓ ℓ
Disc A .Poset.Ob = ⌞ A ⌟
Disc A .Poset._≤_ = _≡_
Disc A .Poset.≤-thin = A .is-tr _ _
Disc A .Poset.≤-refl = refl
Disc A .Poset.≤-trans = _∙_
Disc A .Poset.≤-antisym p _ = p
```

This extends to a functor from $\Sets$ into the category of posets.

```agda
DiscF : ∀ {ℓ} → Functor (Sets ℓ) (Posets ℓ ℓ)
DiscF .Functor.F₀ = Disc
DiscF .Functor.F₁ f .hom = f
DiscF .Functor.F₁ f .pres-≤ = ap f
DiscF .Functor.F-id = trivial!
DiscF .Functor.F-∘ f g = trivial!
```

Furthermore, this functor is a [[left adjoint]] to the forgetful functor
into $\Sets$.

```agda
DiscF⊣Forget : ∀ {ℓ} → DiscF {ℓ} ⊣ Forget-poset
DiscF⊣Forget ._⊣_.unit ._=>_.η A x = x
DiscF⊣Forget ._⊣_.unit ._=>_.is-natural _ _ _ = refl
DiscF⊣Forget ._⊣_.counit ._=>_.η P .hom x = x
DiscF⊣Forget ._⊣_.counit ._=>_.η P .pres-≤ = Poset.path→≤ P
DiscF⊣Forget ._⊣_.counit ._=>_.is-natural P Q f = trivial!
DiscF⊣Forget ._⊣_.zig {A = A} = trivial!
DiscF⊣Forget ._⊣_.zag = refl
```

## Least Upper Bounds

If $f : I \to A$ has a [[least upper bound]] in the discrete poset on
$A$, then $f$ must be a constant family.

```agda
disc-is-lub→const
  : ∀ {ℓ iℓ} {Ix : Type iℓ} {A : Set ℓ}
  → {f : Ix → ∣ A ∣} {x : ∣ A ∣}
  → is-lub (Disc A) f x
  → ∀ i → f i ≡ x
disc-is-lub→const x-lub i = is-lub.fam≤lub x-lub i

disc-lub→const
  : ∀ {ℓ iℓ} {Ix : Type iℓ} {A : Set ℓ}
  → {f : Ix → ∣ A ∣}
  → Lub (Disc A) f
  → ∀ i j → f i ≡ f j
disc-lub→const x-lub i j =
  Lub.fam≤lub x-lub i ∙ sym (Lub.fam≤lub x-lub j)
```
