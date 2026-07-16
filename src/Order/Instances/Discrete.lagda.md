<!--
```agda
open import Cat.Displayed.Total
open import Cat.Functor.Adjoint
open import Cat.Prelude

open import Order.Diagram.Lub
open import Order.Base
```
-->

```agda
module Order.Instances.Discrete where
```

<!--
```agda
open Functor
open Poset
open _⊣_
open _=>_
```
-->

# Discrete orders {defines="discrete-partial-order"}

Every set $A$ can be turned into a [[poset]] by defining $x \le y$ to
be $x = y$.

```agda
Disc : ∀ {ℓ} → Set ℓ → Poset ℓ ℓ
Disc A .Ob = ⌞ A ⌟
Disc A ._≤_ = _≡_
Disc A .≤-thin = A .is-tr _ _
Disc A .≤-refl = refl
Disc A .≤-trans = _∙_
Disc A .≤-antisym p _ = p
```

We can do that same thing using the inductive identity type.

```agda
Discᵢ : ∀ {ℓ} → Set ℓ → Poset ℓ ℓ
Discᵢ A .Ob = ⌞ A ⌟
Discᵢ A ._≤_ = _≡ᵢ_
Discᵢ A .≤-thin = hlevel 1
Discᵢ A .≤-refl = reflᵢ
Discᵢ A .≤-trans = _∙ᵢ_
Discᵢ A .≤-antisym reflᵢ _ = refl
```

This extends to a functor from $\Sets$ into the category of posets.

```agda
DiscF : ∀ {ℓ} → Functor (Sets ℓ) (Posets ℓ ℓ)
DiscF .F₀ = Disc
DiscF .F₁ f .hom = f
DiscF .F₁ f .pres-≤ = ap f
DiscF .F-id    = ext λ _ → refl
DiscF .F-∘ f g = ext λ _ → refl
```

Furthermore, this functor is a [[left adjoint]] to the forgetful functor
into $\Sets$.

```agda
DiscF⊣Forget : ∀ {ℓ} → DiscF {ℓ} ⊣ Posets↪Sets
DiscF⊣Forget .unit .η A x = x
DiscF⊣Forget .unit .is-natural _ _ _ = refl
DiscF⊣Forget .counit .η P .hom x  = x
DiscF⊣Forget .counit .η P .pres-≤ = Poset.≤-refl' P
DiscF⊣Forget .counit .is-natural P Q f = ext λ _ → refl
DiscF⊣Forget .zig = ext λ _ → refl
DiscF⊣Forget .zag = refl
```

## Least upper bounds

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
