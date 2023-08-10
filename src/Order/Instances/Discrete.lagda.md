<!--
```agda
open import Cat.Functor.Adjoint
open import Cat.Displayed.Total
open import Cat.Prelude

open import Order.Base
open import Order.Diagram.Lub

import Order.Reasoning as Poset
```
-->

```agda
module Order.Instances.Discrete where
```

# Discrete Orders

Every set $A$ can be turned into a [poset] by defining $x \le y$ to
be $x = y$.

[poset]: Order.Base.html

```agda
Disc : ∀ {ℓ} → Set ℓ → Poset ℓ ℓ
Disc A = to-poset ∣ A ∣ mk-disc where
  mk-disc : make-poset _ (A .∣_∣)
  mk-disc .make-poset.rel = _≡_
  mk-disc .make-poset.id = refl
  mk-disc .make-poset.thin = A .is-tr _ _
  mk-disc .make-poset.trans = _∙_
  mk-disc .make-poset.antisym p _ = p
```

This extends to a functor from $\Sets$ into the category of posets.

```agda
DiscF : ∀ {ℓ} → Functor (Sets ℓ) (Posets ℓ ℓ)
DiscF .Functor.F₀ = Disc
DiscF .Functor.F₁ f = total-hom f (λ _ _ p → ap f p)
DiscF .Functor.F-id = total-hom-path _ refl refl
DiscF .Functor.F-∘ f g = total-hom-path _ refl refl
```

Furthermore, this functor is left-adjoint to the forgetful functor
into $\Sets$.

```agda
DiscF⊣Forget : ∀ {ℓ} → DiscF {ℓ} ⊣ πᶠ _
DiscF⊣Forget ._⊣_.unit ._=>_.η A x = x
DiscF⊣Forget ._⊣_.unit ._=>_.is-natural _ _ _ = refl
DiscF⊣Forget ._⊣_.counit ._=>_.η P =
  total-hom (λ x → x) (λ _ _ → Poset.path→≤ P)
DiscF⊣Forget ._⊣_.counit ._=>_.is-natural P Q f =
  total-hom-path _ refl
    (funext λ _ → funext λ _ → funext λ _ → Poset.≤-thin Q _ _)
DiscF⊣Forget ._⊣_.zig {A = A} =
  total-hom-path _ refl $
  funext λ x → funext λ y → funext λ p →
  J (λ y p → transport (λ i → p (~ i) ≡ y) refl ≡ p) (transport-refl _) p
DiscF⊣Forget ._⊣_.zag = refl
```

## Least Upper Bounds

If $f : I \to A$ has a least upper bound in the discrete poset on $A$,
then $f$ must be a constant family.


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
