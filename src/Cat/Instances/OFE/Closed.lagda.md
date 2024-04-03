<!--
```agda
open import Cat.Displayed.Univalence.Thin
open import Cat.Displayed.Total
open import Cat.Instances.OFE
open import Cat.Prelude
```
-->

```agda
module Cat.Instances.OFE.Closed where
```

# Function OFEs

If $A$ and $B$ are [OFEs], then so is the space of non-expansive
functions $A \overset{ne}{\to} B$: this makes the category OFE into a
Cartesian closed category.

[OFEs]: Cat.Instances.OFE.html

<!--
```agda
open OFE-Notation

module _ {ℓa ℓb ℓa' ℓb'} {A : Type ℓa} {B : Type ℓb} (O : OFE-on ℓa' A) (P : OFE-on ℓb' B)
  where
  private
    instance
      _ = O
      _ = P
    module O = OFE-on O
    module P = OFE-on P
```
-->

```agda
  Function-OFE : OFE-on (ℓa ⊔ ℓb') (O →ⁿᵉ P)
  Function-OFE .within n f g = ∀ x → f .map x ≈[ n ] g .map x
  Function-OFE .has-is-ofe .has-is-prop n x y = hlevel 1
  Function-OFE .has-is-ofe .≈-refl n x  = P.≈-refl n
  Function-OFE .has-is-ofe .≈-sym n p x = P.≈-sym n (p x)
  Function-OFE .has-is-ofe .≈-trans n p q x = P.≈-trans n (p x) (q x)
  Function-OFE .has-is-ofe .bounded f g x = P.bounded (f .map x) (g .map x)
  Function-OFE .has-is-ofe .step n f g α x = P.step n (f .map x) (g .map x) (α x)
  Function-OFE .has-is-ofe .limit f g α = Nonexp-ext λ x →
    P.limit (f .map x) (g .map x) (λ n → α n x)
```
