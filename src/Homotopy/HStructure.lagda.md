<!--
```agda
open import 1Lab.Prelude

open import Algebra.Group.Cat.Base
open import Algebra.Group.Homotopy
open import Algebra.Group.Ab
open import Algebra.Group

open import Data.Set.Truncation

open import Homotopy.Space.Suspension
open import Homotopy.Space.Delooping
open import Homotopy.Connectedness
open import Homotopy.Base
```
-->

```agda
module Homotopy.HStructure where
```

# H-structures

```agda
module _ {ℓ} ((A , a₀) : Type∙ ℓ) where
  record H-Structure : Type ℓ where
    no-eta-equality
    field
      _⊙_ : A → A → A
      idl : ∀ x → a₀ ⊙ x ≡ x
      idr : ∀ x → x ⊙ a₀ ≡ x
      coh : idl a₀ ≡ idr a₀
      inv : ∀ x → is-equiv (x ⊙_)
```

```agda
module _ {ℓ} (G : Group ℓ) (ab : is-commutative-group G) where
  open Group-on (G .snd)
  private module H = H-Structure

  private
    mul : Deloop G → Deloop G → Deloop G
    mul base       y = y
    mul (path g i) y = pathᵇ G ab y g i
    mul (path-sq x y i j) z = pathᵇ-sq G ab z x y i j
    mul (squash x y p q α β i j k) z = squash (mul x z) (mul y z)
      (λ i → mul (p i) z) (λ i → mul (q i) z)
      (λ i j → mul (α i j) z) (λ i j → mul (β i j) z)
      i j k

  Deloop-H-Structure : H-Structure (Deloop G , base)
  Deloop-H-Structure .H._⊙_   = mul
  Deloop-H-Structure .H.idl x = refl
  Deloop-H-Structure .H.idr   = Deloop-elim-set G _ (λ _ → hlevel 2) refl λ x i j → path x i
  Deloop-H-Structure .H.coh   = refl
  Deloop-H-Structure .H.inv   = Deloop-elim-prop G _ (λ _ → hlevel 1) id-equiv
```

## Higher homotopy groups of suspensions

Inspired by the theorem above[^cycle], one might think that, if $A$ is a
space with $\pi_1(A) = G$, then $\Susp A$ has $\pi_2 = G$, and every
other homotopy group trivial. Sadly, this is not the case: spheres are
suspensions, and the homotopy groups of spheres are famously --- and
comically --- complicated. However, if $A$ has an **h-structure**, then
$\pi_2(\Susp A) = G$.

[^cycle]: which can't be proved in this module because of import cycles

<!--
```agda

module
  _ {ℓ} {A∙@(A , a₀) : Type∙ ℓ}
    (conn : is-connected∙ A∙)
    (trunc : is-groupoid A)
    (hs : H-Structure A∙)
  where

  open H-Structure hs
```
-->

```agda

  rem₂
    : ∀ {ℓ ℓ'} {A∙@(A , a₀) : Type∙ ℓ} {P : A → A → Type ℓ'} n
    → is-n-connected A (2 + n)
    → (∀ x y → is-hlevel (P x y) (2 + n))
    → (f : (x : A) → P x a₀)
    → (g : (x : A) → P a₀ x)
    → f a₀ ≡ g a₀
    → ∀ x y → P x y
  rem₂ {A∙ = A , a₀} {P} n a-conn p-hl f g coh x y = extension x .fst y
    where
    Q : A → Type _
    Q a = Σ (∀ b → P a b) (λ k → k a₀ ≡ f a)

    pt : (x y : A) → is-n-connected (fibre {A = ⊤} (λ _ → x) y) (suc n)
    pt x y = retract→is-n-connected (suc n)
      (tt ,_) snd (λ _ → refl) (Path-is-connected (suc n) a-conn)

    rem₂' : (x : A) → is-hlevel (fibre (λ section → section ∘ (λ _ → a₀)) (λ _ → f x)) 1
    rem₂' a = connected-elim-relative {A = ⊤} {B = A}
      (λ b → P a b) (λ _ → a₀) (suc n) 1 (pt a₀) (λ _ → p-hl _ _) (λ _ → f a)

    extension = Equiv.from
      (_ , connected-elim {A = ⊤} Q (λ _ → a₀) (suc n) (pt a₀) λ x →
        retract→is-hlevel (suc n) (λ (p , q) → p , happly q tt) (λ (p , q) → p , funext λ _ → q) (λ _ → refl) (is-prop→is-hlevel-suc (rem₂' x)))
      λ _ → g , sym coh

  -- rem₁ : (a a' : A) → Path (n-Tr (Path (Susp A) N S) 3)
  --         (inc (merid (a ⊙ a')))
  --         (inc (merid a ∙ sym (merid a₀) ∙ merid a'))
  -- rem₁ = rem₂ {A∙ = A∙} 0 (is-connected∙→is-connected conn) (λ _ _ → n-Tr-is-hlevel 2 _ _)
  --   (λ x → ap n-Tr.inc (ap merid (idr x) ∙ coh1 x))
  --   (λ x → ap n-Tr.inc (ap merid (idl x) ∙ coh2 x))
  --   (ap (ap n-Tr.inc) (ap₂ _∙_ (sym (ap (ap Susp.merid) coh))
  --     (sym (∙-idr _) ∙ ap (merid a₀ ∙_) (sym (∙-invl (merid a₀)))
  --       ≡⟨ {!   !} ⟩
  --      sym (∙-cancell (sym (merid a₀)) (merid a₀))
  --       ∎)))
  --   where
  --     coh1 : ∀ x → merid x ≡ merid x ∙ sym (merid a₀) ∙ merid a₀
  --     coh1 x = sym (∙-idr _) ∙ ap (merid x ∙_) (sym (∙-invl (merid a₀)))
  --     coh2 : ∀ x → merid x ≡ merid a₀ ∙ sym (merid a₀) ∙ merid x
  --     coh2 x = sym (∙-cancell (sym (merid a₀)) (merid x))
```
