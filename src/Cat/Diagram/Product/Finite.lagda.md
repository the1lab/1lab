```agda
open import Cat.Diagram.Product.Indexed
open import Cat.Diagram.Limit.Finite
open import Cat.Diagram.Limit.Base
open import Cat.Diagram.Equaliser
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Prelude

open import Data.Fin

import Cat.Reasoning as Cr

module Cat.Diagram.Product.Finite
  {o ℓ} {C : Precategory o ℓ}
  (terminal : Terminal C)
  (products : ∀ A B → Product C A B)
  where
```

<!--
```agda
open is-indexed-product
open Indexed-product
open is-product
open Terminal
open Product
open Cr C
private module Cart = Cartesian C products
open Cart using (_⊗_)
```
-->

# Computing finite products

Throughout the 1lab, we have referred to categories having a terminal
object and binary products as _Cartesian categories_, _finite products
categories_, and other terms like these. But, a priori, there is no
reason to believe that this implies _all_ finite products exist, right?
Right --- which is why we have to prove it.

In this module, we prove the following theorem: If you have a sequence
of objects in $\ca{C}$ of length $n$, then its product exists as long as
$\ca{C}$ is Cartesian, and can be computed in terms of iterated binary
products and terminal objects.

We take an opportunity to complicate the definition while we're at it:
Instead of computing the product of a one-object sequence to be $A
\times \top$, we simply let it be $A$. This extra case translates to an
extra case in all the proofs, but fortunately it does not complicate
anything too far.

```agda
Cartesian→standard-finite-products : ∀ {n} → (F : Fin n → Ob) → Indexed-product C F
Cartesian→standard-finite-products F = prod where
  F-apex : ∀ {n} → (F : Fin n → Ob) → Ob
  F-apex {zero} F        = terminal .top
  F-apex {suc zero} F    = F fzero
  F-apex {suc (suc n)} F = F fzero ⊗ F-apex (λ e → F (fsuc e))

  F-pi : ∀ {n} (F : Fin n → Ob) (i : Fin n) → Hom (F-apex F) (F i)
  F-pi {suc zero} F fzero       = id
  F-pi {suc (suc n)} F fzero    = Cart.π₁
  F-pi {suc (suc n)} F (fsuc i) = F-pi (λ e → F (fsuc e)) i ∘ Cart.π₂

  F-mult : ∀ {Y} {n} (F : Fin n → Ob)
         → ((i : Fin n) → Hom Y (F i)) → Hom Y (F-apex F)
  F-mult {n = zero} F maps = ! terminal
  F-mult {n = suc zero} F maps = maps fzero
  F-mult {n = suc (suc n)} F maps = Cart.⟨ maps fzero , F-mult (λ z → F (fsuc z)) (λ i → maps (fsuc i)) ⟩

  F-commute : ∀ {Y} {n} (F : Fin n → Ob) (f : (i : Fin n) → Hom Y (F i))
            → ∀ i → F-pi F i ∘ F-mult F f ≡ f i
  F-commute {n = suc zero} F f fzero = idl (f fzero)
  F-commute {n = suc (suc n)} F f fzero = Cart.π₁∘⟨⟩
  F-commute {n = suc (suc n)} F f (fsuc i) = pullr Cart.π₂∘⟨⟩ ∙ F-commute (λ e → F (fsuc e)) (λ e → f (fsuc e)) i

  F-unique
    : ∀ {Y} {n} (F : Fin n → Ob) (f : (i : Fin n) → Hom Y (F i))
    → {h : Hom Y (F-apex F)} → ((i : Fin n) → F-pi F i ∘ h ≡ f i)
    → h ≡ F-mult F f
  F-unique {n = zero} F f {h} p = sym $ !-unique terminal _
  F-unique {n = suc zero} F f {h} p = sym (idl h) ∙ p fzero
  F-unique {n = suc (suc n)} F f {h} p =
    products _ _ .unique h (p fzero)
      (F-unique (λ e → F (fsuc e)) (λ i → f (fsuc i))
        λ i → assoc _ _ _ ∙ p (fsuc i))

  prod : Indexed-product C F
  prod .ΠF = F-apex F
  prod .π  = F-pi F
  prod .has-is-ip .tuple      = F-mult F
  prod .has-is-ip .commute    = F-commute F _ _
  prod .has-is-ip .unique f p = F-unique F f p
```
