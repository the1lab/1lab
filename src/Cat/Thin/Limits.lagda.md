```agda
open import Cat.Diagram.Product.Indexed
open import Cat.Diagram.Limit.Base
open import Cat.Diagram.Terminal
open import Cat.Prelude
open import Cat.Thin

module Cat.Thin.Limits {o ℓ} {P : Proset o ℓ} where
```

<!--
```agda
module P = Proset P
open Cone-hom
open Terminal
open Cone
```
-->

# Limits in prosets

Suppose a proset $\ca{P}$ admits all [indexed products]. Then it also
admits all limits, where the limit of an arbitrary $F : \ca{C} \to
\ca{P}$ is taken to be the indexed product over the space of objects of
$\ca{C}$.

```agda
has-indexed-products→proset-is-complete
  : ∀ {o' ℓ'} → has-indexed-products P.underlying o'
  → is-complete o' ℓ' P.underlying
has-indexed-products→proset-is-complete has-ips {D} F = lim where
  module F = Functor F

  ip : Indexed-product P.underlying F.₀
  ip = has-ips _

  module Π = Indexed-product ip
```

Since the category $\ca{P}$ is thin, all diagrams automatically commute,
and so the morphism part of the functor $F$ does not contribute to the
limit at all:

```agda
  lim : Limit F
  lim .top .apex = Π.ΠF
  lim .top .ψ = Π.π
  lim .top .commutes _ = P.Hom-is-prop _ _ _ _
  lim .has⊤ x .centre .hom = Π.⟨ x .ψ ⟩
  lim .has⊤ x .centre .commutes = P.Hom-is-prop _ _ _ _
  lim .has⊤ x .paths _ = Cone-hom-path _ (P.Hom-is-prop _ _ _ _)
```

## Limits for less

The data of an indexed product can be made a lot less verbose when
dealing with a thin category, since the commutativity data is free:

```agda
indexed-meet→indexed-product
  : ∀ {o′} {I : Type o′} {F : I → P.Ob} {P : P.Ob}
  → (π : ∀ i → P P.≤ F i)                 -- P is ≤ than all the F_is
  → (∀ {B} → (∀ i → B P.≤ F i) → B P.≤ P) -- and largest among those..
  → is-indexed-product P.underlying F π
indexed-meet→indexed-product π is-meet = is-ip where
  open is-indexed-product

  is-ip : is-indexed-product _ _ _
  ⟨ is-ip ⟩         = is-meet
  is-ip .commute    = P.Hom-is-prop _ _ _ _
  is-ip .unique f x = P.Hom-is-prop _ _ _ _
```