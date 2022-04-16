```agda
open import Cat.Diagram.Coproduct.Indexed
open import Cat.Diagram.Product.Indexed
open import Cat.Diagram.Colimit.Base
open import Cat.Diagram.Limit.Base
open import Cat.Diagram.Terminal
open import Cat.Diagram.Initial
open import Cat.Prelude
open import Cat.Thin

module Cat.Thin.Limits {o ℓ} {P : Proset o ℓ} where
```

<!--
```agda
private module P = Proset P
open Cocone-hom
open Cone-hom
open Terminal
open Initial
open Cocone
open Cone
```
-->

# Limits in prosets

Suppose a proset $\ca{P}$ admits all [indexed products]. Then it also
admits all limits, where the limit of an arbitrary $F : \ca{C} \to
\ca{P}$ is taken to be the indexed product over the space of objects of
$\ca{C}$.

[indexed products]: Cat.Diagram.Product.Indexed.html

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
  lim .has⊤ x .centre .commutes o = P.Hom-is-prop _ _ _ _
  lim .has⊤ x .paths _ = Cone-hom-path _ (P.Hom-is-prop _ _ _ _)
```

## Limits for less

The data of an indexed product can be made a lot less verbose when
dealing with a thin category, since the commutativity data is free:

```agda
indexed-meet→indexed-product
  : ∀ {o′} {I : Type o′} {F : I → P.Ob} {P : P.Ob}
  → (π : ∀ i → P P.≤ F i)                 -- P is ≤ than all the F_is
  → (∀ {B} → (∀ i → B P.≤ F i) → B P.≤ P) -- and P is largest among those..
  → is-indexed-product P.underlying F π
indexed-meet→indexed-product π is-meet = is-ip where
  open is-indexed-product

  is-ip : is-indexed-product _ _ _
  ⟨ is-ip ⟩         = is-meet
  is-ip .commute    = P.Hom-is-prop _ _ _ _
  is-ip .unique f x = P.Hom-is-prop _ _ _ _
```

# Colimits in prosets

Dualising the discussion above, colimits in prosets correspond to
indexed **co**products. I won't comment on this part of the code since
it is entirely given by flipping arrows around and fixing names of
record fields.

```agda
has-indexed-coproducts→proset-is-cocomplete
  : ∀ {o' ℓ'} → has-indexed-coproducts P.underlying o'
  → is-cocomplete o' ℓ' P.underlying
has-indexed-coproducts→proset-is-cocomplete has-ips {D} F = colim where
  module F = Functor F

  ic : Indexed-coproduct P.underlying F.₀
  ic = has-ips _

  open Indexed-coproduct ic

  colim : Colimit F
  colim .bot .coapex = ΣF
  colim .bot .ψ = ι
  colim .bot .commutes _ = P.Hom-is-prop _ _ _ _
  colim .has⊥ x .centre .hom = match (x .ψ)
  colim .has⊥ x .centre .commutes o = P.Hom-is-prop _ _ _ _
  colim .has⊥ x .paths _ = Cocone-hom-path _ (P.Hom-is-prop _ _ _ _)

indexed-join→indexed-coproduct
  : ∀ {o′} {I : Type o′} {F : I → P.Ob} {J : P.Ob}
  → (ι : ∀ i → F i P.≤ J)                 -- All the F_is are ≤ than J
  → (∀ {B} → (∀ i → F i P.≤ B) → J P.≤ B) -- and J is smallest among those
  → is-indexed-coproduct P.underlying F ι
indexed-join→indexed-coproduct ι is-join = is-ic where
  open is-indexed-coproduct

  is-ic : is-indexed-coproduct _ _ _
  is-ic .match      = is-join
  is-ic .commute    = P.Hom-is-prop _ _ _ _
  is-ic .unique f x = P.Hom-is-prop _ _ _ _
```
