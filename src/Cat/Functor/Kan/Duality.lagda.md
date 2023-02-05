```agda
open import Cat.Functor.Coherence
open import Cat.Functor.Kan.Base
open import Cat.Prelude

module Cat.Functor.Kan.Duality where
```

<!--
```agda
private
  variable
    o ℓ : Level
    C C′ D : Precategory o ℓ
```
-->

# Duality for Kan extensions

Left kan extensions are dual to right kan extensions.
This is straightforward enough to prove, but does involve some
bureaucracy involving opposite categories.

<!--
```agda
module _ (p : Functor C C′) (F : Functor C D) where
  open Ran
  open Lan
  open is-ran
  open is-lan
  open _=>_

  co-unit→counit
    : ∀ {G : Functor (C′ ^op) (D ^op)}
    → Functor.op F => G F∘ Functor.op p → Functor.op G F∘ p => F
  counit→co-unit
    : ∀ {G : Functor C′ D}
    → G F∘ p => F
    → Functor.op F => Functor.op G F∘ Functor.op p

  unquoteDef co-unit→counit = define-dualiser co-unit→counit
  unquoteDef counit→co-unit = define-dualiser counit→co-unit
```
-->

```agda
  is-co-lan→is-ran
    : ∀ {G : Functor (C′ ^op) (D ^op)} {eta : Functor.op F => G F∘ Functor.op p}
    → is-lan (Functor.op p) (Functor.op F) G eta
    → is-ran p F (Functor.op G) (co-unit→counit eta)
  is-co-lan→is-ran {G = G} {eta = eta} is-lan = ran where
    module lan = is-lan is-lan

    ran : is-ran p F (Functor.op G) (co-unit→counit eta)
    ran .σ {M = M} α = op (lan.σ α′) where
      unquoteDecl α′ = dualise-into α′
        (Functor.op F => Functor.op M F∘ Functor.op p)
        α

    ran .σ-comm = Nat-path λ x → lan.σ-comm ηₚ x
    ran .σ-uniq {M = M} {σ′ = σ′} p =
      Nat-path λ x → lan.σ-uniq {σ′ = σ′op} (Nat-path λ x → p ηₚ x) ηₚ x
      where unquoteDecl σ′op = dualise-into σ′op _ σ′
```

<!--
```agda
  is-ran→is-co-lan
    : ∀ {Ext : Functor C′ D} {eta : Ext F∘ p => F}
    → is-ran p F Ext eta
    → is-lan (Functor.op p) (Functor.op F) (Functor.op Ext) (counit→co-unit eta)
  is-ran→is-co-lan {Ext = Ext} is-ran = lan where
    module ran = is-ran is-ran

    lan : is-lan (Functor.op p) (Functor.op F) (Functor.op Ext) _
    lan .σ {M = M} α = σ′ where
      unquoteDecl α′ = dualise-into α′ (Functor.op M F∘ p => F) α
      unquoteDecl σ′ = dualise-into σ′ (Functor.op Ext => M) (ran.σ α′)

    lan .σ-comm = Nat-path λ x → ran.σ-comm ηₚ x
    lan .σ-uniq {M = M} {σ′ = σ′} p =
      Nat-path λ x → ran.σ-uniq {σ′ = σ′op} (Nat-path λ x → p ηₚ x) ηₚ x
      where unquoteDecl σ′op = dualise-into σ′op _ σ′
```
-->

```agda
  Co-lan→Ran : Lan (Functor.op p) (Functor.op F) → Ran p F
  Co-lan→Ran lan .Ext     = Functor.op (lan .Ext)
  Co-lan→Ran lan .eps     = co-unit→counit (lan .eta)
  Co-lan→Ran lan .has-ran = is-co-lan→is-ran (lan .has-lan)
```

<!-- [TODO: Reed M, 05/02/2023] Opposite direction of duality. -->
