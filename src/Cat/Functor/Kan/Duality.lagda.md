<!--
```agda
open import Cat.Functor.Coherence
open import Cat.Functor.Kan.Base
open import Cat.Prelude
```
-->

```agda
module Cat.Functor.Kan.Duality where
```

<!--
```agda
private
  variable
    o ℓ : Level
    C C' D : Precategory o ℓ
```
-->

# Duality for Kan extensions

[[Left Kan extensions]] are dual to [[right Kan extensions]]. This is
straightforward enough to prove, but does involve some bureaucracy
involving opposite categories.

<!--
```agda
module _ (p : Functor C C') (F : Functor C D) where
  open Ran
  open Lan
  open is-ran
  open is-lan
  open _=>_

  co-unit→counit
    : ∀ {G : Functor (C' ^op) (D ^op)}
    → Functor.op F => G F∘ Functor.op p
    → Functor.op G F∘ p => F
  co-unit←counit
    : ∀ {G : Functor C' D}
    → G F∘ p => F
    → Functor.op F => Functor.op G F∘ Functor.op p

  counit→co-unit
    : ∀ {G : Functor (C' ^op) (D ^op)}
    → G F∘ Functor.op p => Functor.op F
    → F => Functor.op G F∘ p
  counit←co-unit
    : ∀ {G : Functor C' D}
    → F => G F∘ p
    → Functor.op G F∘ Functor.op p => Functor.op F

  unquoteDef co-unit→counit = define-dualiser co-unit→counit
  unquoteDef co-unit←counit = define-dualiser co-unit←counit
  unquoteDef counit→co-unit = define-dualiser counit→co-unit
  unquoteDef counit←co-unit = define-dualiser counit←co-unit
```
-->

```agda
  is-co-lan'→is-ran
    : ∀ {G : Functor (C' ^op) (D ^op)} {eta : Functor.op F => G F∘ Functor.op p}
    → is-lan (Functor.op p) (Functor.op F) G eta
    → is-ran p F (Functor.op G) (co-unit→counit eta)
  is-co-lan'→is-ran {G = G} {eta = eta} is-lan = ran where
    module lan = is-lan is-lan

    ran : is-ran p F (Functor.op G) (co-unit→counit eta)
    ran .σ {M = M} α = op (lan.σ α') where
      unquoteDecl α' = dualise-into α'
        (Functor.op F => Functor.op M F∘ Functor.op p)
        α

    ran .σ-comm = ext (lan.σ-comm ηₚ_)
    ran .σ-uniq {M = M} {σ' = σ'} p = ext λ x →
      lan.σ-uniq {σ' = dualise! σ'} (reext! p) ηₚ x
```

<!--
```agda
  -- This is identical to is-co-lan'→is-ran, but we push the Functor.op
  -- into the is-lan, which is what you want when not dealing with Lan.
  is-co-lan→is-ran
    : {G : Functor C' D} {eps : G F∘ p => F}
    → is-lan (Functor.op p) (Functor.op F) (Functor.op G) (co-unit←counit eps)
    → is-ran p F G eps
  is-co-lan→is-ran {G = G} {eps} lan = ran where
    module lan = is-lan lan

    ran : is-ran p F G eps
    ran .σ {M = M} α = op (lan.σ α') where
      unquoteDecl α' = dualise-into α'
        (Functor.op F => Functor.op M F∘ Functor.op p)
        α
    ran .σ-comm = ext (lan.σ-comm ηₚ_)
    ran .σ-uniq {M = M} {σ' = σ'} p = ext λ x →
      lan.σ-uniq {σ' = dualise! σ'} (reext! p) ηₚ x

  is-ran→is-co-lan
    : ∀ {Ext : Functor C' D} {eta : Ext F∘ p => F}
    → is-ran p F Ext eta
    → is-lan (Functor.op p) (Functor.op F) (Functor.op Ext) (co-unit←counit eta)
  is-ran→is-co-lan {Ext = Ext} is-ran = lan where
    module ran = is-ran is-ran

    lan : is-lan (Functor.op p) (Functor.op F) (Functor.op Ext) _
    lan .σ {M = M} α = σ' where
      unquoteDecl α' = dualise-into α' (Functor.op M F∘ p => F) α
      unquoteDecl σ' = dualise-into σ' (Functor.op Ext => M) (ran.σ α')

    lan .σ-comm = ext (ran.σ-comm ηₚ_)
    lan .σ-uniq {M = M} {σ' = σ'} p = ext λ x →
      ran.σ-uniq {σ' = dualise! σ'} (reext! p) ηₚ x

  Co-lan→Ran : Lan (Functor.op p) (Functor.op F) → Ran p F
  Co-lan→Ran lan .Ext     = Functor.op (lan .Ext)
  Co-lan→Ran lan .eps     = co-unit→counit (lan .eta)
  Co-lan→Ran lan .has-ran = is-co-lan'→is-ran (lan .has-lan)

  Ran→Co-lan : Ran p F → Lan (Functor.op p) (Functor.op F)
  Ran→Co-lan ran .Ext = Functor.op (ran .Ext)
  Ran→Co-lan ran .eta = co-unit←counit (ran .eps)
  Ran→Co-lan ran .has-lan = is-ran→is-co-lan (ran .has-ran)

  is-co-ran'→is-lan
    : {G : Functor (C' ^op) (D ^op)} {eps : G F∘ Functor.op p => Functor.op F}
    → is-ran (Functor.op p) (Functor.op F) G eps
    → is-lan p F (Functor.op G) (counit→co-unit eps)
  is-co-ran'→is-lan {G = G} {eps} is-ran = lan where
    module ran = is-ran is-ran

    lan : is-lan p F (Functor.op G) (counit→co-unit eps)
    lan .σ {M = M} β = op (ran.σ β') where
      unquoteDecl β' = dualise-into β'
        (Functor.op M F∘ Functor.op p => Functor.op F)
        β
    lan .σ-comm = ext (ran.σ-comm ηₚ_)
    lan .σ-uniq {M = M} {σ' = σ'} p = ext λ x →
      ran.σ-uniq {σ' = dualise! σ'} (reext! p) ηₚ x

  is-co-ran→is-lan
    : ∀ {G : Functor C' D} {eta}
    → is-ran (Functor.op p) (Functor.op F) (Functor.op G) (counit←co-unit eta)
    → is-lan p F G eta
  is-co-ran→is-lan {G = G} {eta} is-ran = lan where
    module ran = is-ran is-ran

    lan : is-lan p F G eta
    lan .σ {M = M} β = op (ran.σ β') where
      unquoteDecl β' = dualise-into β'
        (Functor.op M F∘ Functor.op p => Functor.op F)
        β
    lan .σ-comm = ext (ran.σ-comm ηₚ_)
    lan .σ-uniq {M = M} {σ' = σ'} p = ext λ x →
      ran.σ-uniq {σ' = dualise! σ'} (reext! p) ηₚ x

  is-lan→is-co-ran
    : ∀ {G : Functor C' D} {eps : F => G F∘ p}
    → is-lan p F G eps
    → is-ran (Functor.op p) (Functor.op F) (Functor.op G) (counit←co-unit eps)
  is-lan→is-co-ran {G = G} is-lan = ran where
    module lan = is-lan is-lan

    ran : is-ran (Functor.op p) (Functor.op F) (Functor.op G) _
    ran .σ {M = M} β = σ' where
      unquoteDecl β' = dualise-into β' (F => Functor.op M F∘ p) β
      unquoteDecl σ' = dualise-into σ' (M => Functor.op G) (lan.σ β')
    ran .σ-comm = ext (lan.σ-comm ηₚ_)
    ran .σ-uniq {M = M} {σ' = σ'} p = ext λ x →
      lan.σ-uniq {σ' = dualise! σ'} (reext! p) ηₚ x

  Co-ran→Lan : Ran (Functor.op p) (Functor.op F) → Lan p F
  Co-ran→Lan ran .Ext = Functor.op (ran .Ext)
  Co-ran→Lan ran .eta = counit→co-unit (ran .eps)
  Co-ran→Lan ran .has-lan = is-co-ran'→is-lan (ran .has-ran)

  Lan→Co-ran : Lan p F → Ran (Functor.op p) (Functor.op F)
  Lan→Co-ran lan .Ext = Functor.op (lan .Ext)
  Lan→Co-ran lan .eps = counit←co-unit (lan .eta)
  Lan→Co-ran lan .has-ran = is-lan→is-co-ran (lan .has-lan)
```
-->
