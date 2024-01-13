<!--
```agda
open import Cat.Monoidal.Base
open import Cat.Prelude

open import Cat.Enriched.Base

import Cat.Reasoning
```
-->

```agda
module Cat.Enriched.Reasoning
  {ov ℓv oc} {V : Precategory ov ℓv} {V-monoidal : Monoidal-category V}
  (C : Enriched-precategory V-monoidal oc)
  where
```

<!--
```agda
private
  module V = Cat.Reasoning V

open Monoidal-category V-monoidal
open Enriched-precategory C public

private variable
  Γ Δ Ψ Θ : V.Ob
  w x y z : Obv
  a b c d f g h i : V.Hom Γ (Δ ⊗ Hom-ob x y)
  σ : V.Hom Γ Δ
```
-->

# Reasoning for Enriched Categories

## Identity Morphisms

```agda
abstract
  id-commv
    : ∀ {Γ Δ x y} {f : V.Hom Γ (Δ ⊗ Hom-ob x y)}
    → f ∘v idv ≡ idv ∘v f
  id-commv = idrv _ ∙ sym (idlv _)

  id-comm-symv
    : ∀ {Γ Δ x y} {f : V.Hom Γ (Δ ⊗ Hom-ob x y)}
    → idv ∘v f ≡ f ∘v idv
  id-comm-symv = idlv _ ∙ sym (idrv _)

module _ (p : a ≡ idv) where abstract
  elimlv : a ∘v f ≡ f 
  elimlv {f = f} = ap (_∘v f) p ∙ idlv f

  elimrv : f ∘v a ≡ f
  elimrv {f = f} = ap (f ∘v_) p ∙ idrv f

  elim-innerv : f ∘v a ∘v h ≡ f ∘v h
  elim-innerv {f = f} = ap (f ∘v_) elimlv

  introlv : f ≡ a ∘v f
  introlv = sym elimlv

  introrv : f ≡ f ∘v a
  introrv = sym elimrv
```

## Reassociations

```agda
module _ (p : a ∘v b ≡ c) where abstract
  pulllv : a ∘v (b ∘v f) ≡ c ∘v f
  pulllv {f = f} = assocv _ _ _ ∙ ap (_∘v f) p

  pullrv : (f ∘v a) ∘v b ≡ f ∘v c
  pullrv {f = f} = sym (assocv _ _ _) ∙ ap (f ∘v_) p

module _ (p : c ≡ a ∘v b) where abstract
  pushlv : c ∘v f ≡ a ∘v (b ∘v f)
  pushlv = sym (pulllv (sym p))

  pushrv : f ∘v c ≡ (f ∘v a) ∘v b
  pushrv = sym (pullrv (sym p))

module _ (p : f ∘v h ≡ g ∘v i) where abstract
  extendlv : f ∘v (h ∘v b) ≡ g ∘v (i ∘v b)
  extendlv {b = b} =
    assocv _ _ _ ·· ap (_∘v b) p ·· sym (assocv _ _ _)

  extendrv : (a ∘v f) ∘v h ≡ (a ∘v g) ∘v i
  extendrv {a = a} =
    sym (assocv _ _ _) ·· ap (a ∘v_) p ·· assocv _ _ _

  extend-innerv : a ∘v f ∘v h ∘v b ≡ a ∘v g ∘v i ∘v b
  extend-innerv {a = a} = ap (a ∘v_) extendlv 
```

## Cancellation

```agda
module _ (inv : h ∘v i ≡ idv) where
  cancellv : h ∘v (i ∘v f) ≡ f
  cancellv = pulllv inv ∙ idlv _

  cancelrv : (f ∘v h) ∘v i ≡ f
  cancelrv = pullrv inv ∙ idrv _

  insertlv : f ≡ h ∘v (i ∘v f)
  insertlv = sym cancellv

  insertrv : f ≡ (f ∘v h) ∘v i
  insertrv = sym cancelrv

  deletelv : h ∘v (i ∘v f) ∘v g ≡ f ∘v g
  deletelv = pulllv cancellv

  deleterv : (f ∘v g ∘v h) ∘v i ≡ f ∘v g
  deleterv = pullrv cancelrv
```


