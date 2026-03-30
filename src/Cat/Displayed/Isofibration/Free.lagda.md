---
description: |

---

<!--
```agda
open import Cat.Displayed.Instances.Lifting
open import Cat.Displayed.Isofibration
open import Cat.Functor.Properties
open import Cat.Displayed.Functor
open import Cat.Displayed.Total
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Reasoning
import Cat.Displayed.Morphism
import Cat.Functor.Reasoning
import Cat.Reasoning
```
-->

```agda
module Cat.Displayed.Isofibration.Free where
```

<!--
```agda
module _
  {ob ℓb oe ℓe}
  {B : Precategory ob ℓb}
  {E : Precategory oe ℓe}
  (P : Functor E B)
  where
  private
    module B = Cat.Reasoning B
    module E = Cat.Reasoning E
    module P = Cat.Functor.Reasoning P

  open Displayed
  open Functor
```
-->

```agda
  Free-isofibration : Displayed B (ℓb ⊔ oe) (ℓb ⊔ ℓe)
  Free-isofibration .Ob[_] x = Σ[ u ∈ E ] (x B.≅ P.₀ u)
  Free-isofibration .Hom[_] f (u , φ) (v , ψ) =
    Σ[ h ∈ E.Hom u v ] P.₁ h B.∘ B.to φ ≡ (B.to ψ B.∘ f)
  Free-isofibration .Hom[_]-set f a b = hlevel 2
  Free-isofibration .id' = E.id , B.eliml P.F-id ∙ B.intror refl
  Free-isofibration ._∘'_ (f , p) (g , q) = f E.∘ g , P.popr q ∙ B.extendl p
  Free-isofibration .idr' f' = Σ-prop-pathp! (E.idr _)
  Free-isofibration .idl' f' = Σ-prop-pathp! (E.idl _)
  Free-isofibration .assoc' f' g' h' = Σ-prop-pathp! (E.assoc _ _ _)
  Free-isofibration .hom[_] p f = f .fst , (f .snd ∙ B.cdr p)
  Free-isofibration .coh[_] p f = Σ-prop-pathp! refl
```


<!--
```agda
module _
  {ob ℓb oe ℓe}
  {B : Precategory ob ℓb}
  {E : Precategory oe ℓe}
  {P : Functor E B}
  where
  private
    module B = Cat.Reasoning B
    module E = Cat.Reasoning E
    module P = Cat.Functor.Reasoning P
    module Iso[P] = Cat.Displayed.Morphism (Free-isofibration P)

  open Functor
  open Isofibration
  open Lifting
  open Displayed-functor
```
-->

```agda
  Free-isofibration-iso
    : ∀ {a b} {u : a B.≅ b}
    → {x y : E.Ob} {φ : a B.≅ P.₀ x} {ψ : b B.≅ P.₀ y}
    → (θ : x E.≅ y)
    → P.₁ (E.to θ) B.∘ B.to φ ≡ B.to ψ B.∘ B.to u
    -- → B.to ψ B.∘ P.₁ (E.to θ) ≡ B.to u B.∘ B.to φ
    → (x , φ) Iso[P].≅[ u ] (y , ψ)
  Free-isofibration-iso {u = u} {φ = φ} {ψ = ψ} θ p = Iso[P].make-iso[ u ]
    (E.to θ , p)
    (E.from θ , q)
    (Σ-prop-pathp! (E.invl θ))
    (Σ-prop-pathp! (E.invr θ))
    where
      q : P.₁ (E.from θ) B.∘ B.to ψ ≡ B.to φ B.∘ B.from u
      q =
        flip Equiv.from refl $
          P.₁ (E.from θ) B.∘ B.to ψ ≡ B.to φ B.∘ B.from u     ≃⟨ B.post-invr (B.iso→invertible u) ⟩
          (P.₁ (E.from θ) B.∘ B.to ψ) B.∘ B.to u ≡ B.to φ     ≃⟨ ∙-pre-equiv (B.pushr p) ⟩
          P.₁ (E.from θ) B.∘ P.₁ (E.to θ) B.∘ B.to φ ≡ B.to φ ≃⟨ ∙-pre-equiv (P.insertl (E.invr θ)) ⟩
          B.to φ ≡ B.to φ                                     ≃∎


  Free-isofibration-is-isofibration
   : Isofibration (Free-isofibration P)
  Free-isofibration-is-isofibration ._^*_ (x , φ) ψ =
    (x , (φ B.∘Iso ψ))
  Free-isofibration-is-isofibration .iso* (x , φ) ψ =
    Free-isofibration-iso E.id-iso $ P.eliml refl
```

```agda
  Free-isofibration-lifting : Lifting (Free-isofibration P) P
  Free-isofibration-lifting .F₀' x = x , B.id-iso
  Free-isofibration-lifting .F₁' f = f , B.id-comm
  Free-isofibration-lifting .F-id' = Σ-prop-pathp! refl
  Free-isofibration-lifting .F-∘' f g = Σ-prop-pathp! refl

  Free-isofibration-lifting-split-eso
    : is-split-eso (Lifting→Functor (Free-isofibration P) Free-isofibration-lifting)
  Free-isofibration-lifting-split-eso (b , x , φ) =
    x ,
    (total-iso-from-isos (Free-isofibration P) (φ B.Iso⁻¹)
    $ Free-isofibration-iso E.id-iso
    $ P.eliml refl ∙ sym (B.invl φ))

  Free-isofibration-lifting-ff
    : is-fully-faithful (Lifting→Functor (Free-isofibration P) Free-isofibration-lifting)
  Free-isofibration-lifting-ff = is-iso→is-equiv λ where
    .is-iso.from h →  ∫Hom.snd h .fst
    .is-iso.rinv h → ∫Hom-path _ (B.intror refl ∙ ∫Hom.snd h .snd ∙ B.eliml refl) (Σ-prop-pathp! refl)
    .is-iso.linv h → refl
```

```agda
  Free-isofibration-factors
    : ∀ {oh ℓh} {H : Displayed B oh ℓh}
    → Isofibration H
    → (F : Lifting H P)
    → Vertical-functor (Free-isofibration P) H
  Free-isofibration-factors {H = H} H-isofib F = F† where
    module H where
      open Isofibration H-isofib public
      open Cat.Displayed.Reasoning H public
      open Cat.Displayed.Morphism H public

    module F = Lifting F

    F† : Vertical-functor (Free-isofibration P) H
    F† .F₀' (x , φ) = F.F₀' x H.^* φ
    F† .F₁' {a' = (x , φ)} {b' = (y , ψ)} (h , p) =
      H.hom[ B.lswizzle p (B.invr ψ) ] (H.from' (H.iso* _ ψ) H.∘' F.F₁' h H.∘' H.to' (H.iso* _ φ))
    F† .F-id' {x' = (x , φ)} =
      H.begin[]
        H.hom[] (H.from' (H.iso* _ φ) H.∘' F.F₁' E.id H.∘' H.to' (H.iso* _ φ)) H.≡[]⟨ H.unwrap _ ⟩
        H.from' (H.iso* _ φ) H.∘' F.F₁' E.id H.∘' H.to' (H.iso* _ φ)           H.≡[]⟨ (H.refl⟩∘'⟨ H.eliml[] _ F.F-id') ⟩
        H.from' (H.iso* _ φ) H.∘' H.to' (H.iso* _ φ)                           H.≡[]⟨ H.invr' (H.iso* (F.F₀' x) φ) ⟩
        H.id'                                                                  H.∎[]
    F† .F-∘' {f = u} {g = v} {a' = x , φ} {b' = y , ψ} {c' = z , θ} {f' = f , p} {g' = g , q} =
      H.begin[]
        H.hom[] (θ^*← H.∘' F.F₁' (f E.∘ g) H.∘' φ^*→)                                                H.≡[]⟨ H.unwrap _ ⟩
        θ^*← H.∘' F.F₁' (f E.∘ g) H.∘' φ^*→                                                          H.≡[]⟨ H.refl⟩∘'⟨ (H.pushl[] _ (F.F-∘' f g)) ⟩
        θ^*← H.∘' F.F₁' f H.∘' F.F₁' g H.∘' H.to' (H.iso* _ φ)                                       H.≡[]⟨ H.refl⟩∘'⟨ H.refl⟩∘'⟨ (H.introl[] _ (H.invl' (H.iso* _ ψ))) ⟩
        θ^*← H.∘' F.F₁' f H.∘' (ψ^*→ H.∘' ψ^*←) H.∘' F.F₁' g H.∘' H.to' (H.iso* _ φ)                 H.≡[]⟨ (H.refl⟩∘'⟨ H.refl⟩∘'⟨ H.pullr[] _ (H.wrap _)) ⟩
        θ^*← H.∘' F.F₁' f H.∘' ψ^*→ H.∘' H.hom[] (ψ^*← H.∘' F.F₁' g H.∘' φ^*→)                       H.≡[]⟨ (H.pushr[] _ (H.assoc' _ _ _) H.∙[] H.wrapl _) ⟩
        (H.hom[] (θ^*← H.∘' F.F₁' f H.∘' ψ^*→) H.∘' H.hom[] (ψ^*← H.∘' F.F₁' g H.∘' φ^*→))           H.∎[]
      where
        open H._≅[_]_ (H.iso* (F.F₀' x) φ) renaming (to' to φ^*→; from' to φ^*←)
        open H._≅[_]_ (H.iso* (F.F₀' y) ψ) renaming (to' to ψ^*→; from' to ψ^*←)
        open H._≅[_]_ (H.iso* (F.F₀' z) θ) renaming (to' to θ^*→; from' to θ^*←)
```
