<!--
```agda
open import Cat.Instances.Shape.Terminal
open import Cat.Functor.Kan.Unique
open import Cat.Functor.Naturality
open import Cat.Functor.Coherence
open import Cat.Instances.Coalgebras
open import Cat.Diagram.Limit.Base
open import Cat.Diagram.Limit.Cone
open import Cat.Functor.Kan.Base
open import Cat.Displayed.Total
open import Cat.Functor.Compose
open import Cat.Diagram.Comonad
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Instances.Coalgebras.Limits
  {o ℓ} (C : Precategory o ℓ) (W : Comonad C)
  where
```

<!--
```agda
open Cat.Reasoning C

open Total-hom
open _=>_

open Coalgebra-on
open Comonad W using (module W ; module comult ; module counit ; W-∘ ; W-id ; W₀ ; W₁)
```
-->

# header

```agda
module
  _ {oi ℓi} {I : Precategory oi ℓi}
    (pres : ∀ (F : Functor I C) {X η} (l : is-ran !F F X η) → preserves-ran (Comonad.W W) l)
  where

  is-limit-coalgebra
    : ∀ (F : Functor I (Coalgebras W)) {K eps}
    → (l : is-ran !F (πᶠ _ F∘ F) (πᶠ _ F∘ K) (nat-assoc-from (πᶠ _ ▸ eps)))
    → reflects-ran (πᶠ (Coalgebras-over W)) l
  is-limit-coalgebra F {K} {eps} l = to-is-limitp mk fixup where
    module K = Functor K
    module F = Functor F

    module l = is-limit l
    module l' = is-limit (pres _ l)
    open make-is-limit

    module
      _ {x : Coalgebras.Ob W}
        (eta : (j : Precategory.Ob I) → Coalgebras.Hom W x (F.₀ j))
        (nat : ∀ {x y} (f : Precategory.Hom I x y) → Coalgebras._∘_ W (F.₁ f) (eta x) ≡ eta y)
      where

      ν : Hom (x .fst) (K.₀ tt .fst)
      ν = counit.ε _ ∘ l'.universal (λ j → F.₀ j .snd .ρ ∘ eta j .hom) λ f → pulll (F.₁ f .preserves) ∙ pullr (ap hom (nat _))

      ν-β : ∀ {j} → eps .η j .hom ∘ ν ≡ eta j .hom
      ν-β = pulll (sym (counit.is-natural _ _ _))
         ·· pullr (l'.factors _ _)
         ·· cancell (F.₀ _ .snd .ρ-counit)

    mk : make-is-limit F (K.₀ tt)
    mk .ψ j .hom       = l.ψ j
    mk .ψ j .preserves = eps .η j .preserves
    mk .commutes f = coalgebra-hom-path W (l.commutes f)
    mk .universal eta nat .hom = ν eta nat
    mk .universal eta nat .preserves = l'.unique₂ _
      (λ f → pulll (F.₁ f .preserves) ∙ pullr (ap hom (nat _)))
      (λ j → W.pulll (ν-β eta nat) ∙ eta j .preserves)
      (λ j → pulll (eps .η j .preserves) ∙ pullr (ν-β eta nat))
    mk .factors eta nat = coalgebra-hom-path W (ν-β eta nat)
    mk .unique eta nat other comm = coalgebra-hom-path W (l.unique₂ _
      (λ f → ap hom (nat f))
      (λ j → ap hom (comm j))
      (λ j → ν-β eta nat))

    abstract
      fixup : ∀ {j} → mk .ψ j ≡ eps .η j
      fixup = coalgebra-hom-path W refl

  Coalgebra-on-limit
    : (F : Functor I (Coalgebras W))
    → (L : Limit (πᶠ (Coalgebras-over W) F∘ F))
    → Coalgebra-on W (Limit.apex L)
  Coalgebra-on-limit F L = coalg module Coalgebra-on-limit where
    private
      module L   = Limit L
      module L'  = is-limit (pres (πᶠ _ F∘ F) L.has-limit)
      module L'' = is-limit (pres _ (pres (πᶠ _ F∘ F) L.has-limit))
      module F   = Functor F

    opaque
      ν : Hom L.apex (W₀ L.apex)
      ν = L'.universal (λ j → F.₀ j .snd .ρ ∘ L.ψ j) λ h →
          pulll (F.₁ h .preserves)
        ∙ pullr ( sym (L.eps .is-natural _ _ _)
                ∙ elimr L.Ext.F-id)

      ν-β : ∀ {j} → W₁ (L.eps .η j) ∘ ν ≡ F.₀ j .snd .ρ ∘ L.eps .η j
      ν-β = L'.factors _ _

    coalg : Coalgebra-on W (Limit.apex L)
    coalg .ρ = ν
    coalg .ρ-counit = L.unique₂ _
      (λ f → sym (L.eps .is-natural _ _ f) ∙ elimr L.Ext.F-id)
      (λ j → pulll (sym (counit.is-natural _ _ _))
          ·· pullr ν-β
          ·· cancell (F.₀ j .snd .ρ-counit))
      (λ j → idr (L.eps .η j))
    coalg .ρ-comult = L''.unique₂ _
      (λ f → W.extendl (F.₁ f .preserves) ∙ ap₂ _∘_ refl
        ( pulll (F.₁ f .preserves)
        ∙ pullr (sym (L.eps .is-natural _ _ f) ∙ elimr L.Ext.F-id)))
      (λ j → W.extendl ν-β ∙ ap₂ _∘_ refl ν-β)
      λ j → pulll (sym (comult.is-natural _ _ _))
         ·· pullr ν-β
         ·· extendl (sym (F.₀ j .snd .ρ-comult))

  open Ran
  open is-ran

  Coalgebra-limit
    : (F : Functor I (Coalgebras W))
    → Limit (πᶠ (Coalgebras-over W) F∘ F)
    → Limit F
  Coalgebra-limit F lim .Ext = const! (_ , Coalgebra-on-limit F lim)

  Coalgebra-limit F lim .eps .η x .hom       = lim .eps .η x
  Coalgebra-limit F lim .eps .η x .preserves = Coalgebra-on-limit.ν-β F lim
  Coalgebra-limit F lim .eps .is-natural x y f = coalgebra-hom-path W $
    ap₂ _∘_ refl (sym (lim .Ext .Functor.F-id)) ∙ lim .eps .is-natural x y f

  Coalgebra-limit F lim .has-ran = is-limit-coalgebra F $ natural-isos→is-ran
    idni idni rem₁
    (Nat-path λ x → idl _ ∙ elimr (elimr refl ∙ lim .Ext .Functor.F-id))
    (lim .has-ran)

    where
    open make-natural-iso

    rem₁ : lim .Ext ≅ⁿ πᶠ (Coalgebras-over W) F∘ const! (_ , Coalgebra-on-limit F lim)
    rem₁ = to-natural-iso λ where
      .eta x → id
      .inv x → id
      .eta∘inv x → idl id
      .inv∘eta x → idl id
      .natural x y f → eliml refl ∙ intror (lim .Ext .Functor.F-id)
```
