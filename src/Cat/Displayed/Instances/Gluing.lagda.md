<!--
```agda
open import Cat.Displayed.Diagram.Total.Exponential
open import Cat.Displayed.Diagram.Total.Terminal
open import Cat.Displayed.Diagram.Total.Product
open import Cat.Diagram.Exponential
open import Cat.Instances.Product
open import Cat.Diagram.Pullback
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Instances.Comma
open import Cat.Instances.Slice
open import Cat.Displayed.Base
open import Cat.Cartesian
open import Cat.Prelude

import Cat.Functor.Bifunctor as Bifunctor
import Cat.Functor.Reasoning as Fr
import Cat.Reasoning

open Cartesian-closed
open is-exponential
open Exponential
open is-product
open Terminal
open Product
open ↓Obj
open ↓Hom
```
-->

```agda
module Cat.Displayed.Instances.Gluing
  {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'} {F : Functor D C}
  (ccart : Cartesian-category C) (dcart : Cartesian-category D)
  (pres  : Cartesian-functor F dcart ccart)
  where
```

# Artin gluing

<!--
```agda
private
  module F  = Fr F
  module C  = Cartesian-category ccart
  module D  = Cartesian-category dcart

open Cartesian-functor pres renaming (module preserved to is)
open /-Obj public

module _ where
  open Displayed
```
-->

```agda
  Gl : Displayed D (o ⊔ ℓ) ℓ
  Gl .Ob[_]  cod     = /-Obj {C = C} (F.₀ cod)
  Gl .Hom[_] f xm yn = Σ[ g ∈ C.Hom (xm .domain) (yn .domain) ] yn .map C.∘ g ≡ F.₁ f C.∘ xm .map

  Gl .Hom[_]-set f x y = hlevel 2

  Gl .id' = record
    { fst = C.id
    ; snd = C.elimr refl ∙ C.introl F.F-id
    }
  Gl ._∘'_ (f , p) (g , q) = record
    { fst = f C.∘ g
    ; snd = C.pulll p ∙∙ C.pullr q ∙∙ F.pulll refl
    }

  Gl .idr'   (f , _)                 = Σ-prop-pathp! (C.idr f)
  Gl .idl'   (f , _)                 = Σ-prop-pathp! (C.idl f)
  Gl .assoc' (f , _) (g , _) (h , _) = Σ-prop-pathp! (C.assoc f g h)
```

<!--
```agda
module Gl = Displayed Gl

open is-terminal-over
open TerminalP
```
-->

```agda
Gl-terminal : TerminalP Gl D.terminal
Gl-terminal .top' = cut {domain = C.top} (pres-terminal _ .centre)
Gl-terminal .has⊤' .!'          = record
  { fst = C.!
  ; snd = is-contr→is-prop (pres-terminal _) _ _
  }
Gl-terminal .has⊤' .!-unique' h = Σ-prop-path! (C.!-unique _)
```

<!--
```agda
open is-product-over
open ProductP
```
-->

```agda
Gl-products : has-products-over Gl D.products
Gl-products {x} {y} a b = done module Gl-products where
  apx : Gl ʻ (x D.⊗₀ y)
  apx .domain = a .domain C.⊗₀ b .domain
  apx .map    = is.⟨ a .map C.∘ C.π₁ , b .map C.∘ C.π₂ ⟩

  done : ProductP Gl _ a b
  done .apex' = apx
  done .π₁' = record { snd = sym is.π₁∘⟨⟩ }
  done .π₂' = record { snd = sym is.π₂∘⟨⟩ }
  done .has-is-product' .⟨_,_⟩'  {f = f} {a' = a'} {g = g} f' g' =
    record { fst = (C.⟨ f' .fst , g' .fst ⟩) ; snd = coh }
    where abstract
    coh : apx .map C.∘ C.⟨ f' .fst , g' .fst ⟩ ≡ F.₁ (D.⟨ f , g ⟩) C.∘ a' .map
    coh = C.pullr (C.⟨⟩∘ _) ∙ sym (is.unique
      (F.pulll D.π₁∘⟨⟩ ∙ sym (f' .snd) ∙ sym (C.pullr C.π₁∘⟨⟩))
      (F.pulll D.π₂∘⟨⟩ ∙ sym (g' .snd) ∙ sym (C.pullr C.π₂∘⟨⟩)))

  done .has-is-product' .π₁∘⟨⟩' = Σ-prop-pathp! C.π₁∘⟨⟩
  done .has-is-product' .π₂∘⟨⟩' = Σ-prop-pathp! C.π₂∘⟨⟩
  done .has-is-product' .unique' p q = Σ-prop-pathp! $ C.⟨⟩-unique
    (λ i → p i .fst)
    (λ i → q i .fst)
```

<!--
```agda
open Gl-products renaming (apx to _×Gl_) using () public
open Cartesian-over

Gl-cartesian : Cartesian-over Gl dcart
Gl-cartesian .terminal' = Gl-terminal
Gl-cartesian .products' = Gl-products

module _ (ccl : Cartesian-closed C ccart) (dcl : Cartesian-closed D dcart) (pullbacks : has-pullbacks C) where
  private
    module Cλ = Cartesian-closed ccl
    module Dλ = Cartesian-closed dcl

  open is-exponential-over
  open ExponentialP
```
-->

```agda
  Gl-closed : Cartesian-closed-over Gl Gl-cartesian dcl
  Gl-closed {Ay} {By} A B = done where
    φ : C.Hom Cλ.[ A .domain , B .domain ] Cλ.[ A .domain , F.₀ By ]
    φ = Cλ.ƛ (B .map C.∘ Cλ.ev)

    ψ : C.Hom (F.₀ Dλ.[ Ay , By ]) Cλ.[ A .domain , F.₀ By ]
    ψ = Cλ.ƛ (F.₁ Dλ.ev C.∘ comparison.inv C.∘ (C.id C.⊗₁ A .map))

    pb : Pullback C ψ φ
    pb = pullbacks ψ φ

    module pb = Pullback pb

    pow : Gl ʻ Dλ.[ Ay , By ]
    pow .domain = pb.apex
    pow .map    = pb.p₁

    evm : Gl.Hom[ Dλ.ev ] (pow ×Gl A) B
    evm .fst = Cλ.ev C.∘ (pb.p₂ C.⊗₁ C.id)
    evm .snd = Equiv.injective (_ , Cλ.lambda-is-equiv) $
      Cλ.ƛ (B .map C.∘ Cλ.ev C.∘ (pb.p₂ C.⊗₁ C.id))
        ≡⟨ ap Cλ.ƛ (C.pulll refl) ⟩
      Cλ.ƛ ((B .map C.∘ Cλ.ev) C.∘ (pb.p₂ C.⊗₁ C.id))
        ≡⟨ Cλ.ƛ-∘' _ _ _ ⟩
      Cλ.ƛ (Cλ.ev C.∘ (C.id C.⊗₁ C.id)) C.∘ Cλ.ƛ (B .map C.∘ Cλ.ev) C.∘ pb.p₂
        ≡⟨ C.eliml (ap Cλ.ƛ (C.elimr (C.×-functor .Functor.F-id)) ∙ Cλ.lambda-ev) ⟩
      Cλ.ƛ (B .map C.∘ Cλ.ev) C.∘ pb.p₂
        ≡⟨ sym pb.square ⟩
      Cλ.ƛ (F.₁ Dλ.ev C.∘ comparison.inv C.∘ (C.id C.⊗₁ A .map)) C.∘ pb.p₁
        ≡˘⟨ Cλ.ƛ-∘-idr _ _ ⟩
      Cλ.ƛ ((F.₁ Dλ.ev C.∘ comparison.inv C.∘ (C.id C.⊗₁ A .map)) C.∘ (pb.p₁ C.⊗₁ C.id))
        ≡⟨ ap Cλ.ƛ (C.pullr (C.pullr (Fr.collapse C.×-functor (C.idl _ ,ₚ C.idr _)))) ⟩
      Cλ.ƛ (F.₁ Dλ.ev C.∘ comparison.inv C.∘ (pb.p₁ C.⊗₁ A .map))
        ∎

    done : ExponentialP Gl Gl-cartesian _ A B
    done .B^A' = pow
    done .ev'  = evm
    done .has-is-exponential' .ƛ' {Γ' = Γ} {m = mβ} m .fst = alpha module alpha where
      abstract
        coh : ψ C.∘ F.₁ (Dλ.ƛ mβ) C.∘ Γ .map ≡ φ C.∘ Cλ.ƛ (m .fst)
        coh = Equiv.injective₂ (Equiv.inverse (_ , Cλ.lambda-is-equiv))
          (
            Cλ.unlambda (Cλ.ƛ (F.₁ Dλ.ev C.∘ comparison.inv C.∘ (C.id C.⊗₁ A .map)) C.∘ F.₁ (Dλ.ƛ mβ) C.∘ Γ .map)
              ≡⟨ Cλ.unlambda-∘ _ _ ⟩
            Cλ.unlambda (Cλ.ƛ (F.₁ Dλ.ev C.∘ comparison.inv C.∘ (C.id C.⊗₁ A .map))) C.∘ ((F.₁ (Dλ.ƛ mβ) C.∘ Γ .map) C.⊗₁ C.id)
              ≡⟨ C.pushl (Cλ.commutes _) ⟩
            F.₁ Dλ.ev C.∘ (comparison.inv C.∘ (C.id C.⊗₁ A .map)) C.∘ ((F.₁ (Dλ.ƛ mβ) C.∘ Γ .map) C.⊗₁ C.id)
              ≡⟨ ap₂ C._∘_ refl (C.pullr (Fr.weave C.×-functor (C.pulll (C.idl _) ,ₚ C.elimr refl ∙ C.introl F.F-id))) ⟩
            F.₁ Dλ.ev C.∘ comparison.inv C.∘ (F.₁ (Dλ.ƛ mβ) C.⊗₁ F.₁ D.id) C.∘ (Γ .map C.⊗₁ A .map)
              ≡⟨ ap₂ C._∘_ refl (C.extendl (comparison-nat _ _ _)) ⟩
            F.₁ Dλ.ev C.∘ F.₁ (Dλ.ƛ mβ D.⊗₁ D.id) C.∘ comparison.inv C.∘ (Γ .map C.⊗₁ A .map)
              ≡⟨ C.pulll (F.collapse (Dλ.commutes _)) ⟩
            F.₁ mβ C.∘ comparison.inv C.∘ (Γ .map C.⊗₁ A .map)
              ≡˘⟨ m .snd ⟩
            B .map C.∘ m .fst ∎)
          (
            Cλ.unlambda (Cλ.ƛ (B .map C.∘ Cλ.ev) C.∘ Cλ.ƛ (m .fst))
              ≡⟨ Cλ.unlambda-∘ _ _ ⟩
            Cλ.unlambda (Cλ.ƛ (B .map C.∘ Cλ.ev)) C.∘ (Cλ.ƛ (m .fst) C.⊗₁ C.id)
              ≡⟨ C.pushl (Cλ.commutes _) ⟩
            B .map C.∘ Cλ.unlambda (Cλ.ƛ (m .fst))
              ≡⟨ ap₂ C._∘_ refl (Cλ.commutes _) ⟩
            B .map C.∘ m .fst ∎)

      alpha = pb.universal {p₁' = F.₁ (Dλ.ƛ mβ) C.∘ Γ .map} {p₂' = Cλ.ƛ (m .fst)} coh

    done .has-is-exponential' .ƛ' m .snd = pb.p₁∘universal
    done .has-is-exponential' .commutes' m = Σ-prop-pathp! comm1 where abstract
      comm1 : (Cλ.ev C.∘ (pb.p₂ C.⊗₁ C.id)) C.∘ (alpha.alpha m C.⊗₁ C.id) ≡ m .fst
      comm1 = C.pullr (sym (Bifunctor.first∘first C.×-functor))
           ∙∙ ap (Cλ.ev C.∘_) (ap₂ C._⊗₁_ pb.p₂∘universal refl)
           ∙∙ Cλ.commutes _

    done .has-is-exponential' .unique' {Γ' = Γ} {m = mβ} {m'β} {p} {m' = m} m' q =
      Σ-prop-pathp! (pb.unique coh₁ coh₂)
      where

      coh₁ : pb.p₁ C.∘ m' .fst ≡ F.₁ (Dλ.ƛ mβ) C.∘ Γ .map
      coh₁ =
        pb.p₁ C.∘ m' .fst
          ≡⟨ m' .snd ⟩
        F.₁ (m'β) C.∘ Γ .map
          ≡⟨ ap₂ C._∘_ (ap F.₁ (Dλ.unique _ p)) refl ⟩
        F.₁ (Dλ.ƛ mβ) C.∘ Γ .map
          ∎

      coh₂ : pb.p₂ C.∘ m' .fst ≡ Cλ.ƛ (m .fst)
      coh₂ = Cλ.unique _ $
        Cλ.ev C.∘ (pb.p₂ C.∘ m' .fst) C.⊗₁ C.id
          ≡⟨ ap₂ C._∘_ refl (Bifunctor.first∘first C.×-functor) ⟩
        Cλ.ev C.∘ pb.p₂ C.⊗₁ C.id C.∘ m' .fst C.⊗₁ C.id
          ≡⟨ C.pulll refl ∙ (λ i → q i .fst) ⟩
        m .fst
          ∎
```
