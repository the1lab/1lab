<!--
```agda
open import Cat.Displayed.Diagram.Total.Exponential
open import Cat.Displayed.Diagram.Total.Terminal
open import Cat.Displayed.Diagram.Total.Product
open import Cat.Displayed.Instances.Slice
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

# Artin gluing {defines="artin-gluing"}

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
  Gl .Hom[_] f xm yn = Slice-hom C (F.₁ f) xm yn

  Gl .Hom[_]-set f x y = hlevel 2

  Gl .id' = record
    { map = C.id
    ; com = C.elimr refl ∙ C.introl F.F-id
    }
  Gl ._∘'_ f g = record
    { map = f .map C.∘ g .map
    ; com = C.pulll (f .com) ∙∙ C.pullr (g .com) ∙∙ F.pulll refl
    }

  Gl .idr'   f     = Slice-pathp (C.idr (f .map))
  Gl .idl'   f     = Slice-pathp (C.idl (f .map))
  Gl .assoc' f g h = Slice-pathp (C.assoc (f .map) (g .map) (h .map))
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
Gl-terminal .top'      = cut {dom = C.top} (pres-terminal _ .centre)
Gl-terminal .has⊤' .!' = record
  { map = C.!
  ; com = is-contr→is-prop (pres-terminal _) _ _
  }
Gl-terminal .has⊤' .!-unique' h = Slice-pathp (C.!-unique _)
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
  apx .dom = a .dom C.⊗₀ b .dom
  apx .map = is.⟨ a .map C.∘ C.π₁ , b .map C.∘ C.π₂ ⟩

  done : ProductP Gl _ a b
  done .apex' = apx
  done .π₁' = record { com = sym is.π₁∘⟨⟩ }
  done .π₂' = record { com = sym is.π₂∘⟨⟩ }
  done .has-is-product' .⟨_,_⟩'  {f = f} {a' = a'} {g = g} f' g' =
    record { map = (C.⟨ f' .map , g' .map ⟩) ; com = coh }
    where abstract
    coh : apx .map C.∘ C.⟨ f' .map , g' .map ⟩ ≡ F.₁ (D.⟨ f , g ⟩) C.∘ a' .map
    coh = C.pullr (C.⟨⟩∘ _) ∙ sym (is.unique
      (F.pulll D.π₁∘⟨⟩ ∙ sym (f' .com) ∙ sym (C.pullr C.π₁∘⟨⟩))
      (F.pulll D.π₂∘⟨⟩ ∙ sym (g' .com) ∙ sym (C.pullr C.π₂∘⟨⟩)))

  done .has-is-product' .π₁∘⟨⟩' = Slice-pathp C.π₁∘⟨⟩
  done .has-is-product' .π₂∘⟨⟩' = Slice-pathp C.π₂∘⟨⟩
  done .has-is-product' .unique' p q = Slice-pathp $ C.⟨⟩-unique
    (λ i → p i .map)
    (λ i → q i .map)
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
    φ : C.Hom Cλ.[ A .dom , B .dom ] Cλ.[ A .dom , F.₀ By ]
    φ = Cλ.ƛ (B .map C.∘ Cλ.ev)

    ψ : C.Hom (F.₀ Dλ.[ Ay , By ]) Cλ.[ A .dom , F.₀ By ]
    ψ = Cλ.ƛ (F.₁ Dλ.ev C.∘ comparison.inv C.∘ (C.id C.⊗₁ A .map))

    pb : Pullback C ψ φ
    pb = pullbacks ψ φ

    module pb = Pullback pb

    pow : Gl ʻ Dλ.[ Ay , By ]
    pow .dom = pb.apex
    pow .map = pb.p₁

    evm : Gl.Hom[ Dλ.ev ] (pow ×Gl A) B
    evm .map = Cλ.ev C.∘ (pb.p₂ C.⊗₁ C.id)
    evm .com = Equiv.injective (_ , Cλ.lambda-is-equiv) $
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
    done .has-is-exponential' .ƛ' {Γ' = Γ} {m = mβ} m .map = alpha module alpha where
      abstract
        coh : ψ C.∘ F.₁ (Dλ.ƛ mβ) C.∘ Γ .map ≡ φ C.∘ Cλ.ƛ (m .map)
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
              ≡˘⟨ m .com ⟩
            B .map C.∘ m .map ∎)
          (
            Cλ.unlambda (Cλ.ƛ (B .map C.∘ Cλ.ev) C.∘ Cλ.ƛ (m .map))
              ≡⟨ Cλ.unlambda-∘ _ _ ⟩
            Cλ.unlambda (Cλ.ƛ (B .map C.∘ Cλ.ev)) C.∘ (Cλ.ƛ (m .map) C.⊗₁ C.id)
              ≡⟨ C.pushl (Cλ.commutes _) ⟩
            B .map C.∘ Cλ.unlambda (Cλ.ƛ (m .map))
              ≡⟨ ap₂ C._∘_ refl (Cλ.commutes _) ⟩
            B .map C.∘ m .map ∎)

      alpha = pb.universal {p₁' = F.₁ (Dλ.ƛ mβ) C.∘ Γ .map} {p₂' = Cλ.ƛ (m .map)} coh

    done .has-is-exponential' .ƛ' m .com = pb.p₁∘universal
    done .has-is-exponential' .commutes' m = Slice-pathp comm1 where abstract
      comm1 : (Cλ.ev C.∘ (pb.p₂ C.⊗₁ C.id)) C.∘ (alpha.alpha m C.⊗₁ C.id) ≡ m .map
      comm1 = C.pullr (sym (Bifunctor.first∘first C.×-functor))
           ∙∙ ap (Cλ.ev C.∘_) (ap₂ C._⊗₁_ pb.p₂∘universal refl)
           ∙∙ Cλ.commutes _

    done .has-is-exponential' .unique' {Γ' = Γ} {m = mβ} {m'β} {p} {m' = m} m' q =
      Slice-pathp (pb.unique coh₁ coh₂)
      where

      coh₁ : pb.p₁ C.∘ m' .map ≡ F.₁ (Dλ.ƛ mβ) C.∘ Γ .map
      coh₁ =
        pb.p₁ C.∘ m' .map
          ≡⟨ m' .com ⟩
        F.₁ (m'β) C.∘ Γ .map
          ≡⟨ ap₂ C._∘_ (ap F.₁ (Dλ.unique _ p)) refl ⟩
        F.₁ (Dλ.ƛ mβ) C.∘ Γ .map
          ∎

      coh₂ : pb.p₂ C.∘ m' .map ≡ Cλ.ƛ (m .map)
      coh₂ = Cλ.unique _ $
        Cλ.ev C.∘ (pb.p₂ C.∘ m' .map) C.⊗₁ C.id
          ≡⟨ ap₂ C._∘_ refl (Bifunctor.first∘first C.×-functor) ⟩
        Cλ.ev C.∘ pb.p₂ C.⊗₁ C.id C.∘ m' .map C.⊗₁ C.id
          ≡⟨ C.pulll refl ∙ (λ i → q i .map) ⟩
        m .map
          ∎
```
