<!--
```agda
open import Cat.Diagram.Pullback.Properties
open import Cat.Diagram.Pullback
open import Cat.Diagram.Product
open import Cat.Diagram.Image
open import Cat.Displayed.Cocartesian
open import Cat.Displayed.Univalence
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Base
open import Cat.Displayed.Fibre
open import Cat.Prelude

import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Displayed.Instances.Subobjects
  {o ℓ} (B : Precategory o ℓ)
  where
```

<!--
```agda
open Cr B
open Displayed
```
-->

# The fibration of subobjects

```agda

record Subobject (y : Ob) : Type (o ⊔ ℓ) where
  field
    {domain} : Ob
    map   : Hom domain y
    monic : is-monic map

open Subobject public

record ≤-over {x y} (f : Hom x y) (a : Subobject x) (b : Subobject y) : Type ℓ where
  field
    map : Hom (a .domain) (b .domain)
    sq : f ∘ Subobject.map a ≡ Subobject.map b ∘ map

open ≤-over public

≤-over-is-prop
  : ∀ {x y} {f : Hom x y} {a : Subobject x} {b : Subobject y}
  → (p q : ≤-over f a b)
  → p ≡ q
≤-over-is-prop {f = f} {a} {b} p q = path where
  maps : p .map ≡ q .map
  maps = b .monic (p .map) (q .map) (sym (p .sq) ∙ q .sq)

  path : p ≡ q
  path i .map = maps i
  path i .sq = is-prop→pathp (λ i → Hom-set _ _ (f ∘ a .map) (b .map ∘ maps i)) (p .sq) (q .sq) i

instance
  H-Level-≤-over
    : ∀ {x y} {f : Hom x y} {a : Subobject x} {b : Subobject y} {n}
    → H-Level (≤-over f a b) (suc n)
  H-Level-≤-over = prop-instance ≤-over-is-prop

Subobjects : Displayed B (o ⊔ ℓ) ℓ
Subobjects .Ob[_] y = Subobject y
Subobjects .Hom[_]  = ≤-over
Subobjects .Hom[_]-set f a b = is-prop→is-set ≤-over-is-prop
Subobjects .id′ = record { map = id ; sq = id-comm-sym }
Subobjects ._∘′_ α β = record { map = α .map ∘ β .map ; sq = pullr (β .sq) ∙ extendl (α .sq) }
Subobjects .idr′ _ = is-prop→pathp (λ i → hlevel 1) _ _
Subobjects .idl′ _ = is-prop→pathp (λ i → hlevel 1) _ _
Subobjects .assoc′ _ _ _ = is-prop→pathp (λ i → hlevel 1) _ _

open Cartesian-fibration
open Cartesian-lift
open is-cartesian
open Pullback

Subobject-fibration
  : has-pullbacks B
  → Cartesian-fibration Subobjects
Subobject-fibration pb .has-lift f y′ = lifted where
  it = pb (y′ .map) f

  lifted : Cartesian-lift Subobjects f y′
  lifted .x′ .domain = it .apex
  lifted .x′ .map    = it .p₂
  lifted .x′ .monic  = is-monic→pullback-is-monic (y′ .monic) (it .has-is-pb)

  lifted .lifting .map = it .p₁
  lifted .lifting .sq = sym (it .square)

  lifted .cartesian .universal {u′ = u′} m h′ .map =
    it .universal {p₁' = h′ .map} {p₂' = m ∘ u′ .map} (sym (h′ .sq) ∙ sym (assoc f m (u′ .map)))
  lifted .cartesian .universal {u′ = u′} m h′ .sq = sym (it .p₂∘universal)
  lifted .cartesian .commutes _ _ = ≤-over-is-prop _ _
  lifted .cartesian .unique _ _ = ≤-over-is-prop _ _

open Cocartesian-fibration
open Cocartesian-lift
open is-cocartesian

Subobject-opfibration
  : (∀ {x y} (f : Hom x y) → Image B f)
  → (pb : has-pullbacks B)
  → Cocartesian-fibration Subobjects
Subobject-opfibration images pb .has-lift f x′ = lifted where
  it = images (f ∘ x′ .map)
  open Image B it

  lifted : Cocartesian-lift Subobjects f x′
  lifted .y′ .domain = Im
  lifted .y′ .map = Im→codomain
  lifted .y′ .monic = Im→codomain-is-M
  lifted .lifting .map = corestrict
  lifted .lifting .sq = sym image-factors
  lifted .cocartesian .is-cocartesian.universal {u′ = u′} m h′ =
    record { map = also .p₁ ∘ mono
           ; sq = sym (extendl (also .square) ∙ ap₂ _∘_ refl universal-factors)
           }
    where
    also = pb (u′ .map) m

    mono : Hom Im (also .apex)
    mono = Image.universal
      B it (also .p₂)
      (is-monic→pullback-is-monic (u′ .monic) (also .has-is-pb))
      (also .Pullback.universal {p₁' = h′ .map} {p₂' = f ∘ x′ .map}
        (sym (h′ .sq) ∙ sym (assoc _ _ _))) (also .p₂∘universal)
  lifted .cocartesian .commutes _ _ = hlevel 1 _ _
  lifted .cocartesian .unique _ _   = hlevel 1 _ _

Sub : Ob → Precategory (o ⊔ ℓ) ℓ
Sub y = Fibre′ Subobjects y re coh where
  re : ∀ {a b} → ≤-over (id ∘ id) a b → ≤-over id a b
  re x .map = x .map
  re x .sq  = ap₂ _∘_ (introl refl) refl ∙ x .sq

  abstract
    coh : ∀ {a b} (f : ≤-over (id ∘ id) a b) → re f ≡ transport (λ i → ≤-over (idl id i) a b) f
    coh f = hlevel 1 _ _

module Sub {y} = Cr (Sub y)

_≤ₘ_ : ∀ {y} (a b : Subobject y) → Type _
_≤ₘ_ = ≤-over id

≤ₘ→mono : ∀ {y} {a b : Subobject y} → a ≤ₘ b → a .domain ↪ b .domain
≤ₘ→mono x .mor = x .map
≤ₘ→mono {a = a} x .monic g h α = a .monic g h $
  a .map ∘ g      ≡⟨ ap (_∘ g) (introl refl ∙ x .sq) ∙ pullr refl ⟩
  _ ∘ x .map ∘ g  ≡⟨ ap₂ _∘_ refl α ⟩
  _ ∘ x .map ∘ h  ≡⟨ pulll (sym (x .sq) ∙ idl _) ⟩
  a .map ∘ h      ∎

cutₛ : ∀ {x y} {f : Hom x y} → is-monic f → Subobject y
cutₛ x .domain = _
cutₛ x .map    = _
cutₛ x .monic  = x

Sub-antisym
  : ∀ {y} {a b : Subobject y}
  → a ≤ₘ b
  → b ≤ₘ a
  → a Sub.≅ b
Sub-antisym f g = Sub.make-iso f g (hlevel 1 _ _) (hlevel 1 _ _)

Subobject-path
  : ∀ {y} {a b : Subobject y}
  → (p : a .domain ≡ b .domain)
  → PathP (λ i → Hom (p i) y) (a .map) (b .map)
  → a ≡ b
Subobject-path p q i .domain = p i
Subobject-path p q i .map = q i
Subobject-path {a = a} {b = b} p q i .monic {c} =
  is-prop→pathp (λ i → Π-is-hlevel³ 1 λ (g h : Hom c (p i)) (_ : q i ∘ g ≡ q i ∘ h) → Hom-set _ _ g h)
    (a .monic) (b .monic) i

Sub-products
  : ∀ {y}
  → has-pullbacks B
  → has-products (Sub y)
Sub-products {y} pb a b = prod where
  it = pb (a .map) (b .map)

  prod : Product (Sub y) a b
  prod .Product.apex .domain = it .apex
  prod .Product.apex .map = a .map ∘ it .p₁
  prod .Product.apex .monic g h α =
    unique₂ it {p = assoc _ _ _ ∙ sym α ∙ pushl (it .square)} (a .monic _ _ (assoc _ _ _ ∙ α ∙ sym (assoc _ _ _)))
      refl refl (b .monic _ _ (pulll (sym (it .square)) ∙ sym α ∙ pushl (it .square)))

  prod .Product.π₁ .map = it .p₁
  prod .Product.π₁ .sq = idl _

  prod .Product.π₂ .map = it .p₂
  prod .Product.π₂ .sq = idl _ ∙ it .square

  prod .Product.has-is-product .is-product.⟨_,_⟩ q≤a q≤b .map =
    it .universal {p₁' = q≤a .map} {p₂' = q≤b .map} (sym (q≤a .sq) ∙ q≤b .sq)
  prod .Product.has-is-product .is-product.⟨_,_⟩ q≤a q≤b .sq =
    idl _ ∙ sym (pullr (it .p₁∘universal) ∙ sym (q≤a .sq) ∙ idl _)
  prod .Product.has-is-product .is-product.π₁∘factor = hlevel 1 _ _
  prod .Product.has-is-product .is-product.π₂∘factor = hlevel 1 _ _
  prod .Product.has-is-product .is-product.unique _ _ _ = hlevel 1 _ _

Sub-is-category : ∀ {y} → is-category B → is-category (Sub y)
Sub-is-category b-cat .to-path {a} {b} x =
  Subobject-path
    (b-cat .to-path i)
    (Univalent.Hom-pathp-refll-iso b-cat (sym (x .Sub.from .sq) ∙ idl _))
  where
    i : a .domain ≅ b .domain
    i = make-iso (x .Sub.to .map) (x .Sub.from .map) (ap map (Sub.invl x)) (ap map (Sub.invr x))
Sub-is-category b-cat .to-path-over p = Sub.≅-pathp refl _ (is-prop→pathp (λ _ → hlevel 1) _ _)
```
