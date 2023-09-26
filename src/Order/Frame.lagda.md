<!--
```agda
open import Cat.Displayed.Total
open import Cat.Functor.Subcategory
open import Cat.Prelude

open import Order.Base
open import Order.Lattice
open import Order.Semilattice
open import Order.Diagram.Glb
open import Order.Diagram.Lub

import Cat.Reasoning

import Order.Reasoning as Poset
```
-->

```agda
module Order.Frame where
```

# Frames

```agda
module _ {o ℓ} (X : Poset o ℓ) where
  open Poset X

  record is-frame : Type (o ⊔ lsuc ℓ) where
    no-eta-equality
    field
      has-is-meet-semilattice : is-meet-semilattice X
      has-joins : ∀ {I : Type ℓ} → (f : I → Ob) → Lub X f

    open is-meet-semilattice has-is-meet-semilattice public
    module has-joins {I : Type ℓ} (f : I → Ob) = Lub (has-joins f)

    open has-joins
      using ()
      renaming
        (lub to ⋃
        ; fam≤lub to fam≤⋃
        ; least to ⋃-universal
        ; has-lub to ⋃-lub)
      public

    field
      ⋃-distrib-l : ∀ {I} (x : Ob) (f : I → Ob) → x ∩ ⋃ f ≡ ⋃ λ i → x ∩ f i
```

<!--
```agda
  is-frame-is-prop : is-prop is-frame
  is-frame-is-prop =
    Iso→is-hlevel 1 eqv $
    Σ-is-hlevel 1 (is-meet-semilattice-is-prop X) λ _ →
    Σ-is-hlevel 1 (Π-is-hlevel′ 1 λ _ → Π-is-hlevel 1 λ _ → Lub-is-prop X) λ _ →
    Π-is-hlevel′ 1 λ _ → Π-is-hlevel² 1 λ _ _ →  X .fst .is-tr _ _
    where unquoteDecl eqv = declare-record-iso eqv (quote is-frame)
```
-->

# Morphisms of frames

```agda
module _ {o ℓ} {X Y : Poset o ℓ} where
  open Total-hom
  private
    module X = Poset X
    module Y = Poset Y

  record is-frame-hom (f : Posets.Hom X Y) : Type (o ⊔ lsuc ℓ) where
    no-eta-equality
    field
      pres-finite-meets : preserves-finite-meets f
      pres-joins : ∀ {I : Type ℓ} (fam : I → X.Ob) (lub : X.Ob)
                 → is-lub X fam lub → is-lub Y (f .hom ⊙ fam) (f .hom lub)
```

<!--
```agda
  is-frame-hom-is-prop : ∀ (f : Posets.Hom X Y) → is-prop (is-frame-hom f)
  is-frame-hom-is-prop f =
    Iso→is-hlevel 1 eqv $
    ×-is-hlevel 1 (preserves-finite-meets-is-prop f) $
    Π-is-hlevel′ 1 λ _ → Π-is-hlevel³ 1 λ _ _ _ → is-lub-is-prop Y
    where unquoteDecl eqv = declare-record-iso eqv (quote is-frame-hom) 
```
-->

```agda
module _ where
  open is-frame-hom

  is-frame-hom-id
    : ∀ {o ℓ} {X : Poset o ℓ}
    → is-frame-hom (Posets.id {x = X})
  is-frame-hom-id .is-frame-hom.pres-finite-meets = preserves-finite-meets-id
  is-frame-hom-id .is-frame-hom.pres-joins _ _ lub = lub

  is-frame-hom-∘
    : ∀ {o ℓ} {X Y Z : Poset o ℓ}
    → {f : Posets.Hom Y Z} {g : Posets.Hom X Y}
    → is-frame-hom f → is-frame-hom g
    → is-frame-hom (f Posets.∘ g)
  is-frame-hom-∘ p q .is-frame-hom.pres-finite-meets =
    preserves-finite-meets-∘ (p .pres-finite-meets) (q .pres-finite-meets)
  is-frame-hom-∘ p q .is-frame-hom.pres-joins fam lub has-lub =
    p .pres-joins _ _ (q .pres-joins _ _ has-lub)
```


# The category of frames

```agda
Frames-subcat : ∀ o ℓ → Subcat (Posets o ℓ) (o ⊔ lsuc ℓ) (o ⊔ lsuc ℓ)
Frames-subcat o ℓ .Subcat.is-ob = is-frame
Frames-subcat o ℓ .Subcat.is-hom f _ _ = is-frame-hom f
Frames-subcat o ℓ .Subcat.is-hom-prop f _ _ = is-frame-hom-is-prop f
Frames-subcat o ℓ .Subcat.is-hom-id _ = is-frame-hom-id
Frames-subcat o ℓ .Subcat.is-hom-∘ = is-frame-hom-∘

Frames : ∀ o ℓ → Precategory (lsuc (o ⊔ ℓ)) ((o ⊔ lsuc ℓ))
Frames o ℓ = Subcategory (Frames-subcat o ℓ)

module Frames {o} {ℓ} = Cat.Reasoning (Frames o ℓ)

Frame : ∀ o ℓ → Type _
Frame o ℓ = Frames.Ob {o} {ℓ}
```

<!--
```agda
{-# DISPLAY  Frames.Ob {o} {ℓ} = Frame o ℓ #-}
```
-->

# Reasoning with frames

```agda
module Frame {o ℓ} (X : Frame o ℓ) where
  poset : Poset o ℓ
  poset = X .fst

  set : Set o
  set = X .fst .fst

  open Poset poset public

  has-is-frame : is-frame poset
  has-is-frame = X .snd

  open is-frame has-is-frame public

  ⋃-twice
    : ∀ {I : Type ℓ} {J : I → Type ℓ} (F : (i : I) → J i → Ob)
    → ⋃ (λ i → ⋃ λ j → F i j)
    ≡ ⋃ {I = Σ I J} (λ ij → F (ij .fst) (ij .snd))
  ⋃-twice F =
    ≤-antisym
      (⋃-universal _ _ λ i → ⋃-universal _ _ λ j → fam≤⋃ _ (i , j))
      (⋃-universal _ _ λ (i , j) →
        ≤-trans (fam≤⋃ (F i) j) (fam≤⋃ _ i))

  ⋃-singleton
    : ∀ {I : Type ℓ} → (F : I → Ob)
    → (p : is-contr I)
    → ⋃ F ≡ F (p .centre)
  ⋃-singleton F p =
    ≤-antisym
      (⋃-universal F _ λ i →
        subst (λ e → F e ≤ F (p .centre)) (p .paths i) ≤-refl)
      (fam≤⋃ F (p .centre))

  ⋃-ap
    : ∀ {I I′ : Type ℓ} {f : I → Ob} {g : I′ → Ob}
    → (e : I ≃ I′)
    → (∀ i → f i ≡ g (Equiv.to e i))
    → ⋃ f ≡ ⋃ g
  ⋃-ap e p = ap₂ (λ I f → ⋃ {I = I} f) (ua e) (ua→ p)

  -- raised i for "index", raised f for "family"
  ⋃-apⁱ : ∀ {I I′ : Type ℓ} {f : I′ → Ob} (e : I ≃ I′) → ⋃ (λ i → f (e .fst i)) ≡ ⋃ f
  ⋃-apᶠ : ∀ {I : Type ℓ} {f g : I → Ob} → (∀ i → f i ≡ g i) → ⋃ f ≡ ⋃ g
  
  ⋃-apⁱ e = ⋃-ap e (λ i → refl)
  ⋃-apᶠ p = ⋃-ap (_ , id-equiv) p

  ⋃-distrib-r
    : ∀ {I : Type ℓ} {f : I → Ob} {x}
    → ⋃ f ∩ x ≡ ⋃ (λ i → f i ∩ x)
  ⋃-distrib-r =
    ∩-commutative _ _
    ·· ⋃-distrib-l _ _
    ·· ap ⋃ (funext λ _ → ∩-commutative _ _)

  ⋃-monotone
    : ∀ {I : Type ℓ} {f g : I → Ob}
    → (∀ i → f i ≤ g i)
    → ⋃ f ≤ ⋃ g
  ⋃-monotone p = ⋃-universal _ _ (λ i → ≤-trans (p i) (fam≤⋃ _ _))
```
