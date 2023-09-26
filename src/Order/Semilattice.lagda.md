<!--
```agda
open import Cat.Displayed.Total
open import Cat.Functor.Subcategory
open import Cat.Prelude

open import Order.Diagram.Glb
open import Order.Diagram.Lub
open import Order.Base

import Cat.Reasoning

import Order.Reasoning as Poset
```
-->

```agda
module Order.Semilattice where
```

# Semilattices {defines=semilattice}

```agda
module _ {o ℓ} (X : Poset o ℓ) where
  open Poset X

  record is-meet-semilattice : Type (o ⊔ ℓ) where
    no-eta-equality
    field
      has-top : Top X
      has-meets : ∀ x y → Meet X x y

    module top = Top has-top
    open top using (top) renaming (has-top to top-universal) public

    module meet x y = Meet (has-meets x y)
    open meet renaming
      ( glb to _∩_
      ; greatest to ∩-universal
      ; meet≤l to ∩≤l
      ; meet≤r to ∩≤r
      ; has-meet to ∩-meet)
      public


    ∩-idl : ∀ x → top ∩ x ≡ x
    ∩-idl x =
      ≤-antisym (∩≤r _ _) (∩-universal _ _ _ (top-universal _) ≤-refl)

    ∩-idr : ∀ x → x ∩ top ≡ x
    ∩-idr x =
      ≤-antisym (∩≤l _ _) (∩-universal _ _ _ ≤-refl (top-universal _))

    ∩-assoc : ∀ x y z → x ∩ (y ∩ z) ≡ (x ∩ y) ∩ z
    ∩-assoc x y z =
      ≤-antisym
        (∩-universal _ _ _
          (∩-universal _ _ _ (∩≤l _ _) (≤-trans (∩≤r _ _) (∩≤l _ _)))
          (≤-trans (∩≤r _ _) (∩≤r _ _)))
        (∩-universal _ _ _
          (≤-trans (∩≤l _ _) (∩≤l _ _))
          (∩-universal _ _ _ (≤-trans (∩≤l _ _) (∩≤r _ _)) (∩≤r _ _)))

    ∩-commutative : ∀ x y → x ∩ y ≡ y ∩ x
    ∩-commutative x y =
      ≤-antisym
        (∩-universal _ _ _ (∩≤r _ _) (∩≤l _ _))
        (∩-universal _ _ _ (∩≤r _ _) (∩≤l _ _))

    ∩-idempotent : ∀ x → x ∩ x ≡ x
    ∩-idempotent x =
      ≤-antisym
        (∩≤l _ _)
        (∩-universal _ _ _ ≤-refl ≤-refl)

    ∩-monotone : ∀ {x x′ y y′} → x ≤ x′ → y ≤ y′ → (x ∩ y) ≤ (x′ ∩ y′)
    ∩-monotone p q =
      ∩-universal _ _ _
        (≤-trans (∩≤l _ _) p)
        (≤-trans (∩≤r _ _) q)

  record is-join-semilattice : Type (o ⊔ ℓ) where
    no-eta-equality
    field
      has-bottom : Bottom X
      has-joins : ∀ x y → Join X x y

    module bottom = Bottom has-bottom
    open bottom using (bot) renaming (has-bottom to bottom-universal) public

    module join x y = Join (has-joins x y)
    open join renaming
      ( lub to _∪_
      ; least to ∪-universal
      ; l≤join to l≤∪
      ; r≤join to r≤∪
      ; has-join to ∪-join)
      public

    ∪-idl : ∀ x → bot ∪ x ≡ x
    ∪-idl x =
      ≤-antisym (∪-universal _ _ _ (bottom-universal _) ≤-refl) (r≤∪ _ _)

    ∪-idr : ∀ x → x ∪ bot ≡ x
    ∪-idr x =
      ≤-antisym (∪-universal _ _ _ ≤-refl (bottom-universal _)) (l≤∪ _ _)

    ∪-assoc : ∀ x y z → x ∪ (y ∪ z) ≡ (x ∪ y) ∪ z
    ∪-assoc x y z =
      ≤-antisym
        (∪-universal _ _ _
          (≤-trans (l≤∪ _ _) (l≤∪ _ _))
          (∪-universal _ _ _ (≤-trans (r≤∪ _ _) (l≤∪ _ _)) (r≤∪ _ _)))
        (∪-universal _ _ _
          (∪-universal _ _ _ (l≤∪ _ _) (≤-trans (l≤∪ _ _) (r≤∪ _ _)))
          (≤-trans (r≤∪ _ _) (r≤∪ _ _)))

    ∪-commutative : ∀ x y → x ∪ y ≡ y ∪ x
    ∪-commutative x y =
      ≤-antisym
        (∪-universal _ _ _ (r≤∪ _ _) (l≤∪ _ _))
        (∪-universal _ _ _ (r≤∪ _ _) (l≤∪ _ _))

    ∪-idempotent : ∀ x → x ∪ x ≡ x
    ∪-idempotent x =
      ≤-antisym
        (∪-universal _ _ _ ≤-refl ≤-refl)
        (l≤∪ _ _)
```

<!--
```agda
  is-meet-semilattice-is-prop : is-prop is-meet-semilattice
  is-meet-semilattice-is-prop = Iso→is-hlevel 1 eqv $
    Σ-is-hlevel 1 (Top-is-prop X) λ _ →
    Π-is-hlevel² 1 λ _ _ → Meet-is-prop X
    where unquoteDecl eqv = declare-record-iso eqv (quote is-meet-semilattice)

  is-join-semilattice-is-prop : is-prop is-join-semilattice
  is-join-semilattice-is-prop = Iso→is-hlevel 1 eqv $
    Σ-is-hlevel 1 (Bottom-is-prop X) λ _ →
    Π-is-hlevel² 1 λ _ _ → Join-is-prop X
    where unquoteDecl eqv = declare-record-iso eqv (quote is-join-semilattice)
```
-->

# Morphisms of Semilattices

```agda
module _ {o ℓ} {X Y : Poset o ℓ} where
  private
    module X = Poset X
    module Y = Poset Y
    open Total-hom

  record preserves-finite-meets (f : Posets.Hom X Y) : Type (o ⊔ ℓ) where
    no-eta-equality
    field
      pres-tops
        : ∀ x
        → is-top X x
        → is-top Y (f .hom x)
      pres-meets
        : ∀ x y meet
        → is-meet X x y meet
        → is-meet Y (f .hom x) (f .hom y) (f .hom meet)

  record preserves-finite-joins (f : Posets.Hom X Y) : Type (o ⊔ ℓ) where
    no-eta-equality
    field
      pres-bottoms
        : ∀ x
        → is-bottom X x
        → is-bottom Y (f .hom x)
      pres-joins
        : ∀ x y join
        → is-join X x y join
        → is-join Y (f .hom x) (f .hom y) (f .hom join)
```

<!--
```agda
  preserves-finite-meets-is-prop
    : (f : Posets.Hom X Y)
    → is-prop (preserves-finite-meets f)
  preserves-finite-meets-is-prop f =
    Iso→is-hlevel 1 eqv $
    Σ-is-hlevel 1 (hlevel 1) λ x →
    Π-is-hlevel³ 1 λ _ _ _ →
    Π-is-hlevel 1 λ _ → is-meet-is-prop Y
    where unquoteDecl eqv = declare-record-iso eqv (quote preserves-finite-meets)

  preserves-finite-joins-is-prop
    : (f : Posets.Hom X Y)
    → is-prop (preserves-finite-joins f)
  preserves-finite-joins-is-prop f =
    Iso→is-hlevel 1 eqv $
    Σ-is-hlevel 1 (hlevel 1) λ x →
    Π-is-hlevel³ 1 λ _ _ _ →
    Π-is-hlevel 1 λ _ → is-join-is-prop Y
    where unquoteDecl eqv = declare-record-iso eqv (quote preserves-finite-joins) 
```
-->

<!--
```agda
module _ where
  open Total-hom
  open preserves-finite-meets
  open preserves-finite-joins
```
-->

```agda

  preserves-finite-meets-id
    : ∀ {o ℓ} {X : Poset o ℓ}
    → preserves-finite-meets (Posets.id {x = X})

  preserves-finite-joins-id
    : ∀ {o ℓ} {X : Poset o ℓ}
    → preserves-finite-joins (Posets.id {x = X})

  preserves-finite-meets-∘
    : ∀ {o ℓ} {X Y Z : Poset o ℓ}
    → {f : Posets.Hom Y Z} {g : Posets.Hom X Y}
    → preserves-finite-meets f → preserves-finite-meets g
    → preserves-finite-meets (f Posets.∘ g)

  preserves-finite-joins-∘
    : ∀ {o ℓ} {X Y Z : Poset o ℓ}
    → {f : Posets.Hom Y Z} {g : Posets.Hom X Y}
    → preserves-finite-joins f → preserves-finite-joins g
    → preserves-finite-joins (f Posets.∘ g)
```

<!--
```agda
  preserves-finite-meets-id .pres-tops _ top = top
  preserves-finite-meets-id .pres-meets _ _ _ meet = meet


  preserves-finite-joins-id .pres-bottoms _ bot = bot
  preserves-finite-joins-id .pres-joins _ _ _ join = join

  preserves-finite-meets-∘ p q .pres-tops _ top =
    p .pres-tops _ (q .pres-tops _ top)
  preserves-finite-meets-∘ p q .pres-meets _ _ _ meet =
    p .pres-meets _ _ _ (q .pres-meets _ _ _ meet)

  preserves-finite-joins-∘ p q .pres-bottoms _ top =
    p .pres-bottoms _ (q .pres-bottoms _ top)
  preserves-finite-joins-∘ p q .pres-joins _ _ _ join =
    p .pres-joins _ _ _ (q .pres-joins _ _ _ join)
```
-->

# Categories of Semilattices

```agda
Meet-semilattices-subcat : ∀ o ℓ → Subcat (Posets o ℓ) (o ⊔ ℓ) (o ⊔ ℓ)
Meet-semilattices-subcat o ℓ .Subcat.is-ob = is-meet-semilattice
Meet-semilattices-subcat o ℓ .Subcat.is-hom f _ _ = preserves-finite-meets f
Meet-semilattices-subcat o ℓ .Subcat.is-hom-prop f _ _ = preserves-finite-meets-is-prop f
Meet-semilattices-subcat o ℓ .Subcat.is-hom-id _ = preserves-finite-meets-id
Meet-semilattices-subcat o ℓ .Subcat.is-hom-∘ = preserves-finite-meets-∘

Join-semilattices-subcat : ∀ o ℓ → Subcat (Posets o ℓ) (o ⊔ ℓ) (o ⊔ ℓ)
Join-semilattices-subcat o ℓ .Subcat.is-ob = is-join-semilattice
Join-semilattices-subcat o ℓ .Subcat.is-hom f _ _ = preserves-finite-joins f
Join-semilattices-subcat o ℓ .Subcat.is-hom-prop f _ _ = preserves-finite-joins-is-prop f
Join-semilattices-subcat o ℓ .Subcat.is-hom-id _ = preserves-finite-joins-id
Join-semilattices-subcat o ℓ .Subcat.is-hom-∘ = preserves-finite-joins-∘

Meet-semilattices : ∀ o ℓ → Precategory (lsuc (o ⊔ ℓ)) (o ⊔ ℓ)
Meet-semilattices o ℓ = Subcategory (Meet-semilattices-subcat o ℓ)

Join-semilattices : ∀ o ℓ → Precategory (lsuc (o ⊔ ℓ)) (o ⊔ ℓ)
Join-semilattices o ℓ = Subcategory (Join-semilattices-subcat o ℓ)

module Meet-semilattices {o} {ℓ} = Cat.Reasoning (Meet-semilattices o ℓ)
module Join-semilattices {o} {ℓ} = Cat.Reasoning (Join-semilattices o ℓ)

Meet-semilattice : ∀ o ℓ → Type _
Meet-semilattice o ℓ = Meet-semilattices.Ob {o} {ℓ}

Join-semilattice : ∀ o ℓ → Type _
Join-semilattice o ℓ = Join-semilattices.Ob {o} {ℓ}
```

<!--
```agda
{-# DISPLAY Meet-semilattices.Ob {o} {ℓ} = Meet-semilattice o ℓ #-}
{-# DISPLAY Join-semilattices.Ob {o} {ℓ} = Join-semilattice o ℓ #-}
```
-->

```agda
Meet-semilattices-is-category : ∀ {o ℓ} → is-category (Meet-semilattices o ℓ)
Meet-semilattices-is-category =
  subcat-is-category Posets-is-category is-meet-semilattice-is-prop

Join-semilattices-is-category : ∀ {o ℓ} → is-category (Join-semilattices o ℓ)
Join-semilattices-is-category =
  subcat-is-category Posets-is-category is-join-semilattice-is-prop
```


# Reasoning with Semilattices

```agda
module Meet-semilattice {o ℓ} (L : Meet-semilattice o ℓ) where
  poset : Poset o ℓ
  poset = L .fst

  set : Set o
  set = L .fst .fst

  open Poset poset public

  has-is-meet-semilattice : is-meet-semilattice poset
  has-is-meet-semilattice = L .snd

  open is-meet-semilattice has-is-meet-semilattice public
```

<!--
```agda
module Join-semilattice {o ℓ} (L : Join-semilattice o ℓ) where
  poset : Poset o ℓ
  poset = L .fst

  set : Set o
  set = L .fst .fst

  open Poset poset public

  has-is-join-semilattice : is-join-semilattice poset
  has-is-join-semilattice = L .snd

  open is-join-semilattice has-is-join-semilattice public
```
-->
