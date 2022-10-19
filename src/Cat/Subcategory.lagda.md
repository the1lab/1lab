```agda
module Cat.Subcategory where

open import Cat.Prelude
open import Cat.Displayed.Base
```

# Subcategories

```agda
record is-subcategory {o ℓ o′ ℓ′} {B : Precategory o ℓ} (E : Displayed B o′ ℓ′) :
  Type (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) where

  open Displayed E

  field
    prop-obj : ∀ X → is-prop Ob[ X ]
    prop-hom : ∀ {X Y} f (X′ : Ob[ X ]) (Y′ : Ob[ Y ]) → is-prop (Hom[ f ] X′ Y′)


record Subcategory {o ℓ} (B : Precategory o ℓ) (o′ ℓ′ : Level) :
  Type (o ⊔ ℓ ⊔ lsuc o′ ⊔ lsuc ℓ′) where
  field
    Subcat : Displayed B o′ ℓ′
    has-is-subcategory : is-subcategory Subcat

  open is-subcategory has-is-subcategory public
```

## Constructing Subcategories

```agda
record make-subcategory {o ℓ} (B : Precategory o ℓ) (o′ ℓ′ : Level) :
  Type (o ⊔ ℓ ⊔ lsuc o′ ⊔ lsuc ℓ′) where
  open Precategory B
  field
    Ob? : Ob → Prop o′
    Hom? : ∀ {X Y} → Hom X Y → ∣ Ob? X ∣ → ∣ Ob? Y ∣ → Prop ℓ′
    hom?-id : ∀ {X} → (PX : ∣ Ob? X ∣) → ∣ Hom? id PX PX ∣
    hom?-∘  : ∀ {X Y Z f g}
              → (PX : ∣ Ob? X ∣) → (PY : ∣ Ob? Y ∣) → (PZ : ∣ Ob? Z ∣)
              → ∣ Hom? f PY PZ ∣ → ∣ Hom? g PX PY ∣ → ∣ Hom? (f ∘ g) PX PZ ∣ 

to-subcategory : ∀ {o ℓ o′ ℓ′} {B : Precategory o ℓ}
                 → make-subcategory B o′ ℓ′ → Subcategory B o′ ℓ′
to-subcategory mk-subcat = subcat
  where
    open make-subcategory mk-subcat
    open Subcategory
    open Displayed

    subcat : Subcategory _ _ _
    subcat .Subcat .Ob[_] X = ∣ Ob? X ∣
    subcat .Subcat .Hom[_] f PX PY = ∣ Hom? f PX PY ∣
    subcat .Subcat .Hom[_]-set f PX PY = is-prop→is-set (is-tr (Hom? f PX PY))
    subcat .Subcat .id′ = hom?-id _
    subcat .Subcat ._∘′_ f g = hom?-∘ _ _ _ f g
    subcat .Subcat .idr′ f = is-prop→pathp (λ _ → is-tr (Hom? _ _ _)) _ _
    subcat .Subcat .idl′ f = is-prop→pathp (λ _ → is-tr (Hom? _ _ _)) _ _
    subcat .Subcat .assoc′ f g h = is-prop→pathp (λ _ → is-tr (Hom? _ _ _)) _ _
    subcat .has-is-subcategory .is-subcategory.prop-obj _ = is-tr (Ob? _)
    subcat .has-is-subcategory .is-subcategory.prop-hom _ _ _ = is-tr (Hom? _ _ _)
```

# Wide Subcategories

```agda
record is-wide-subcategory {o ℓ o′ ℓ′} {B : Precategory o ℓ} (E : Displayed B o′ ℓ′) :
  Type (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) where
  open Displayed E
  field
    contr-obj : ∀ X → is-contr Ob[ X ]
    prop-hom : ∀ {X Y} f (X′ : Ob[ X ]) (Y′ : Ob[ Y ]) → is-prop (Hom[ f ] X′ Y′)

  has-is-subcategory : is-subcategory E
  has-is-subcategory .is-subcategory.prop-obj X = is-contr→is-prop (contr-obj X)
  has-is-subcategory .is-subcategory.prop-hom = prop-hom

record Wide-subcategory {o ℓ} (B : Precategory o ℓ) (o′ ℓ′ : Level) :
  Type (o ⊔ ℓ ⊔ lsuc o′ ⊔ lsuc ℓ′) where
  field
    Subcat : Displayed B o′ ℓ′
    has-is-wide-subcategory : is-wide-subcategory Subcat

  open is-wide-subcategory has-is-wide-subcategory public
```

## Constructing Wide Subcategories

```agda
record make-wide-subcategory {o ℓ} (B : Precategory o ℓ) (ℓ′ : Level) :
  Type (o ⊔ ℓ ⊔ lsuc ℓ′) where
  open Precategory B
  field
    Hom? : ∀ {X Y} → Hom X Y → Prop ℓ′
    hom?-id : ∀ {X} → ∣ Hom? (id {X}) ∣
    hom?-∘  : ∀ {X Y Z} {f : Hom Y Z} {g : Hom X Y} → ∣ Hom? f ∣ → ∣ Hom? g ∣ → ∣ Hom? (f ∘ g) ∣ 

to-wide-subcategory : ∀ {o ℓ ℓ′} {B : Precategory o ℓ}
                      → make-wide-subcategory B ℓ′ → Wide-subcategory B lzero ℓ′
to-wide-subcategory mk-subcat = subcat
  where
    open make-wide-subcategory mk-subcat
    open Wide-subcategory
    open is-wide-subcategory
    open Displayed

    subcat : Wide-subcategory _ _ _
    Ob[ subcat .Subcat ] X = ⊤
    subcat .Subcat .Hom[_] f _ _ = ∣ Hom? f ∣
    subcat .Subcat .Hom[_]-set f _ _ = is-prop→is-set (is-tr (Hom? f))
    subcat .Subcat .id′ = hom?-id
    subcat .Subcat ._∘′_ = hom?-∘
    subcat .Subcat .idr′ _ = is-prop→pathp (λ _ → is-tr (Hom? _)) _ _
    subcat .Subcat .idl′ _ = is-prop→pathp (λ _ → is-tr (Hom? _)) _ _
    subcat .Subcat .assoc′ _ _ _ = is-prop→pathp (λ _ → is-tr (Hom? _)) _ _
    subcat .has-is-wide-subcategory .contr-obj _ = hlevel 0
    subcat .has-is-wide-subcategory .prop-hom _ _ _ = is-tr (Hom? _)
```

# Full Subcategories

```agda
record is-full-subcategory {o ℓ o′ ℓ′} {B : Precategory o ℓ} (E : Displayed B o′ ℓ′) :
  Type (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) where
  open Displayed E
  field
    prop-obj : ∀ X → is-prop Ob[ X ]
    contr-hom : ∀ {X Y} f (X′ : Ob[ X ]) (Y′ : Ob[ Y ]) → is-contr (Hom[ f ] X′ Y′)

  has-is-subcategory : is-subcategory E
  has-is-subcategory .is-subcategory.prop-obj = prop-obj
  has-is-subcategory .is-subcategory.prop-hom f PX PY = is-contr→is-prop (contr-hom f PX PY)

record Full-subcategory {o ℓ} (B : Precategory o ℓ) (o′ ℓ′ : Level) :
  Type (o ⊔ ℓ ⊔ lsuc o′ ⊔ lsuc ℓ′) where
  field
    Subcat : Displayed B o′ ℓ′
    has-is-full-subcategory : is-full-subcategory Subcat

  open is-full-subcategory has-is-full-subcategory public
```

## Constructing Full Subcategories

```agda
to-full-subcategory : ∀ {o ℓ o′} {B : Precategory o ℓ}
                      → (Precategory.Ob B → Prop o′)
                      → Full-subcategory B o′ lzero
to-full-subcategory Ob? = subcat
  where
    open Full-subcategory
    open is-full-subcategory
    open Displayed

    subcat : Full-subcategory _ _ _
    subcat .Subcat .Ob[_] X = ∣ Ob? X ∣
    subcat .Subcat .Hom[_] f PX PY = ⊤
    subcat .Subcat .Hom[_]-set _ _ _ = hlevel 2
    subcat .Subcat .id′ = tt
    subcat .Subcat ._∘′_ _ _ = tt
    subcat .Subcat .idr′ _ = refl
    subcat .Subcat .idl′ _ = refl
    subcat .Subcat .assoc′ _ _ _ = refl
    subcat .has-is-full-subcategory .prop-obj X = is-tr (Ob? X)
    subcat .has-is-full-subcategory .contr-hom _ _ _ = hlevel 0
```
