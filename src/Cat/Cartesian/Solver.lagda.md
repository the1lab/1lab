---
description: |
  A solver for cartesian categories.
---
<!--
```agda
open import 1Lab.Reflection

open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Prelude

open import Data.Id.Base

import Cat.Reasoning
```
-->
```agda
module Cat.Cartesian.Solver where
```

```agda
module NbE
  {o ℓ} {C : Precategory o ℓ}
  (term : Terminal C)
  (prod : Binary-products C) where
  open Cat.Reasoning C
  open Binary-products prod
  open Terminal term
```

## Expressions


```agda
  data “Ob” : Type (o ⊔ ℓ) where
    “top” : “Ob”
    _“⊗”_ : “Ob” → “Ob” → “Ob”
    “_”   : Ob → “Ob”

  sem-ob : “Ob” → Ob
  sem-ob “top” = top
  sem-ob (X “⊗” Y) = sem-ob X ⊗₀ sem-ob Y
  sem-ob “ X ” = X

  instance
    Brackets-“Ob” : ⟦⟧-notation “Ob”
    Brackets-“Ob” .⟦⟧-notation.lvl = o
    Brackets-“Ob” .⟦⟧-notation.Sem = Ob
    Brackets-“Ob” .⟦⟧-notation.⟦_⟧ = sem-ob

  data “Hom” : “Ob” → “Ob” → Type (o ⊔ ℓ) where
    “id”    : ∀ {X} → “Hom” X X
    _“∘”_   : ∀ {X Y Z} → “Hom” Y Z → “Hom” X Y → “Hom” X Z
    “!”     : ∀ {X} → “Hom” X “top”
    “π₁”    : ∀ {X Y} → “Hom” (X “⊗” Y) X
    “π₂”    : ∀ {X Y} → “Hom” (X “⊗” Y) Y
    “⟨_,_⟩” : ∀ {X Y Z} → “Hom” X Y → “Hom” X Z → “Hom” X (Y “⊗” Z)
    “_”     : ∀ {X Y} → Hom ⟦ X ⟧ ⟦ Y ⟧ → “Hom” X Y

  sem-hom : ∀ {X Y} → “Hom” X Y → Hom ⟦ X ⟧ ⟦ Y ⟧
  sem-hom “id” = id
  sem-hom (f “∘” g) = sem-hom f ∘ sem-hom g
  sem-hom “!” = !
  sem-hom “π₁” = π₁
  sem-hom “π₂” = π₂
  sem-hom “⟨ f , g ⟩” = ⟨ sem-hom f , sem-hom g ⟩
  sem-hom “ f ” = f

  instance
    Brackets-“Hom” : ∀ {X Y} → ⟦⟧-notation (“Hom” X Y)
    Brackets-“Hom” .⟦⟧-notation.lvl = _
    Brackets-“Hom” .⟦⟧-notation.Sem = _
    Brackets-“Hom” .⟦⟧-notation.⟦_⟧ = sem-hom
```

## Values

```agda
  data Value : “Ob” → “Ob” → Type (o ⊔ ℓ) where
    vhom  : ∀ {X Y} → Hom ⟦ X ⟧ ⟦ Y ⟧ → Value X Y
    vbang : ∀ {X} → Value X “top”
    vpair : ∀ {X Y Z} → Value X Y → Value X Z → Value X (Y “⊗” Z)
```

```agda
  vfst : ∀ {X Y Z} → Value X (Y “⊗” Z) → Value X Y
  vfst (vhom f) = vhom (π₁ ∘ f)
  vfst (vpair v1 v2) = v1

  vsnd : ∀ {X Y Z} → Value X (Y “⊗” Z) → Value X Z
  vsnd (vhom f) = vhom (π₂ ∘ f)
  vsnd (vpair v1 v2) = v2

  vid : ∀ {X} → Value X X
  vid = vhom id
```

## Quotation

```agda
  reflect : ∀ X Y → Value X Y → Hom ⟦ X ⟧ ⟦ Y ⟧
  reflect X “top” v = !
  reflect X (Y “⊗” Z) v = ⟨ (reflect X Y (vfst v)) , reflect X Z (vsnd v) ⟩
  reflect X “ Y ” (vhom f) = f
```

## Evaluation

```agda
  eval : ∀ {X Y Z} → “Hom” Y Z → Value X Y → Value X Z
  eval “id” v = v
  eval (e1 “∘” e2) v = eval e1 (eval e2 v)
  eval “!” v = vbang
  eval “π₁” v = vfst v
  eval “π₂” v = vsnd v
  eval “⟨ e1 , e2 ⟩” v = vpair (eval e1 v) (eval e2 v)
  eval “ f ” v = vhom (f ∘ reflect _ _ v)
```

```agda
  nf : ∀ X Y → “Hom” X Y → Hom ⟦ X ⟧ ⟦ Y ⟧
  nf X Y e = reflect X Y (eval e vid)
```

## Soundness

```agda
  vhom-sound : ∀ X Y → (f : Hom ⟦ X ⟧ ⟦ Y ⟧) → reflect X Y (vhom f) ≡ f
  vhom-sound X “top” f = !-unique f
  vhom-sound X (Y “⊗” Z) f =
    ⟨ reflect X Y (vhom (π₁ ∘ f)) , reflect X Z (vhom (π₂ ∘ f)) ⟩ ≡⟨ ap₂ ⟨_,_⟩ (vhom-sound X Y (π₁ ∘ f)) (vhom-sound X Z (π₂ ∘ f)) ⟩
    ⟨ π₁ ∘ f , π₂ ∘ f ⟩                                           ≡˘⟨ ⟨⟩-unique refl refl ⟩
    f                                                             ∎
  vhom-sound X “ Y ” f = refl
```

```agda
  vfst-sound : ∀ X Y Z → (v : Value X (Y “⊗” Z)) → reflect X Y (vfst v) ≡ π₁ ∘ reflect X (Y “⊗” Z) v
  vfst-sound X Y Z (vhom f) =
    reflect X Y (vhom (π₁ ∘ f))       ≡⟨ vhom-sound X Y (π₁ ∘ f) ⟩
    π₁ ∘ f                            ≡˘⟨ refl⟩∘⟨ vhom-sound X (Y “⊗” Z) f ⟩
    π₁ ∘ reflect X (Y “⊗” Z) (vhom f) ∎
  vfst-sound X Y Z (vpair v1 v2) =
    reflect X Y v1                               ≡˘⟨ π₁∘⟨⟩ ⟩
    π₁ ∘ ⟨ (reflect X Y v1) , (reflect X Z v2) ⟩ ∎

  vsnd-sound : ∀ X Y Z → (v : Value X (Y “⊗” Z)) → reflect X Z (vsnd v) ≡ π₂ ∘ reflect X (Y “⊗” Z) v
  vsnd-sound X Y Z (vhom f) =
    reflect X Z (vhom (π₂ ∘ f))       ≡⟨ vhom-sound X Z (π₂ ∘ f) ⟩
    π₂ ∘ f                            ≡˘⟨ refl⟩∘⟨ vhom-sound X (Y “⊗” Z) f ⟩
    π₂ ∘ reflect X (Y “⊗” Z) (vhom f) ∎
  vsnd-sound X Y Z (vpair v1 v2) =
    reflect X Z v2                               ≡˘⟨ π₂∘⟨⟩ ⟩
    π₂ ∘ ⟨ (reflect X Y v1) , (reflect X Z v2) ⟩ ∎
```

```agda
  sound-k : ∀ X Y Z → (e : “Hom” Y Z) → (v : Value X Y)
          → reflect X Z (eval e v) ≡ ⟦ e ⟧ ∘ reflect X Y v
  sound-k X Y Y “id” v = sym (idl _)
  sound-k X Y Z (e1 “∘” e2) v =
    reflect X Z (eval e1 (eval e2 v)) ≡⟨ sound-k X _ Z e1 (eval e2 v) ⟩
    ⟦ e1 ⟧ ∘ reflect X _ (eval e2 v) ≡⟨ refl⟩∘⟨ sound-k X Y _ e2 v ⟩
    ⟦ e1 ⟧ ∘ ⟦ e2 ⟧ ∘ reflect X Y v ≡⟨ assoc _ _ _ ⟩
    ⟦ e1 “∘” e2 ⟧ ∘ reflect X Y v    ∎
  sound-k X Y “top” “!” v = !-unique (! ∘ reflect X Y v)
  sound-k X (Y “⊗” Z) Y “π₁” v = vfst-sound X Y Z v
  sound-k X (Y “⊗” Z) Z “π₂” v = vsnd-sound X Y Z v
  sound-k X Y (Z1 “⊗” Z2) “⟨ e1 , e2 ⟩” v =
    ⟨ reflect X Z1 (eval e1 v) , reflect X Z2 (eval e2 v) ⟩ ≡⟨ ap₂ ⟨_,_⟩ (sound-k X Y Z1 e1 v) (sound-k X Y Z2 e2 v) ⟩
    ⟨ ⟦ e1 ⟧ ∘ reflect X Y v , ⟦ e2 ⟧ ∘ reflect X Y v ⟩   ≡˘⟨ ⟨⟩∘ _ ⟩
    ⟨ ⟦ e1 ⟧ , ⟦ e2 ⟧ ⟩ ∘ reflect X Y v                   ∎
  sound-k X Y Z “ x ” v = vhom-sound X Z _
```

```agda
  sound : ∀ X Y → (e : “Hom” X Y) → nf X Y e ≡ ⟦ e ⟧
  sound X Y e = sound-k X X Y e vid ∙ elimr (vhom-sound X X id)
```

## Solver interface

```agda
  abstract
    solve : ∀ X Y → (e1 e2 : “Hom” X Y) → nf X Y e1 ≡ nf X Y e2 → ⟦ e1 ⟧ ≡ ⟦ e2 ⟧
    solve X Y e1 e2 p = sym (sound X Y e1) ·· p ·· sound X Y e2
```

```agda
module _
  {o ℓ} {C : Precategory o ℓ}
  {term : Terminal C}
  {prod : Binary-products C} where
  open Cat.Reasoning C
  open Binary-products prod
  open Terminal term
  open NbE term prod

  record Cartesian-ob (X : Ob) : Typeω where
    field
      “ob” : “Ob”
      ob-repr : ⟦ “ob” ⟧ ≡ᵢ X

  “ob” : (X : Ob) → ⦃ “X” : Cartesian-ob X ⦄ → “Ob”
  “ob” X ⦃ “X” ⦄ = Cartesian-ob.“ob” “X”

  ob-repr : (X : Ob) → ⦃ “X” : Cartesian-ob X ⦄ → ⟦ “ob” X ⟧ ≡ᵢ X
  ob-repr X ⦃ “X” ⦄ = Cartesian-ob.ob-repr “X”

  record Cartesian-hom
    {X Y : Ob}
    ⦃ “X” : Cartesian-ob X ⦄ ⦃ “Y” : Cartesian-ob Y ⦄
    (f : Hom X Y) : Typeω where
    field
      “hom” : “Hom” (“ob” X) (“ob” Y)

  “hom”
    : ∀ {X Y : Ob} → (f : Hom X Y)
    → ⦃ “X” : Cartesian-ob X ⦄ ⦃ “Y” : Cartesian-ob Y ⦄
    → ⦃ “f” : Cartesian-hom f ⦄
    → “Hom” (“ob” X) (“ob” Y)
  “hom” f ⦃ “f” = “f” ⦄ = Cartesian-hom.“hom” “f”

  instance
    Cartesian-ob-Default
      : ∀ {X} → Cartesian-ob X
    Cartesian-ob-Default {X = X} .Cartesian-ob.“ob” = NbE.“ X ”
    Cartesian-ob-Default .Cartesian-ob.ob-repr = reflᵢ
    {-# INCOHERENT Cartesian-ob-Default #-}

    Cartesian-ob-top
      : Cartesian-ob top
    Cartesian-ob-top .Cartesian-ob.“ob” = “top”
    Cartesian-ob-top .Cartesian-ob.ob-repr = reflᵢ

    Cartesian-ob-⊗₀
      : ∀ {X Y}
      → ⦃ “X” : Cartesian-ob X ⦄ ⦃ “Y” : Cartesian-ob Y ⦄
      → Cartesian-ob (X ⊗₀ Y)
    Cartesian-ob-⊗₀ {X = X} {Y = Y} .Cartesian-ob.“ob” =
      “ob” X “⊗” “ob” Y
    Cartesian-ob-⊗₀ {X = X} {Y = Y} .Cartesian-ob.ob-repr =
      ap₂ᵢ _⊗₀_ (ob-repr X) (ob-repr Y)

    Cartesian-hom-Default
      : ∀ {X Y} {f : Hom X Y}
      → ⦃ “X” : Cartesian-ob X ⦄ ⦃ “Y” : Cartesian-ob Y ⦄
      → Cartesian-hom f
    Cartesian-hom-Default {X = X} {Y = Y} {f = f} .Cartesian-hom.“hom” =
      “ substᵢ (λ X → Hom X ⟦ “ob” Y ⟧) (symᵢ (ob-repr X)) (substᵢ (λ Y → Hom X Y) (symᵢ (ob-repr Y)) f) ”
    {-# INCOHERENT Cartesian-hom-Default #-}

    Cartesian-hom-id
      : ∀ {X}
      → ⦃ “X” : Cartesian-ob X ⦄
      → Cartesian-hom (id {X})
    Cartesian-hom-id {X = X} .Cartesian-hom.“hom” = “id” {X = “ob” X}

    Cartesian-hom-∘
      : ∀ {X Y Z} {f : Hom Y Z} {g : Hom X Y}
      → ⦃ “X” : Cartesian-ob X ⦄ ⦃ “Y” : Cartesian-ob Y ⦄ ⦃ “Z” : Cartesian-ob Z ⦄
      → ⦃ “f” : Cartesian-hom f ⦄ ⦃ “g” : Cartesian-hom g ⦄
      → Cartesian-hom (f ∘ g)
    Cartesian-hom-∘ {f = f} {g = g} .Cartesian-hom.“hom” = “hom” f “∘” “hom” g

    Cartesian-hom-!
      : ∀ {X}
      → ⦃ “X” : Cartesian-ob X ⦄
      → Cartesian-hom (! {X})
    Cartesian-hom-! .Cartesian-hom.“hom” = “!”

    Cartesian-hom-π₁
      : ∀ {X Y}
      → ⦃ “X” : Cartesian-ob X ⦄ ⦃ “Y” : Cartesian-ob Y ⦄
      → Cartesian-hom (π₁ {X} {Y})
    Cartesian-hom-π₁ .Cartesian-hom.“hom” = “π₁”

    Cartesian-hom-π₂
      : ∀ {X Y}
      → ⦃ “X” : Cartesian-ob X ⦄ ⦃ “Y” : Cartesian-ob Y ⦄
      → Cartesian-hom (π₂ {X} {Y})
    Cartesian-hom-π₂ .Cartesian-hom.“hom” = “π₂”

    Cartesian-hom-⟨⟩
      : ∀ {X Y Z} {f : Hom X Y} {g : Hom X Z}
      → ⦃ “X” : Cartesian-ob X ⦄ ⦃ “Y” : Cartesian-ob Y ⦄ ⦃ “Z” : Cartesian-ob Z ⦄
      → ⦃ “f” : Cartesian-hom f ⦄ ⦃ “g” : Cartesian-hom g ⦄
      → Cartesian-hom ⟨ f , g ⟩
    Cartesian-hom-⟨⟩ {f = f} {g = g} .Cartesian-hom.“hom” = “⟨ “hom” f , “hom” g ⟩”

abstract
  solve-cartesian
    : ∀ {o h} {C : Precategory o h} (term : Terminal C) (prod : Binary-products C)
    → (let open Precategory C) (let open NbE term prod)
    → ∀ {X Y}
    → (f g : Hom X Y)
    → ⦃ “X” : Cartesian-ob X ⦄ ⦃ “Y” : Cartesian-ob Y ⦄
    → ⦃ “f” : Cartesian-hom f ⦄ ⦃ “g” : Cartesian-hom g ⦄
    → nf (“ob” X) (“ob” Y) (“hom” f) ≡ nf (“ob” X) (“ob” Y) (“hom” g)
    → ⟦ “hom” f ⟧ ≡ ⟦ “hom” g ⟧
  solve-cartesian term prod {X = X} {Y = Y} f g p =
    sym (NbE.sound term prod (“ob” X) (“ob” Y) (“hom” f))
    ·· p
    ·· NbE.sound term prod (“ob” X) (“ob” Y) (“hom” g)

macro
  cartesian!
    : ∀ {o ℓ} {C : Precategory o ℓ}
    → Terminal C
    → Binary-products C
    → Term → TC ⊤
  cartesian! term prod hole =
    withNormalisation false $ do
    goal ← infer-type hole >>= reduce
    just (lhs , rhs) ← get-boundary goal
      where nothing → typeError $ strErr "Can't determine boundary: " ∷
                                  termErr goal ∷ []
    “term” ← quoteTC term
    “prod” ← quoteTC prod
    unify hole (def (quote solve-cartesian) (“term” v∷ “prod” v∷ lhs v∷ rhs v∷ “refl” v∷ []))
```
