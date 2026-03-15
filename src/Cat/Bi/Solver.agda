open import 1Lab.Reflection

open import Cat.Bi.Base
open import Cat.Prelude

import Cat.Bi.Reasoning as Br
import Cat.Morphism as Cm

module Cat.Bi.Solver where

module NbE {o ℓ ℓ'} (C : Prebicategory o ℓ ℓ') where

  open Br C
  open Cm._≅_
  open Hom hiding (Hom ; Ob ; id ; _∘_ ; invr ; invl)
  open _=>_

  private variable
    W X Y Z : Ob

  data Expr₁ : Ob → Ob → Type (o ⊔ ℓ) where
    _↑   : X ↦ Y → Expr₁ X Y
    `id  : Expr₁ X X
    _`⊗_ : Expr₁ Y Z → Expr₁ X Y → Expr₁ X Z

  embed₁ : Expr₁ X Y → X ↦ Y
  embed₁ (x ↑)    = x
  embed₁ `id      = id
  embed₁ (f `⊗ g) = embed₁ f ⊗ embed₁ g

  instance
    ⟦⟧-Expr₁ : ⟦⟧-notation (Expr₁ X Y)
    ⟦⟧-Expr₁ = brackets _ embed₁

  data Expr₂ : Expr₁ X Y → Expr₁ X Y → Type (o ⊔ ℓ ⊔ ℓ') where
    _↑   : {f g : Expr₁ X Y} → ⟦ f ⟧ ⇒ ⟦ g ⟧ → Expr₂ f g
    `id  : {f : Expr₁ X Y} → Expr₂ f f
    _`∘_ : {f g h : Expr₁ X Y} → Expr₂ g h → Expr₂ f g → Expr₂ f h
    _`◆_
      : {f₁ f₂ : Expr₁ Y Z} (α : Expr₂ f₁ f₂)
      → {g₁ g₂ : Expr₁ X Y} (β : Expr₂ g₁ g₂) → Expr₂ (f₁ `⊗ g₁) (f₂ `⊗ g₂)
    `λ← : (f : Expr₁ X Y) → Expr₂ (`id `⊗ f) f
    `λ→ : (f : Expr₁ X Y) → Expr₂ f (`id `⊗ f)
    `ρ← : (f : Expr₁ X Y) → Expr₂ (f `⊗ `id) f
    `ρ→ : (f : Expr₁ X Y) → Expr₂ f (f `⊗ `id)
    `α←
      : (f : Expr₁ Z W) (g : Expr₁ Y Z) (h : Expr₁ X Y)
      → Expr₂ (f `⊗ (g `⊗ h)) ((f `⊗ g) `⊗ h)
    `α→
      : (f : Expr₁ Z W) (g : Expr₁ Y Z) (h : Expr₁ X Y)
      → Expr₂ ((f `⊗ g) `⊗ h) (f `⊗ (g `⊗ h))

  infix  50 _↑
  infixr 40 _`∘_
  infixr 30 _`⊗_
  infix 30 _`◆_

  _`▶_
    : (f : Expr₁ Y Z) {g₁ g₂ : Expr₁ X Y} → Expr₂ g₁ g₂ → Expr₂ (f `⊗ g₁) (f `⊗ g₂)
  f `▶ β = `id {f = f} `◆ β

  _`◀_
    : {f₁ f₂ : Expr₁ Y Z} → Expr₂ f₁ f₂ → (g : Expr₁ X Y) → Expr₂ (f₁ `⊗ g) (f₂ `⊗ g)
  α `◀ g = α `◆ `id {f = g}

  infix 40 _`▶_
  infix 40 _`◀_

  `_ : {f g : X ↦ Y} → f ⇒ g → Expr₂ (f ↑) (g ↑)
  `_ f = f ↑

  infix 50 `_

  embed₂ : {f g : Expr₁ X Y} → Expr₂ f g → ⟦ f ⟧ ⇒ ⟦ g ⟧
  embed₂ (x ↑)       = x
  embed₂ `id         = Hom.id
  embed₂ (α `∘ β)    = embed₂ α ∘ embed₂ β
  embed₂ (α `◆ β)    = embed₂ α ◆ embed₂ β
  embed₂ (`λ← f)     = λ← ⟦ f ⟧
  embed₂ (`λ→ f)     = λ→ ⟦ f ⟧
  embed₂ (`ρ← f)     = ρ← ⟦ f ⟧
  embed₂ (`ρ→ f)     = ρ→ ⟦ f ⟧
  embed₂ (`α← f g h) = α← ⟦ f ⟧ ⟦ g ⟧ ⟦ h ⟧
  embed₂ (`α→ f g h) = α→ ⟦ f ⟧ ⟦ g ⟧ ⟦ h ⟧

  instance
    ⟦⟧-Expr₂ : {f g : Expr₁ X Y} → ⟦⟧-notation (Expr₂ f g)
    ⟦⟧-Expr₂ = brackets _ embed₂

  --------------------------------------------------------------------------------
  -- Evaluation

  eval₁ : Expr₁ Y Z → Expr₁ X Y → Expr₁ X Z
  eval₁ (x ↑)    k = x ↑ `⊗ k
  eval₁ `id      k = k
  eval₁ (f `⊗ g) k = eval₁ f (eval₁ g k)

  nf₁ : Expr₁ X Y → X ↦ Y
  nf₁ e = ⟦ eval₁ e `id ⟧

  eval₁-sound : (e : Expr₁ Y Z) (k : Expr₁ X Y) → ⟦ eval₁ e k ⟧ ≅ ⟦ e ⟧ ⊗ ⟦ k ⟧
  eval₁-sound (x ↑) k     = id-iso
  eval₁-sound `id k       = λ≅
  eval₁-sound (e `⊗ e₁) k =
    eval₁-sound e (eval₁ e₁ k) ∙Iso
    ▶.F-map-iso (eval₁-sound e₁ k) ∙Iso
    α≅ Iso⁻¹

  nf₁-sound : (e : Expr₁ X Y) → nf₁ e ≅ ⟦ e ⟧
  nf₁-sound e = eval₁-sound e `id ∙Iso ρ≅ Iso⁻¹

  data Frame : (f g : Expr₁ X Y) → Type (o ⊔ ℓ ⊔ ℓ') where
    _↑  : {f g : Expr₁ X Y} → ⟦ f ⟧ ⇒ ⟦ g ⟧ → Frame f g
    `λ← : (f : Expr₁ X Y) → Frame (`id `⊗ f) f
    `λ→ : (f : Expr₁ X Y) → Frame f (`id `⊗ f)
    `α←
      : (f : Expr₁ Z W) (g : Expr₁ Y Z) (h : Expr₁ X Y)
      → Frame (f `⊗ (g `⊗ h)) ((f `⊗ g) `⊗ h)
    `α→
      : (f : Expr₁ Z W) (g : Expr₁ Y Z) (h : Expr₁ X Y)
      → Frame ((f `⊗ g) `⊗ h) (f `⊗ (g `⊗ h))
    _`▷_ : (f : Expr₁ Y Z) {g h : Expr₁ X Y} → Frame g h → Frame (f `⊗ g) (f `⊗ h)
    _`◁_ : {g h : Expr₁ Y Z} → Frame g h → (f : Expr₁ X Y) → Frame (g `⊗ f) (h `⊗ f)

  frame-embed : {f g : Expr₁ X Y} → Frame f g → ⟦ f ⟧ ⇒ ⟦ g ⟧
  frame-embed (x ↑)       = x
  frame-embed (f `▷ x)    = ⟦ f ⟧ ▶ frame-embed x
  frame-embed (x `◁ f)    = frame-embed x ◀ ⟦ f ⟧
  frame-embed (`λ← f)     = λ← ⟦ f ⟧
  frame-embed (`λ→ f)     = λ→ ⟦ f ⟧
  frame-embed (`α← f g h) = α← ⟦ f ⟧ ⟦ g ⟧ ⟦ h ⟧
  frame-embed (`α→ f g h) = α→ ⟦ f ⟧ ⟦ g ⟧ ⟦ h ⟧

  instance
    ⟦⟧-Frame : {f g : Expr₁ X Y} → ⟦⟧-notation (Frame f g)
    ⟦⟧-Frame = brackets _ frame-embed

  data Val₂ : (f g : Expr₁ X Y) → Type (o ⊔ ℓ ⊔ ℓ') where
    `id  : {f : Expr₁ X Y} → Val₂ f f
    _↑   : {f g : Expr₁ X Y} → Frame f g → Val₂ f g
    _`∘_ : {f g h : Expr₁ X Y} → Val₂ g h → Val₂ f g → Val₂ f h

  val₂-embed : {f g : Expr₁ X Y} → Val₂ f g → ⟦ f ⟧ ⇒ ⟦ g ⟧
  val₂-embed `id      = Hom.id
  val₂-embed (x ↑)    = ⟦ x ⟧
  val₂-embed (x `∘ y) = val₂-embed x Hom.∘ val₂-embed y

  instance
    ⟦⟧-Val₂ : {f g : Expr₁ X Y} → ⟦⟧-notation (Val₂ f g)
    ⟦⟧-Val₂ = brackets _ val₂-embed

  `whisker
    : (f : Expr₁ Y Z) {h₁ h₂ : Expr₁ X Y} → Val₂ h₁ h₂
    → Val₂ (eval₁ f h₁) (eval₁ f h₂)
  `whisker `id xs           = xs
  `whisker (f `⊗ f₁) xs     = `whisker f (`whisker f₁ xs)
  `whisker (f ↑) `id        = `id
  `whisker (f ↑) (x ↑)      = ((f ↑) `▷ x) ↑
  `whisker (f ↑) (xs `∘ ys) = `whisker (f ↑) xs `∘ `whisker (f ↑) ys

  `eval₁-sound-to : (g : Expr₁ Y Z) {k : Expr₁ X Y} → Val₂ (eval₁ g k) (g `⊗ k)
  `eval₁-sound-to (x ↑)     = `id
  `eval₁-sound-to `id       = `λ→ _ ↑
  `eval₁-sound-to (g `⊗ g₁) =
    `α← _ _ _ ↑ `∘ `eval₁-sound-to g `∘ `whisker g (`eval₁-sound-to g₁)

  `eval₁-sound-from : (g : Expr₁ Y Z) {k : Expr₁ X Y} → Val₂ (g `⊗ k) (eval₁ g k)
  `eval₁-sound-from (x ↑)     = `id
  `eval₁-sound-from `id       = `λ← _ ↑
  `eval₁-sound-from (g `⊗ g₁) =
    `whisker g (`eval₁-sound-from g₁) `∘ `eval₁-sound-from g `∘ `α→ _ _ _ ↑

  eval₂ : {g h : Expr₁ Y Z} → Expr₂ g h → {k : Expr₁ X Y} → Val₂ (eval₁ g k) (eval₁ h k)
  eval₂ {g = g} {h} (x ↑) {k} = `eval₁-sound-from h `∘ ((x ↑) `◁ k) ↑ `∘ `eval₁-sound-to g
  eval₂ `id                   = `id
  eval₂ (α `∘ β)              = eval₂ α `∘ eval₂ β
  eval₂ (_`◆_ {f₁ = f₁} α β)  = eval₂ α `∘ `whisker f₁ (eval₂ β)
  eval₂ (`λ← f)               = `id
  eval₂ (`λ→ f)               = `id
  eval₂ (`ρ← f)               = `id
  eval₂ (`ρ→ f)               = `id
  eval₂ (`α← f g h)           = `id
  eval₂ (`α→ f g h)           = `id

  data FrameCompare : (f g : Expr₁ X Y) → Type (o ⊔ ℓ ⊔ ℓ') where
    f-swap   : {f g h : Expr₁ X Y} → Frame g h → Frame f g → FrameCompare f h
    f-reduce : {f h : Expr₁ X Y} → Frame f h → FrameCompare f h
    f-stop   : {f h : Expr₁ X Y} → FrameCompare f h
    f-drop   : {f : Expr₁ X Y} → FrameCompare f f

  frame-compare : {f g h : Expr₁ X Y} → Frame g h → Frame f g → FrameCompare f h
  frame-compare (f `▷ x) (f `▷ y) = case frame-compare x y of λ where
    (f-swap x' y') → f-swap (f `▷ x') (f `▷ y')
    (f-reduce z)   → f-reduce (f `▷ z)
    f-stop         → f-stop
    f-drop         → f-drop
  frame-compare (x `◁ f) (y `◁ f) = case frame-compare x y of λ where
    (f-swap x' y') → f-swap (x' `◁ f) (y' `◁ f)
    (f-reduce z)   → f-reduce (z `◁ f)
    f-stop         → f-stop
    f-drop         → f-drop
  frame-compare (f `▷ x)        (y `◁ g)    = f-swap (y `◁ _) (_ `▷ x)
  frame-compare (f `▷ (g `▷ x)) (`α→ _ _ _) = f-swap (`α→ f g _) ((f `⊗ g) `▷ x)
  frame-compare ((f `⊗ g) `▷ x) (`α← _ _ _) = f-swap (`α← f g _) (f `▷ (g `▷ x))
  frame-compare (`id `▷ x)      (`λ→ _)     = f-swap (`λ→ _) x
  frame-compare (f `▷ x)        (`λ← _)     = f-swap (`λ← _) (`id `▷ (f `▷ x))
  frame-compare ((x `◁ f) `◁ g) (`α← _ _ _) = f-swap (`α← _ f g) (x `◁ (f `⊗ g))
  frame-compare (x `◁ (f `⊗ g)) (`α→ _ _ _) = f-swap (`α→ _ f g) ((x `◁ f) `◁ g)
  frame-compare (`λ→ _)         (`λ← _)     = f-drop
  frame-compare (`λ← _)         (`λ→ _)     = f-drop
  frame-compare (`λ← _)         (`α→ _ _ _) = f-reduce (`λ← _ `◁ _)
  frame-compare (`α← _ _ _)     (`α→ _ _ _) = f-drop
  frame-compare (`α→ _ _ _)     (`α← _ _ _) = f-drop
  frame-compare (`α← _ _ _)     (`λ→ _)     = f-reduce (`λ→ _ `◁ _)
  frame-compare _ _                         = f-stop

  data PushResult (f h : Expr₁ X Y) : Type (o ⊔ ℓ ⊔ ℓ') where
    p-cont : {g : Expr₁ X Y} → Val₂ g h → Frame f g → PushResult f h
    p-stop : Val₂ f h → PushResult f h

  val₂-push : {f g h : Expr₁ X Y} → Frame g h → Val₂ f g → PushResult f h
  val₂-push x `id   = p-cont `id x
  val₂-push x (y ↑) = case frame-compare x y of λ where
    (f-swap x' y') → p-cont (x' ↑) y'
    (f-reduce z)   → p-cont `id z
    f-stop         → p-stop (x ↑ `∘ y ↑)
    f-drop         → p-stop `id
  val₂-push x (ys `∘ zs) = case val₂-push x ys of λ where
    (p-stop xys)   → p-stop (xys `∘ zs)
    (p-cont xys y) → case val₂-push y zs of λ where
      (p-stop yzs)   → p-stop (xys `∘ yzs)
      (p-cont yzs z) → p-cont (xys `∘ yzs) z

  val₂-merge : {f g h : Expr₁ X Y} → Val₂ g h → Val₂ f g → Val₂ f h
  val₂-merge `id ys   = ys
  val₂-merge (x ↑) ys = case val₂-push x ys of λ where
    (p-stop z)     → z
    (p-cont ys' y) → ys' `∘ y ↑
  val₂-merge (xs `∘ ys) zs = val₂-merge xs (val₂-merge ys zs)

  val₂-eval : {f g : Expr₁ X Y} {h : X ↦ Y} → Val₂ f g → h ⇒ ⟦ f ⟧ → h ⇒ ⟦ g ⟧
  val₂-eval `id        = λ z → z
  val₂-eval (x ↑)      = ⟦ x ⟧ ∘_
  val₂-eval (xs `∘ ys) = val₂-eval xs ⊙ val₂-eval ys

  nf₂ : {f g : Expr₁ X Y} → Expr₂ f g → nf₁ f ⇒ nf₁ g
  nf₂ e = val₂-eval (val₂-merge (eval₂ e) `id) Hom.id

  --------------------------------------------------------------------------------
  -- Soundness

  `whisker-sound
    : (f : Expr₁ Y Z) {h₁ h₂ : Expr₁ X Y} (α : Val₂ h₁ h₂)
    → eval₁-sound f h₂ .to ∘ ⟦ `whisker f α ⟧ ≡ ⟦ f ⟧ ▶ ⟦ α ⟧ ∘ eval₁-sound f h₁ .to
  `whisker-sound `id xs                    = λ→nat _
  `whisker-sound {_} {Z} {X} (f₁ `⊗ f₂) xs =
    eval₁-sound (f₁ `⊗ f₂) _ .to ∘ ⟦ `whisker (f₁ `⊗ f₂) xs ⟧                   ≡⟨ cat! (Hom X Z) ⟩
    α← _ _ _ ∘ _ ∘ eval₁-sound f₁ _ .to ∘ ⟦ `whisker f₁ (`whisker f₂ xs) ⟧      ≡⟨ refl⟩∘⟨ refl⟩∘⟨ `whisker-sound f₁ (`whisker f₂ xs) ⟩
    α← _ _ _ ∘ ⟦ f₁ ⟧ ▶ eval₁-sound f₂ _ .to ∘ ⟦ f₁ ⟧ ▶ ⟦ `whisker f₂ xs ⟧ ∘ _  ≡⟨ refl⟩∘⟨ ▶.extendl (`whisker-sound f₂ xs) ⟩
    α← _ _ _ ∘ ⟦ f₁ ⟧ ▶ (⟦ f₂ ⟧ ▶ ⟦ xs ⟧) ∘ ⟦ f₁ ⟧ ▶ eval₁-sound f₂ _ .to ∘ _   ≡⟨ extendl (▶-assoc .from .is-natural _ _ _) ⟩
    (⟦ f₁ ⟧ ⊗ ⟦ f₂ ⟧) ▶ ⟦ xs ⟧ ∘ α← _ _ _ ∘ ⟦ f₁ ⟧ ▶ eval₁-sound f₂ _ .to ∘ _   ≡⟨ refl⟩∘⟨ assoc _ _ _ ⟩
    (⟦ f₁ ⟧ ⊗ ⟦ f₂ ⟧) ▶ ⟦ xs ⟧ ∘ (α← _ _ _ ∘ ⟦ f₁ ⟧ ▶ eval₁-sound f₂ _ .to) ∘ _ ∎
  `whisker-sound (f ↑) `id        = ▶.intro refl ⟩∘⟨refl
  `whisker-sound (f ↑) (x ↑)      = id-comm-sym
  `whisker-sound (f ↑) (xs `∘ ys) =
    Hom.id ∘ ⟦ `whisker (f ↑) xs ⟧ ∘ ⟦ `whisker (f ↑) ys ⟧ ≡⟨ extendl (`whisker-sound (f ↑) xs) ⟩
    f ▶ ⟦ xs ⟧ ∘ Hom.id ∘ ⟦ `whisker (f ↑) ys ⟧            ≡⟨ refl⟩∘⟨ `whisker-sound (f ↑) ys ⟩
    f ▶ ⟦ xs ⟧ ∘ f ▶ ⟦ ys ⟧ ∘ Hom.id                       ≡⟨ ▶.pulll refl ⟩
    f ▶ (⟦ xs ⟧ ∘ ⟦ ys ⟧) ∘ Hom.id                         ∎

  `eval₁-sound-to-sound
    : (g : Expr₁ Y Z) {f : Expr₁ X Y}
    → ⟦ `eval₁-sound-to g ⟧ ≡ eval₁-sound g f .to
  `eval₁-sound-to-sound (g ↑)         = refl
  `eval₁-sound-to-sound `id           = refl
  `eval₁-sound-to-sound (g `⊗ g₁) {f} =
    _ ∘ ⟦ `eval₁-sound-to g ⟧ ∘ ⟦ `whisker g (`eval₁-sound-to g₁) ⟧ ≡⟨ refl⟩∘⟨ `eval₁-sound-to-sound g ⟩∘⟨refl ⟩
    _ ∘ eval₁-sound g _ .to ∘ ⟦ `whisker g (`eval₁-sound-to g₁) ⟧   ≡⟨ refl⟩∘⟨ `whisker-sound g (`eval₁-sound-to g₁) ⟩
    _ ∘ ⟦ g ⟧ ▶ ⟦ `eval₁-sound-to g₁ ⟧ ∘ eval₁-sound g _ .to        ≡⟨ pulll (refl⟩∘⟨ ▶.⟨ `eval₁-sound-to-sound g₁ ⟩) ⟩
    eval₁-sound (g `⊗ g₁) f .to                                     ∎

  `eval₁-sound-from-sound
    : (g : Expr₁ Y Z) {f : Expr₁ X Y}
    → ⟦ `eval₁-sound-from g ⟧ ≡ eval₁-sound g f .from
  `eval₁-sound-from-sound (g ↑)         = refl
  `eval₁-sound-from-sound `id           = refl
  `eval₁-sound-from-sound (g `⊗ g₁) {f} =
    ⟦ `whisker g (`eval₁-sound-from g₁) ⟧ ∘ ⟦ `eval₁-sound-from g ⟧ ∘ _ ≡⟨ refl⟩∘⟨ `eval₁-sound-from-sound g ⟩∘⟨refl ⟩
    ⟦ `whisker g (`eval₁-sound-from g₁) ⟧ ∘ eval₁-sound g _ .from ∘ _   ≡⟨ extendl `whisker-sound' ⟩
    eval₁-sound g _ .from ∘ ⟦ g ⟧ ▶ ⟦ `eval₁-sound-from g₁ ⟧ ∘ _        ≡⟨ refl⟩∘⟨ ▶.⟨ `eval₁-sound-from-sound g₁ ⟩ ⟩∘⟨refl ⟩
    eval₁-sound (g `⊗ g₁) f .from                                       ∎
    where `whisker-sound' = sym $ swizzle
            (sym $ `whisker-sound g (`eval₁-sound-from g₁))
            (eval₁-sound g _ .invl) (eval₁-sound g _ .invr)

  eval₂-sound
    : {g h : Expr₁ Y Z} (α : Expr₂ g h) {k : Expr₁ X Y}
    → eval₁-sound h k .to ∘ ⟦ eval₂ α ⟧ ≡ ⟦ α ⟧ ◀ ⟦ k ⟧ ∘ eval₁-sound g k .to
  eval₂-sound {g = g} {h} (α ↑) {k} =
    eval₁-sound h k .to ∘ ⟦ `eval₁-sound-from h ⟧ ∘ α ◀ _ ∘ ⟦ `eval₁-sound-to g ⟧ ≡⟨ refl⟩∘⟨ `eval₁-sound-from-sound h ⟩∘⟨refl ⟩
    eval₁-sound h k .to ∘ eval₁-sound h k .from ∘ α ◀ _ ∘ ⟦ `eval₁-sound-to g ⟧   ≡⟨ cancell (eval₁-sound h _ .invl) ⟩
    α ◀ ⟦ k ⟧ ∘ ⟦ `eval₁-sound-to g ⟧                                             ≡⟨ refl⟩∘⟨ `eval₁-sound-to-sound g ⟩
    (α ◀ ⟦ k ⟧) ∘ eval₁-sound g k .to                                             ∎
  eval₂-sound `id                            = idr _ ∙ ◀.introl refl
  eval₂-sound (_`∘_ {f = f} {g} {h} α β) {k} =
    eval₁-sound h k .to ∘ ⟦ eval₂ α ⟧ ∘ ⟦ eval₂ β ⟧     ≡⟨ extendl (eval₂-sound α) ⟩
    ⟦ α ⟧ ◀ ⟦ k ⟧ ∘ eval₁-sound g k .to ∘ ⟦ eval₂ β ⟧   ≡⟨ refl⟩∘⟨ eval₂-sound β ⟩
    ⟦ α ⟧ ◀ ⟦ k ⟧ ∘ ⟦ β ⟧ ◀ ⟦ k ⟧ ∘ eval₁-sound f k .to ≡⟨ ◀.pulll refl ⟩
    (⟦ α ⟧ ∘ ⟦ β ⟧) ◀ ⟦ k ⟧ ∘ eval₁-sound f k .to       ∎
  eval₂-sound {_} {Z} {X} (_`◆_ {f₁ = f₁} {f₂} α {g₁} {g₂} β) {k} =
    eval₁-sound (f₂ `⊗ g₂) k .to ∘ ⟦ eval₂ α ⟧ ∘ ⟦ `whisker f₁ (eval₂ β) ⟧      ≡⟨ cat! (Hom X Z) ⟩
    _ ∘ _ ∘ eval₁-sound f₂ _ .to ∘ ⟦ eval₂ α ⟧ ∘ ⟦ `whisker f₁ (eval₂ β) ⟧      ≡⟨ refl⟩∘⟨ refl⟩∘⟨ extendl (eval₂-sound α) ∙ ap (⟦ α ⟧ ◀ _ ∘_) (`whisker-sound f₁ (eval₂ β)) ⟩
    _ ∘ ⟦ f₂ ⟧ ▶ eval₁-sound g₂ k .to ∘ ⟦ α ⟧ ◀ ⟦ eval₁ g₂ k ⟧ ∘ ⟦ f₁ ⟧ ▶ _ ∘ _ ≡⟨ refl⟩∘⟨ ⊗.extendl (id-comm-sym ,ₚ id-comm) ⟩
    _ ∘ _ ∘ ⟦ f₁ ⟧ ▶ eval₁-sound g₂ k .to ∘ ⟦ f₁ ⟧ ▶ ⟦ eval₂ β ⟧ ∘ _            ≡⟨ refl⟩∘⟨ refl⟩∘⟨ ▶.extendl (eval₂-sound β) ⟩
    α← _ _ _ ∘ ⟦ α ⟧ ◀ (⟦ g₂ ⟧ ⊗ ⟦ k ⟧) ∘ ⟦ f₁ ⟧ ▶ (⟦ β ⟧ ◀ ⟦ k ⟧) ∘ _          ≡⟨ extendl (◀-assoc .to .is-natural _ _ _) ⟩
    (⟦ α ⟧ ◀ ⟦ g₂ ⟧) ◀ ⟦ k ⟧ ∘ α← _ _ _ ∘ ⟦ f₁ ⟧ ▶ (⟦ β ⟧ ◀ ⟦ k ⟧) ∘ _          ≡⟨ refl⟩∘⟨ extendl (◀-▶-comm .from .is-natural _ _ _) ⟩
    (⟦ α ⟧ ◀ ⟦ g₂ ⟧) ◀ ⟦ k ⟧ ∘ (⟦ f₁ ⟧ ▶ ⟦ β ⟧) ◀ ⟦ k ⟧ ∘ α← _ _ _ ∘ _          ≡⟨ ◀.pulll (⊗.collapse (idr _ ,ₚ idl _)) ⟩
    (⟦ α ⟧ ◆ ⟦ β ⟧) ◀ ⟦ k ⟧ ∘ α← _ _ _ ∘ _                                      ≡⟨ refl ⟩∘⟨ assoc _ _ _ ⟩
    (⟦ α ⟧ ◆ ⟦ β ⟧) ◀ ⟦ k ⟧ ∘ eval₁-sound (f₁ `⊗ g₁) k .to                      ∎
  eval₂-sound (`λ← f) {k} =
    eval₁-sound f k .to ∘ Hom.id                              ≡⟨ idr _ ∙ intror (λ≅ .invr) ∙ extendl (sym $ λ←nat _) ⟩
    λ← _ ∘ id ▶ eval₁-sound f k .to ∘ λ→ _                    ≡⟨ pushl (sym (rswizzle (sym triangle-λ←) (α≅ .invl))) ⟩
    λ← _ ◀ ⟦ k ⟧ ∘ α← _ _ _ ∘ id ▶ eval₁-sound f k .to ∘ λ→ _ ≡⟨ refl⟩∘⟨ assoc _ _ _ ⟩
    λ← _ ◀ ⟦ k ⟧ ∘ eval₁-sound (`id `⊗ f) k .to               ∎
  eval₂-sound (`λ→ f) {k} =
    eval₁-sound (`id `⊗ f) k .to ∘ Hom.id   ≡⟨ idr _ ∙ extendr (sym $ λ→nat _) ⟩
    (α← _ _ _ ∘ λ→ _) ∘ eval₁-sound f k .to ≡⟨ lswizzle triangle-λ→ (α≅ .invr) ⟩∘⟨refl ⟩
    λ→ _ ◀ ⟦ k ⟧ ∘ eval₁-sound f k .to      ∎
  eval₂-sound (`ρ← f) =
    idr _ ∙ insertl (pulll (triangle _ _) ∙ ▶.annihilate (λ≅ .invr))
  eval₂-sound (`ρ→ f) {k} = idr _ ∙ ap (_∘ eval₁-sound f k .to) triangle-inv
  eval₂-sound {_} {Z} {X} (`α← f g h) {k} =
    eval₁-sound ((f `⊗ g) `⊗ h) k .to ∘ Hom.id                                   ≡⟨ cat! (Hom X Z) ⟩
    α← _ _ _ ∘ (⟦ f ⟧ ⊗ ⟦ g ⟧) ▶ eval₁-sound h k .to ∘ α← _ _ _ ∘ _              ≡⟨ refl⟩∘⟨ extendl (sym $ ▶-assoc .from .is-natural _ _ _) ⟩
    α← _ _ _ ∘ α← _ _ _ ∘ ⟦ f ⟧ ▶ (⟦ g ⟧ ▶ _) ∘ _                                ≡⟨ extendl (sym $ pentagon _ _ _ _) ⟩
    α← _ _ _ ◀ ⟦ k ⟧ ∘ (α← _ _ _ ∘ ⟦ f ⟧ ▶ α← _ _ _) ∘ ⟦ f ⟧ ▶ _ ∘ ⟦ f ⟧ ▶ _ ∘ _ ≡˘⟨ refl⟩∘⟨ assoc _ _ _ ⟩
    _ ∘ _ ∘ ⟦ f ⟧ ▶ α← _ _ _ ∘ ⟦ f ⟧ ▶ (⟦ g ⟧ ▶ _) ∘ ⟦ f ⟧ ▶ _ ∘ _               ≡⟨ refl⟩∘⟨ refl⟩∘⟨ ▶.pulll refl ∙ ▶.pulll refl ⟩
    α← _ _ _ ◀ ⟦ k ⟧ ∘ α← _ _ _ ∘ ⟦ f ⟧ ▶ _ ∘ _                                  ≡⟨ refl⟩∘⟨ assoc _ _ _ ⟩
    α← _ _ _ ◀ ⟦ k ⟧ ∘ eval₁-sound (f `⊗ g `⊗ h) k .to                           ∎
  eval₂-sound {_} {Z} {X} (`α→ f g h) {k} =
    eval₁-sound (f `⊗ (g `⊗ h)) k .to ∘ Hom.id                              ≡⟨ cat! (Hom X Z) ⟩
    α← _ _ _ ∘ ⟦ f ⟧ ▶ ((α← _ _ _ ∘ ⟦ g ⟧ ▶ eval₁-sound h k .to) ∘ _) ∘ _   ≡⟨ refl⟩∘⟨ ▶.pushl refl ∙ ▶.pushl refl ⟩
    α← _ _ _ ∘ ⟦ f ⟧ ▶ α← _ _ _ ∘ ⟦ f ⟧ ▶ (⟦ g ⟧ ▶ eval₁-sound h k .to) ∘ _ ≡⟨ extendl (sym $ lswizzle (sym $ pentagon _ _ _ _) (◀.annihilate (α≅ .invl))) ⟩
    α→ _ _ _ ◀ ⟦ k ⟧ ∘ (α← _ _ _ ∘ α← _ _ _) ∘ ⟦ f ⟧ ▶ (⟦ g ⟧ ▶ _) ∘ _      ≡˘⟨ refl⟩∘⟨ assoc _ _ _ ⟩
    α→ _ _ _ ◀ ⟦ k ⟧ ∘ α← _ _ _ ∘ α← _ _ _ ∘ ⟦ f ⟧ ▶ (⟦ g ⟧ ▶ _) ∘ _        ≡⟨ refl⟩∘⟨ refl⟩∘⟨ extendl (▶-assoc .from .is-natural _ _ _) ⟩
    α→ _ _ _ ◀ ⟦ k ⟧ ∘ α← _ _ _ ∘ (⟦ f ⟧ ⊗ ⟦ g ⟧) ▶ _ ∘ α← _ _ _ ∘ _        ≡⟨ cat! (Hom X Z) ⟩
    α→ _ _ _ ◀ ⟦ k ⟧ ∘ eval₁-sound ((f `⊗ g) `⊗ h) k .to                    ∎

  fc-is-cont : {f g : Expr₁ X Y} → FrameCompare f g → Type
  fc-is-cont (f-swap _ _) = ⊤
  fc-is-cont (f-reduce _) = ⊤
  fc-is-cont f-drop       = ⊤
  fc-is-cont f-stop       = ⊥

  fc-embed
    : {f g : Expr₁ X Y} (cmp : FrameCompare f g) → fc-is-cont cmp → ⟦ f ⟧ ⇒ ⟦ g ⟧
  fc-embed (f-swap x y) _ = ⟦ x ⟧ ∘ ⟦ y ⟧
  fc-embed (f-reduce x) _ = ⟦ x ⟧
  fc-embed f-drop       _ = Hom.id

  frame-compare-sound
    : {f g h : Expr₁ X Y} (x : Frame g h) (y : Frame f g)
    → {p : fc-is-cont (frame-compare x y)}
    → fc-embed (frame-compare x y) p ≡ ⟦ x ⟧ ∘ ⟦ y ⟧
  frame-compare-sound (f `▷ x) (f `▷ y)
    with frame-compare x y | frame-compare-sound x y
  ... | f-swap _ _ | sound = ▶.weave sound
  ... | f-reduce _ | sound = ▶.expand sound
  ... | f-drop     | sound = sym (▶.annihilate (sym sound))
  frame-compare-sound (x `◁ f) (y `◁ f)
    with frame-compare x y | frame-compare-sound x y
  ... | f-swap _ _ | sound = ◀.weave sound
  ... | f-reduce _ | sound = ◀.expand sound
  ... | f-drop     | sound = sym (◀.annihilate (sym sound))
  frame-compare-sound (f `▷ x)        (y `◁ g)    = ⊗.weave (id-comm ,ₚ id-comm-sym)
  frame-compare-sound (f `▷ (g `▷ x)) (`α→ _ _ _) = ▶-assoc .to .is-natural _ _ _
  frame-compare-sound ((f `⊗ g) `▷ x) (`α← _ _ _) = ▶-assoc .from .is-natural _ _ _
  frame-compare-sound (`id `▷ x)      (`λ→ _)     = λ→nat _
  frame-compare-sound (f `▷ x)        (`λ← _)     = λ←nat _
  frame-compare-sound (x `◁ (f `⊗ g)) (`α→ _ _ _) = ◀-assoc .from .is-natural _ _ _
  frame-compare-sound ((x `◁ f) `◁ g) (`α← _ _ _) = ◀-assoc .to .is-natural _ _ _
  frame-compare-sound (`λ→ _)         (`λ← _)     = sym (λ≅ .invl)
  frame-compare-sound (`λ← _)         (`λ→ _)     = sym (λ≅ .invr)
  frame-compare-sound (`λ← _)         (`α→ _ _ _) = sym triangle-λ←
  frame-compare-sound (`α→ _ _ _)     (`α← _ _ _) = sym (α≅ .invl)
  frame-compare-sound (`α← _ _ _)     (`α→ _ _ _) = sym (α≅ .invr)
  frame-compare-sound (`α← _ _ _)     (`λ→ _)     =
    sym (lswizzle triangle-λ→ (α≅ .invr))

  pr-embed : {f g : Expr₁ X Y} → PushResult f g → ⟦ f ⟧ ⇒ ⟦ g ⟧
  pr-embed (p-cont x xs) = ⟦ x ⟧ ∘ ⟦ xs ⟧
  pr-embed (p-stop x)    = ⟦ x ⟧

  val₂-push-sound
    : {f g h : Expr₁ X Y} (x : Frame g h) (ys : Val₂ f g)
    → pr-embed (val₂-push x ys) ≡ ⟦ x ⟧ ∘ ⟦ ys ⟧
  val₂-push-sound x `id = id-comm-sym
  val₂-push-sound x (y ↑) with frame-compare x y | frame-compare-sound x y
  ... | f-swap _ _ | sound = sound
  ... | f-reduce _ | sound = idl _ ∙ sound
  ... | f-drop     | sound = sound
  ... | f-stop     | _     = refl
  val₂-push-sound x (ys `∘ ys') with val₂-push x ys | val₂-push-sound x ys
  ... | p-stop _   | sound = pushl sound
  ... | p-cont _ y | sound with val₂-push y ys' | val₂-push-sound y ys'
  ... | p-stop _   | sound' = ap (_ ∘_) sound' ∙ extendl sound
  ... | p-cont _ _ | sound' = extendr sound' ∙ pushl sound

  val₂-merge-sound
    : {f g h : Expr₁ X Y} (xs : Val₂ g h) (ys : Val₂ f g)
    → ⟦ val₂-merge xs ys ⟧ ≡ ⟦ xs ⟧ ∘ ⟦ ys ⟧
  val₂-merge-sound `id ys = sym (idl _)
  val₂-merge-sound (x ↑) ys with val₂-push x ys | val₂-push-sound x ys
  ... | p-stop _   | sound = sound
  ... | p-cont _ _ | sound = sound
  val₂-merge-sound (xs `∘ xs') ys =
    val₂-merge-sound xs (val₂-merge xs' ys) ∙ pushr (val₂-merge-sound xs' ys)

  val₂-eval-sound
    : {f g : Expr₁ X Y} {h : X ↦ Y} (xs : Val₂ f g) (k : h ⇒ ⟦ f ⟧)
    → val₂-eval xs k ≡ ⟦ xs ⟧ ∘ k
  val₂-eval-sound `id k        = sym (idl _)
  val₂-eval-sound (x ↑) k      = refl
  val₂-eval-sound (xs `∘ ys) k =
    val₂-eval-sound xs (val₂-eval ys k) ∙ pushr (val₂-eval-sound ys k)

  nf₂-sound
    : {f g : Expr₁ X Y} (α : Expr₂ f g)
    → nf₁-sound g .to ∘ nf₂ α ≡ ⟦ α ⟧ ∘ nf₁-sound f .to
  nf₂-sound {f = f} {g} α =
    nf₁-sound g .to ∘ nf₂ α                        ≡⟨ refl⟩∘⟨ val₂-eval-sound (val₂-merge (eval₂ α) `id) Hom.id ∙ idr _ ⟩
    nf₁-sound g .to ∘ ⟦ val₂-merge (eval₂ α) `id ⟧ ≡⟨ refl⟩∘⟨ val₂-merge-sound (eval₂ α) `id ∙ idr _ ⟩
    nf₁-sound g .to ∘ ⟦ eval₂ α ⟧                  ≡⟨ extendr (eval₂-sound α) ∙ sym (assoc _ _ _) ⟩
    ρ← ⟦ g ⟧ ∘ ⟦ α ⟧ ◀ id ∘ eval₁-sound f `id .to  ≡⟨ extendl (ρ←nat _) ⟩
    ⟦ α ⟧ ∘ nf₁-sound f .to                        ∎

  abstract
    solve : {f g : Expr₁ X Y} (α β : Expr₂ f g) → nf₂ α ≡ nf₂ β → ⟦ α ⟧ ≡ ⟦ β ⟧
    solve {f = f} {g} α β p =
      iso→epic (nf₁-sound f) _ _ $
      sym (nf₂-sound α) ∙ ap (nf₁-sound g .to ∘_) p ∙ nf₂-sound β


module Reflection where

  pattern category-args Z xs      = _ hm∷ _ hm∷ Z v∷ xs
  pattern bicategory-args Z xs    = _ hm∷ _ hm∷ _ hm∷ Z v∷ xs
  pattern functor-args functor xs =
    _ hm∷ _ hm∷ _ hm∷ _ hm∷ _ hm∷ _ hm∷ functor v∷ xs
  pattern iso-args f xs = _ hm∷ _ hm∷ _ h∷ _ h∷ _ h∷ f v∷ xs
  pattern nt-args nt xs = _ hm∷ _ hm∷ _ hm∷ _ hm∷ _ hm∷ _ hm∷ _ h∷ _ h∷ nt v∷ xs

  pattern “F₀” functor x =
    def (quote Functor.F₀) (functor-args functor (x v∷ []))

  pattern “F₁” functor x y f =
    def (quote Functor.F₁) (functor-args functor (x h∷ y h∷ f v∷ []))

  pattern “,” x y =
    con (quote _,_) (_ hm∷ _ hm∷ _ h∷ _ h∷ x v∷ y v∷ [])

  pattern “id₁” =
    def (quote Prebicategory.id) (bicategory-args _ (_ h∷ []))

  pattern “compose” =
    (def (quote Prebicategory.compose) (bicategory-args _ (_ h∷ _ h∷ _ h∷ [])))

  pattern “unitor-l” =
    (def (quote Prebicategory.unitor-l) (bicategory-args _ (_ h∷ _ h∷ [])))

  pattern “unitor-r” =
    (def (quote Prebicategory.unitor-r) (bicategory-args _ (_ h∷ _ h∷ [])))

  pattern “associator” =
    (def (quote Prebicategory.associator) (bicategory-args _ (_ h∷ _ h∷ _ h∷ _ h∷ [])))

  pattern “to” f =
    (def (quote Cm._≅_.to) (iso-args f []))

  pattern “from” f =
    (def (quote Cm._≅_.from) (iso-args f []))

  pattern “η” f x =
    (def (quote _=>_.η) (nt-args f (x v∷ [])))

  pattern “⊗” f g = “F₀” “compose” (“,” f g)

  pattern “Hom” =
    (def (quote Prebicategory.Hom) (bicategory-args _ (_ v∷ _ v∷ [])))

  pattern “id₂” f =
    def (quote Precategory.id) (category-args “Hom” (f h∷ []))

  pattern “∘” f g h α β =
    def (quote Precategory._∘_) (category-args “Hom” (f h∷ g h∷ h h∷ α v∷ β v∷ []))

  pattern “◆” f₁ f₂ α g₁ g₂ β = “F₁” “compose” (“,” f₁ g₁) (“,” f₂ g₂) (“,” α β)

  pattern “λ←” f     = “η” (“from” “unitor-l”) f
  pattern “λ→” f     = “η” (“to” “unitor-l”) f
  pattern “ρ←” f     = “η” (“from” “unitor-r”) f
  pattern “ρ→” f     = “η” (“to” “unitor-r”) f
  pattern “α←” f g h = “η” (“from” “associator”) (“,” f (“,” g h))
  pattern “α→” f g h = “η” (“to” “associator”) (“,” f (“,” g h))

  mk-hom-args : Term → List (Arg Term) → List (Arg Term)
  mk-hom-args cat xs = infer-hidden 3 $ cat h∷ infer-hidden 2 xs

  “solve” : Term → Term → Term → Term
  “solve” cat lhs rhs =
    def (quote NbE.solve) (cat v∷ lhs v∷ rhs v∷ def (quote refl) [] v∷ [])

  “nf₂” : Term → Term → Term
  “nf₂” cat α = def (quote NbE.nf₂) (cat v∷ α v∷ [])

  build-expr₁ : Term → Term
  build-expr₁ “id₁”     = con (quote NbE.Expr₁.`id) []
  build-expr₁ (“⊗” f g) = con (quote NbE.Expr₁._`⊗_) (ef v∷ eg v∷ []) where
    ef = build-expr₁ f
    eg = build-expr₁ g
  build-expr₁ f = con (quote NbE.Expr₁._↑) (f v∷ [])

  build-expr₂ : Term → Term → Term → Term → Term
  build-expr₂ cat = build where
    build-unitor : Name → Term → Term
    build-unitor n f = con n (ef v∷ []) where
      ef = build-expr₁ f
    build-associator : Name → Term → Term → Term → Term
    build-associator n f g h = con n (ef v∷ eg v∷ eh v∷ []) where
      ef = build-expr₁ f
      eg = build-expr₁ g
      eh = build-expr₁ h

    build : Term → Term → Term → Term
    build _ _ (“id₂” f) = con (quote NbE.Expr₂.`id) (mk-hom-args cat (ef h∷ [])) where
      ef = build-expr₁ f
    build _ _ (“∘” f g h α β) = con (quote NbE.Expr₂._`∘_) (eα v∷ eβ v∷ []) where
      eα = build-expr₂ cat g h α
      eβ = build-expr₂ cat f g β
    build _ _ (“◆” f₁ f₂ α g₁ g₂ β) = con (quote NbE.Expr₂._`◆_) (eα v∷ eβ v∷ []) where
      eα = build-expr₂ cat f₁ f₂ α
      eβ = build-expr₂ cat g₁ g₂ β
    build _ _ (“λ←” f)     = build-unitor (quote NbE.Expr₂.`λ←) f
    build _ _ (“λ→” f)     = build-unitor (quote NbE.Expr₂.`λ→) f
    build _ _ (“ρ←” f)     = build-unitor (quote NbE.Expr₂.`ρ←) f
    build _ _ (“ρ→” f)     = build-unitor (quote NbE.Expr₂.`ρ→) f
    build _ _ (“α←” f g h) = build-associator (quote NbE.Expr₂.`α←) f g h
    build _ _ (“α→” f g h) = build-associator (quote NbE.Expr₂.`α→) f g h
    build f g α            = con (quote NbE.Expr₂._↑) args where
      ef = build-expr₁ f
      eg = build-expr₁ g
      args = mk-hom-args cat (ef h∷ eg h∷ α v∷ [])

  dont-reduce : List Name
  dont-reduce =
    [ quote Prebicategory.id
    , quote Prebicategory.compose
    , quote Prebicategory.unitor-l
    , quote Prebicategory.unitor-r
    , quote Prebicategory.associator
    , quote Prebicategory.Hom
    ]

module _ {o ℓ ℓ'} (C : Prebicategory o ℓ ℓ') where
  open Reflection
  open Prebicategory C
  module _ {X Y : Ob} {f g : X ↦ Y} {α β : f ⇒ g} where
    private
      bicat-worker : Term → TC ⊤
      bicat-worker hole =
        withNormalisation true $
        withReduceDefs (false , dont-reduce) $ do
        `α ← wait-for-type =<< quoteTC α
        `β ← quoteTC β
        `f ← quoteTC f
        `g ← quoteTC g
        `C ← quoteTC C
        noConstraints $ unify hole
          $ “solve” `C (build-expr₂ `C `f `g `α) (build-expr₂ `C `f `g `β)

    bicat-wrapper : {@(tactic bicat-worker) p : α ≡ β} → α ≡ β
    bicat-wrapper {p = p} = p

macro
  bicat! : Term → Term → TC ⊤
  bicat! c = flip unify (def (quote bicat-wrapper) (c v∷ []))

private module _ {o ℓ ℓ'} {C : Prebicategory o ℓ ℓ'} where
  open Prebicategory C
  variable
    X Y : Ob
    f g h i : X ↦ Y
    α β γ δ : f ⇒ g

  test-distrib-▶ : f ▶ (α ∘ β) ≡ f ▶ α ∘ f ▶ β
  test-distrib-▶ = bicat! C

  test-distrib-◀ : (α ∘ β) ◀ f ≡ α ◀ f ∘ β ◀ f
  test-distrib-◀ = bicat! C

  test-pentagon-α→
    : (f ▶ α→ g h i) ∘ α→ f (g ⊗ h) i ∘ (α→ f g h ◀ i)
    ≡ α→ f g (h ⊗ i) ∘ α→ (f ⊗ g) h i
  test-pentagon-α→ = bicat! C

  test-triangle-ρ← : ρ← (f ⊗ g) ∘ α← f g id ≡ f ▶ ρ← g
  test-triangle-ρ← = bicat! C

  test-triangle-λ← : λ← (f ⊗ g) ∘ α→ id f g ≡ λ← f ◀ g
  test-triangle-λ← = bicat! C

  test-interchange : (α ∘ β) ◆ (γ ∘ δ) ≡ (α ◆ γ) ∘ (β ◆ δ)
  test-interchange = bicat! C

  test-interchange-whisker : (f ⊗ g) ▶ α ∘ δ ◀ g ≡ δ ◀ h ∘ i ▶ α
  test-interchange-whisker = bicat! C
