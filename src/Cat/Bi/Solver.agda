open import 1Lab.Reflection

open import Cat.Bi.Base
open import Cat.Prelude

import Cat.Bi.Reasoning as Br
import Cat.Morphism as Cm

module Cat.Bi.Solver where

module NbE {o ℓ ℓ'} (C : Prebicategory o ℓ ℓ') where

  open Br C
  open Cm._≅_
  open Hom hiding (id ; invr ; invl)
  open _=>_

  private variable
    W X Y Z : Ob

  data Expr₁ : Ob → Ob → SSet (o ⊔ ℓ) where
    _↑   : X ↦ Y → Expr₁ X Y
    `id  : Expr₁ X X
    _`⊗_ : Expr₁ Y Z → Expr₁ X Y → Expr₁ X Z

  ⟦_⟧₁ : Expr₁ X Y → X ↦ Y
  ⟦_⟧₁ (x ↑)    = x
  ⟦_⟧₁ `id      = id
  ⟦_⟧₁ (f `⊗ g) = ⟦ f ⟧₁ ⊗ ⟦ g ⟧₁

  data Expr₂ : Expr₁ X Y → Expr₁ X Y → SSet (o ⊔ ℓ ⊔ ℓ') where
    _↑   : {f g : Expr₁ X Y} → ⟦ f ⟧₁ ⇒ ⟦ g ⟧₁ → Expr₂ f g
    `id  : {f : Expr₁ X Y} → Expr₂ f f
    _`∘_ : {f g h : Expr₁ X Y} → Expr₂ g h → Expr₂ f g → Expr₂ f h
    -- _`◆_
    --   : {f₁ f₂ : Expr₁ Y Z} (α : Expr₂ f₁ f₂)
    --   → {g₁ g₂ : Expr₁ X Y} (β : Expr₂ g₁ g₂) → Expr₂ (f₁ `⊗ g₁) (f₂ `⊗ g₂)
    _`▶_
      : (f : Expr₁ Y Z) {g₁ g₂ : Expr₁ X Y} → Expr₂ g₁ g₂ → Expr₂ (f `⊗ g₁) (f `⊗ g₂)
    _`◀_
      : {f₁ f₂ : Expr₁ Y Z} → Expr₂ f₁ f₂ → (g : Expr₁ X Y) → Expr₂ (f₁ `⊗ g) (f₂ `⊗ g)
    -- α `◀ g = α `◆ `id {f = g}
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

  -- _`▶_
  --   : (f : Expr₁ Y Z) {g₁ g₂ : Expr₁ X Y} → Expr₂ g₁ g₂ → Expr₂ (f `⊗ g₁) (f `⊗ g₂)
  -- f `▶ β = `id {f = f} `◆ β

  -- _`◀_
  --   : {f₁ f₂ : Expr₁ Y Z} → Expr₂ f₁ f₂ → (g : Expr₁ X Y) → Expr₂ (f₁ `⊗ g) (f₂ `⊗ g)
  -- α `◀ g = α `◆ `id {f = g}

  infix 40 _`▶_
  infix 40 _`◀_

  `_ : {f g : X ↦ Y} → f ⇒ g → Expr₂ (f ↑) (g ↑)
  `_ f = f ↑

  infix 50 `_

  ⟦_⟧₂ : {f g : Expr₁ X Y} → Expr₂ f g → ⟦ f ⟧₁ ⇒ ⟦ g ⟧₁
  ⟦ x ↑ ⟧₂       = x
  ⟦ `id ⟧₂       = Hom.id
  ⟦ α `∘ β ⟧₂    = ⟦ α ⟧₂ ∘ ⟦ β ⟧₂
  ⟦ α `◀ β ⟧₂    = ⟦ α ⟧₂ ◀ _
  ⟦ α `▶ β ⟧₂    = _ ▶ ⟦ β ⟧₂
  ⟦ `λ← f ⟧₂     = λ← _
  ⟦ `λ→ f ⟧₂     = λ→ _
  ⟦ `ρ← f ⟧₂     = ρ← _
  ⟦ `ρ→ f ⟧₂     = ρ→ _
  ⟦ `α← f g h ⟧₂ = α← _
  ⟦ `α→ f g h ⟧₂ = α→ _

  --------------------------------------------------------------------------------
  -- Evaluation

  eval₁ : Expr₁ Y Z → Expr₁ X Y → Expr₁ X Z
  eval₁ (x ↑)    k = x ↑ `⊗ k
  eval₁ `id      k = k
  eval₁ (f `⊗ g) k = eval₁ f (eval₁ g k)

  nf₁ : Expr₁ X Y → X ↦ Y
  nf₁ e = ⟦ eval₁ e `id ⟧₁

  data Frame : (f g : Expr₁ X Y) → SSet (o ⊔ ℓ ⊔ ℓ') where
    _↑  : {f g : Expr₁ X Y} → ⟦ f ⟧₁ ⇒ ⟦ g ⟧₁ → Frame f g
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

  ⟦_⟧f : {f g : Expr₁ X Y} → Frame f g → ⟦ f ⟧₁ ⇒ ⟦ g ⟧₁
  ⟦ x ↑ ⟧f       = x
  ⟦ f `▷ x ⟧f    = ⟦ f ⟧₁ ▶ ⟦ x ⟧f
  ⟦ x `◁ f ⟧f    = ⟦ x ⟧f ◀ ⟦ f ⟧₁
  ⟦ `λ← f ⟧f     = λ← _
  ⟦ `λ→ f ⟧f     = λ→ _
  ⟦ `α← f g h ⟧f = α← _
  ⟦ `α→ f g h ⟧f = α→ _

  data Val₂ : (f g : Expr₁ X Y) → SSet (o ⊔ ℓ ⊔ ℓ') where
    `id  : {f : Expr₁ X Y} → Val₂ f f
    _↑   : {f g : Expr₁ X Y} → Frame f g → Val₂ f g
    _`∘_ : {f g h : Expr₁ X Y} → Val₂ g h → Val₂ f g → Val₂ f h

  ⟦_⟧vv : {f g : Expr₁ X Y} → Val₂ f g → ⟦ f ⟧₁ ⇒ ⟦ g ⟧₁
  ⟦ `id ⟧vv    = Hom.id
  ⟦ x ↑ ⟧vv    = ⟦ x ⟧f
  ⟦ x `∘ y ⟧vv = ⟦ x ⟧vv ∘ ⟦ y ⟧vv

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
  eval₂ (_`◀_ α β)            = eval₂ α
  eval₂ (_`▶_ α β)            = `whisker α (eval₂ β)
  eval₂ (`λ← f)               = `id
  eval₂ (`λ→ f)               = `id
  eval₂ (`ρ← f)               = `id
  eval₂ (`ρ→ f)               = `id
  eval₂ (`α← f g h)           = `id
  eval₂ (`α→ f g h)           = `id

  data FrameCompare : (f g : Expr₁ X Y) → SSet (o ⊔ ℓ ⊔ ℓ') where
    f-swap   : {f g h : Expr₁ X Y} → Frame g h → Frame f g → FrameCompare f h
    f-reduce : {f h : Expr₁ X Y} → Frame f h → FrameCompare f h
    f-stop   : {f h : Expr₁ X Y} → FrameCompare f h
    f-drop   : {f : Expr₁ X Y} → FrameCompare f f

  frame-compare : {f g h : Expr₁ X Y} → Frame g h → Frame f g → FrameCompare f h
  frame-compare (f `▷ x) (f `▷ y) with frame-compare x y
  ... | f-swap x' y' = f-swap (f `▷ x') (f `▷ y')
  ... | f-reduce z   = f-reduce (f `▷ z)
  ... | f-stop       = f-stop
  ... | f-drop       = f-drop
  frame-compare (x `◁ f) (y `◁ f) with frame-compare x y
  ... | f-swap x' y' = f-swap (x' `◁ f) (y' `◁ f)
  ... | f-reduce z   = f-reduce (z `◁ f)
  ... | f-stop       = f-stop
  ... | f-drop       = f-drop
  frame-compare (f `▷ x)        (y `◁ g)        = f-swap (y `◁ _) (_ `▷ x)
  frame-compare (f `▷ (g `▷ x)) (`α→ _ _ _)     = f-swap (`α→ f g _) ((f `⊗ g) `▷ x)
  frame-compare ((f `⊗ g) `▷ x) (`α← _ _ _)     = f-swap (`α← f g _) (f `▷ (g `▷ x))
  frame-compare (`id `▷ x)      (`λ→ _)         = f-swap (`λ→ _) x
  frame-compare (f `▷ x)        (`λ← _)         = f-swap (`λ← _) (`id `▷ (f `▷ x))
  frame-compare (`α→ _ _ _)     ((x `◁ f) `◁ g) = f-swap (x `◁ (f `⊗ g)) (`α→ _ _ _)
  frame-compare (`α← _ _ _)     (x `◁ (f `⊗ g)) = f-swap ((x `◁ f) `◁ g) (`α← _ _ _)
  frame-compare (`α← _ _ _)     (`α→ _ _ _)     = f-drop
  frame-compare (`α→ _ _ _)     (`α← _ _ _)     = f-drop
  frame-compare (`α← _ _ _)     (`λ→ _)         = f-reduce (`λ→ _ `◁ _)
  frame-compare (`λ→ _)         (`λ← _)         = f-drop
  frame-compare (`λ← _)         (`λ→ _)         = f-drop
  frame-compare (`λ← _)         (`α→ _ _ _)     = f-reduce (`λ← _ `◁ _)
  frame-compare _ _                             = f-stop

  data PushResult (f h : Expr₁ X Y) : SSet (o ⊔ ℓ ⊔ ℓ') where
    p-cont : {g : Expr₁ X Y} → Val₂ g h → Frame f g → PushResult f h
    p-stop : Val₂ f h → PushResult f h

  val₂-push : {f g h : Expr₁ X Y} → Frame g h → Val₂ f g → PushResult f h
  val₂-push x `id = p-cont `id x
  val₂-push x (y ↑) with frame-compare x y
  ... | f-swap x' y' = p-cont (x' ↑) y'
  ... | f-reduce z   = p-cont `id z
  ... | f-stop       = p-stop (x ↑ `∘ y ↑)
  ... | f-drop       = p-stop `id
  val₂-push x (ys `∘ zs) with val₂-push x ys
  ... | p-stop xys = p-stop (xys `∘ zs)
  ... | p-cont xys y with val₂-push y zs
  ... | p-stop yzs   = p-stop (xys `∘ yzs)
  ... | p-cont yzs z = p-cont (xys `∘ yzs) z

  val₂-merge : {f g h : Expr₁ X Y} → Val₂ g h → Val₂ f g → Val₂ f h
  val₂-merge `id ys = ys
  val₂-merge (x ↑) ys with val₂-push x ys
  ... | p-stop z     = z
  ... | p-cont ys' y = ys' `∘ y ↑
  val₂-merge (xs `∘ ys) zs = val₂-merge xs (val₂-merge ys zs)

  val₂-eval : {f g : Expr₁ X Y} {h : X ↦ Y} → Val₂ f g → h ⇒ ⟦ f ⟧₁ → h ⇒ ⟦ g ⟧₁
  val₂-eval `id        = λ z → z
  val₂-eval (x ↑)      = ⟦ x ⟧f ∘_
  val₂-eval (xs `∘ ys) = val₂-eval xs ⊙ val₂-eval ys

  nf₂ : {f g : Expr₁ X Y} → Expr₂ f g → nf₁ f ⇒ nf₁ g
  nf₂ e = val₂-eval (val₂-merge (eval₂ e) `id) Hom.id

  --------------------------------------------------------------------------------
  -- Soundness

  eval₁-sound : (e : Expr₁ Y Z) (k : Expr₁ X Y) → ⟦ eval₁ e k ⟧₁ ≅ ⟦ e ⟧₁ ⊗ ⟦ k ⟧₁
  eval₁-sound (x ↑) k     = id-iso
  eval₁-sound `id k       = λ≅
  eval₁-sound (e `⊗ e₁) k =
         eval₁-sound e (eval₁ e₁ k)
    ∙Iso ▶.F-map-iso (eval₁-sound e₁ k)
    ∙Iso α≅ Iso⁻¹

  nf₁-sound : (e : Expr₁ X Y) → nf₁ e ≅ ⟦ e ⟧₁
  nf₁-sound e = eval₁-sound e `id ∙Iso ρ≅ Iso⁻¹

  `whisker-sound
    : (f : Expr₁ Y Z) {h₁ h₂ : Expr₁ X Y} (α : Val₂ h₁ h₂)
    → eval₁-sound f h₂ .to ∘ ⟦ `whisker f α ⟧vv
    ≡ ⟦ f ⟧₁ ▶ ⟦ α ⟧vv ∘ eval₁-sound f h₁ .to
  `whisker-sound `id xs                         = λ→nat _
  `whisker-sound {_} {Z} {X} (f₁ `⊗ f₂) {h₁} xs =
    eval₁-sound (f₁ `⊗ f₂) _ .to ∘ ⟦ `whisker (f₁ `⊗ f₂) xs ⟧vv
      ≡⟨ cat! (Hom X Z) ⟩
    α← _ ∘ _ ∘ eval₁-sound f₁ _ .to ∘ ⟦ `whisker f₁ (`whisker f₂ xs) ⟧vv
      ≡⟨ refl⟩∘⟨ refl⟩∘⟨ `whisker-sound f₁ (`whisker f₂ xs) ⟩
    α← _ ∘ ⟦ f₁ ⟧₁ ▶ eval₁-sound f₂ _ .to ∘ ⟦ f₁ ⟧₁ ▶ ⟦ `whisker f₂ xs ⟧vv ∘ _
      ≡⟨ refl⟩∘⟨ ▶.extendl (`whisker-sound f₂ xs) ⟩
    α← _ ∘ ⟦ f₁ ⟧₁ ▶ (⟦ f₂ ⟧₁ ▶ ⟦ xs ⟧vv) ∘ ⟦ f₁ ⟧₁ ▶ eval₁-sound f₂ h₁ .to ∘ _
      ≡⟨ extendl (▶-assoc .from .is-natural _ _ _) ⟩
    (⟦ f₁ ⟧₁ ⊗ ⟦ f₂ ⟧₁) ▶ ⟦ xs ⟧vv ∘ α← _ ∘ ⟦ f₁ ⟧₁ ▶ eval₁-sound f₂ h₁ .to ∘ _
      ≡⟨ refl⟩∘⟨ assoc _ _ _ ⟩
    (⟦ f₁ ⟧₁ ⊗ ⟦ f₂ ⟧₁) ▶ ⟦ xs ⟧vv ∘ (α← _ ∘ ⟦ f₁ ⟧₁ ▶ eval₁-sound f₂ h₁ .to) ∘ _
      ∎
  `whisker-sound (f ↑) `id        = ▶.intro refl ⟩∘⟨refl
  `whisker-sound (f ↑) (x ↑)      = id-comm-sym
  `whisker-sound (f ↑) (xs `∘ ys) =
    Hom.id ∘ ⟦ `whisker (f ↑) xs ⟧vv ∘ ⟦ `whisker (f ↑) ys ⟧vv ≡⟨ extendl (`whisker-sound (f ↑) xs) ⟩
    f ▶ ⟦ xs ⟧vv ∘ Hom.id ∘ ⟦ `whisker (f ↑) ys ⟧vv            ≡⟨ refl⟩∘⟨ `whisker-sound (f ↑) ys ⟩
    f ▶ ⟦ xs ⟧vv ∘ f ▶ ⟦ ys ⟧vv ∘ Hom.id                       ≡⟨ ▶.pulll refl ⟩
    f ▶ (⟦ xs ⟧vv ∘ ⟦ ys ⟧vv) ∘ Hom.id                         ∎

  `eval₁-sound-to-sound
    : (g : Expr₁ Y Z) {f : Expr₁ X Y}
    → ⟦ `eval₁-sound-to g ⟧vv ≡ eval₁-sound g f .to
  `eval₁-sound-to-sound (g ↑)         = refl
  `eval₁-sound-to-sound `id           = refl
  `eval₁-sound-to-sound (g `⊗ g₁) {f} =
    _ ∘ ⟦ `eval₁-sound-to g ⟧vv ∘ ⟦ `whisker g (`eval₁-sound-to g₁) ⟧vv ≡⟨ refl⟩∘⟨ `eval₁-sound-to-sound g ⟩∘⟨refl ⟩
    _ ∘ eval₁-sound g _ .to ∘ ⟦ `whisker g (`eval₁-sound-to g₁) ⟧vv     ≡⟨ refl⟩∘⟨ `whisker-sound g (`eval₁-sound-to g₁) ⟩
    _ ∘ ⟦ g ⟧₁ ▶ ⟦ `eval₁-sound-to g₁ ⟧vv ∘ eval₁-sound g _ .to         ≡⟨ pulll (refl⟩∘⟨ ▶.⟨ `eval₁-sound-to-sound g₁ ⟩) ⟩
    eval₁-sound (g `⊗ g₁) f .to                                         ∎

  `eval₁-sound-from-sound
    : (g : Expr₁ Y Z) {f : Expr₁ X Y}
    → ⟦ `eval₁-sound-from g ⟧vv ≡ eval₁-sound g f .from
  `eval₁-sound-from-sound (g ↑)         = refl
  `eval₁-sound-from-sound `id           = refl
  `eval₁-sound-from-sound (g `⊗ g₁) {f} =
    let
      `whisker-sound' = sym $ swizzle
        (sym $ `whisker-sound g (`eval₁-sound-from g₁))
        (eval₁-sound g _ .invl) (eval₁-sound g _ .invr)
    in
      ⟦ `whisker g (`eval₁-sound-from g₁) ⟧vv ∘ ⟦ `eval₁-sound-from g ⟧vv ∘ _ ≡⟨ refl⟩∘⟨ `eval₁-sound-from-sound g ⟩∘⟨refl ⟩
      ⟦ `whisker g (`eval₁-sound-from g₁) ⟧vv ∘ eval₁-sound g _ .from ∘ _     ≡⟨ extendl `whisker-sound' ⟩
      eval₁-sound g _ .from ∘ ⟦ g ⟧₁ ▶ ⟦ `eval₁-sound-from g₁ ⟧vv ∘ _         ≡⟨ refl⟩∘⟨ ▶.⟨ `eval₁-sound-from-sound g₁ ⟩ ⟩∘⟨refl ⟩
      eval₁-sound (g `⊗ g₁) f .from                                           ∎

  eval₂-sound
    : {g h : Expr₁ Y Z} (α : Expr₂ g h) {k : Expr₁ X Y}
    → eval₁-sound h k .to ∘ ⟦ eval₂ α ⟧vv ≡ ⟦ α ⟧₂ ◀ ⟦ k ⟧₁ ∘ eval₁-sound g k .to
  eval₂-sound {g = g} {h} (α ↑) {k} =
    eval₁-sound h k .to ∘ ⟦ `eval₁-sound-from h ⟧vv ∘ α ◀ _ ∘ ⟦ `eval₁-sound-to g ⟧vv
      ≡⟨ refl⟩∘⟨ `eval₁-sound-from-sound h ⟩∘⟨refl ⟩
    eval₁-sound h k .to ∘ eval₁-sound h k .from ∘ α ◀ _ ∘ ⟦ `eval₁-sound-to g ⟧vv
      ≡⟨ cancell (eval₁-sound h _ .invl) ⟩
    α ◀ ⟦ k ⟧₁ ∘ ⟦ `eval₁-sound-to g ⟧vv
      ≡⟨ refl⟩∘⟨ `eval₁-sound-to-sound g ⟩
    (α ◀ ⟦ k ⟧₁) ∘ eval₁-sound g k .to
      ∎
  eval₂-sound `id                            = idr _ ∙ ◀.introl refl
  eval₂-sound (_`∘_ {f = f} {g} {h} α β) {k} =
    eval₁-sound h k .to ∘ ⟦ eval₂ α ⟧vv ∘ ⟦ eval₂ β ⟧vv     ≡⟨ extendl (eval₂-sound α) ⟩
    ⟦ α ⟧₂ ◀ ⟦ k ⟧₁ ∘ eval₁-sound g k .to ∘ ⟦ eval₂ β ⟧vv   ≡⟨ refl⟩∘⟨ eval₂-sound β ⟩
    ⟦ α ⟧₂ ◀ ⟦ k ⟧₁ ∘ ⟦ β ⟧₂ ◀ ⟦ k ⟧₁ ∘ eval₁-sound f k .to ≡⟨ ◀.pulll refl ⟩
    (⟦ α ⟧₂ ∘ ⟦ β ⟧₂) ◀ ⟦ k ⟧₁ ∘ eval₁-sound f k .to        ∎
  eval₂-sound {_} {Z} {X} (_`▶_ f {g₁} {g₂} β) {k} =
    ((α← _ ∘ (_ ▶ eval₁-sound g₂ k .to)) ∘ eval₁-sound f (eval₁ g₂ k) .to) ∘ ⟦ `whisker f (eval₂ β) ⟧vv
      ≡⟨ pullr (`whisker-sound f (eval₂ β)) ⟩
    (α← _ ∘ (_ ▶ eval₁-sound g₂ k .to)) ∘ ⟦ f ⟧₁ ▶ ⟦ eval₂ β ⟧vv ∘ eval₁-sound f (eval₁ g₁ k) .to
      ≡⟨ pullr (▶.extendl (eval₂-sound β)) ⟩
    (α← _ ∘ ⟦ f ⟧₁ ▶ (⟦ β ⟧₂ ◀ ⟦ k ⟧₁) ∘ ⟦ f ⟧₁ ▶ eval₁-sound g₁ k .to ∘ eval₁-sound f (eval₁ g₁ k) .to)
      ≡⟨ extendl (◀-▶-comm .from .is-natural _ _ _) ∙ ap₂ _∘_ refl (assoc _ _ _) ⟩
    (_ ▶ ⟦ β ⟧₂) ◀ _ ∘ (α← _ ∘ _ ▶ eval₁-sound g₁ k .to) ∘ eval₁-sound f (eval₁ g₁ k) .to
      ∎
  eval₂-sound {_} {Z} {X} (_`◀_ {f₁ = f₁} {f₂} α g) {k} =
    ((α← _ ∘ _ ▶ eval₁-sound g k .to) ∘ eval₁-sound f₂ (eval₁ g k) .to) ∘ ⟦ eval₂ α ⟧vv
      ≡⟨ pullr (eval₂-sound α) ⟩
    (α← _ ∘ _ ▶ eval₁-sound g k .to) ∘ ⟦ α ⟧₂ ◀ _ ∘ eval₁-sound f₁ (eval₁ g k) .to
      ≡⟨ pullr (extendl (compose.rlmap _ _)) ⟩
    α← _ ∘ ⟦ α ⟧₂ ◀ _ ∘ (_ ▶ eval₁-sound g k .to) ∘ eval₁-sound f₁ (eval₁ g k) .to
      ≡⟨ extendl (◀-assoc .to .is-natural _ _ _) ∙ ap₂ _∘_ refl (assoc _ _ _) ⟩
    (⟦ α ⟧₂ ◀ _) ◀ _ ∘ (α← _ ∘ _ ▶ eval₁-sound g k .to) ∘ eval₁-sound f₁ (eval₁ g k) .to
      ∎
  eval₂-sound (`λ← f) {k} =
    eval₁-sound f k .to ∘ Hom.id                           ≡⟨ idr _ ∙ intror (λ≅ .invr) ∙ extendl (sym $ λ←nat _) ⟩
    λ← _ ∘ id ▶ eval₁-sound f k .to ∘ λ→ _                 ≡⟨ pushl (sym (rswizzle (sym triangle-λ←) (α≅ .invl))) ⟩
    λ← _ ◀ ⟦ k ⟧₁ ∘ α← _ ∘ id ▶ eval₁-sound f k .to ∘ λ→ _ ≡⟨ refl⟩∘⟨ assoc _ _ _ ⟩
    λ← _ ◀ ⟦ k ⟧₁ ∘ eval₁-sound (`id `⊗ f) k .to           ∎
  eval₂-sound (`λ→ f) {k} =
    eval₁-sound (`id `⊗ f) k .to ∘ Hom.id ≡⟨ idr _ ∙ extendr (sym $ λ→nat _) ⟩
    (α← _ ∘ λ→ _) ∘ eval₁-sound f k .to   ≡⟨ lswizzle triangle-λ→ (α≅ .invr) ⟩∘⟨refl ⟩
    λ→ _ ◀ ⟦ k ⟧₁ ∘ eval₁-sound f k .to   ∎
  eval₂-sound (`ρ← f) =
    idr _ ∙ insertl (pulll (triangle _ _) ∙ ▶.annihilate (λ≅ .invr))
  eval₂-sound (`ρ→ f) {k} = idr _ ∙ ap (_∘ eval₁-sound f k .to) triangle-inv
  eval₂-sound {_} {Z} {X} (`α← f g h) {k} =
    eval₁-sound ((f `⊗ g) `⊗ h) k .to ∘ Hom.id
      ≡⟨ cat! (Hom X Z) ⟩
    α← _ ∘ (⟦ f ⟧₁ ⊗ ⟦ g ⟧₁) ▶ eval₁-sound h k .to ∘ α← _ ∘ _
      ≡⟨ refl⟩∘⟨ extendl (sym $ ▶-assoc .from .is-natural _ _ _) ⟩
    α← _ ∘ α← _ ∘ ⟦ f ⟧₁ ▶ (⟦ g ⟧₁ ▶ _) ∘ _
      ≡⟨ extendl (sym $ pentagon _ _ _ _) ⟩
    α← _ ◀ ⟦ k ⟧₁ ∘ (α← _ ∘ ⟦ f ⟧₁ ▶ α← _) ∘ ⟦ f ⟧₁ ▶ _ ∘ ⟦ f ⟧₁ ▶ _ ∘ _
      ≡˘⟨ refl⟩∘⟨ assoc _ _ _ ⟩
    _ ∘ _ ∘ ⟦ f ⟧₁ ▶ α← _ ∘ ⟦ f ⟧₁ ▶ (⟦ g ⟧₁ ▶ _) ∘ ⟦ f ⟧₁ ▶ _ ∘ _
      ≡⟨ refl⟩∘⟨ refl⟩∘⟨ ▶.pulll refl ∙ ▶.pulll refl ⟩
    α← _ ◀ ⟦ k ⟧₁ ∘ α← _ ∘ ⟦ f ⟧₁ ▶ _ ∘ _
      ≡⟨ refl⟩∘⟨ assoc _ _ _ ⟩
    α← _ ◀ ⟦ k ⟧₁ ∘ eval₁-sound (f `⊗ g `⊗ h) k .to
      ∎
  eval₂-sound {_} {Z} {X} (`α→ f g h) {k} =
    eval₁-sound (f `⊗ (g `⊗ h)) k .to ∘ Hom.id                         ≡⟨ cat! (Hom X Z) ⟩
    α← _ ∘ ⟦ f ⟧₁ ▶ ((α← _ ∘ ⟦ g ⟧₁ ▶ eval₁-sound h k .to) ∘ _) ∘ _    ≡⟨ refl⟩∘⟨ ▶.pushl refl ∙ ▶.pushl refl ⟩
    α← _ ∘ ⟦ f ⟧₁ ▶ α← _ ∘ ⟦ f ⟧₁ ▶ (⟦ g ⟧₁ ▶ eval₁-sound h k .to) ∘ _ ≡⟨ extendl (sym $ lswizzle (sym $ pentagon _ _ _ _) (◀.annihilate (α≅ .invl))) ⟩
    α→ _ ◀ ⟦ k ⟧₁ ∘ (α← _ ∘ α← _) ∘ ⟦ f ⟧₁ ▶ (⟦ g ⟧₁ ▶ _) ∘ _          ≡˘⟨ refl⟩∘⟨ assoc _ _ _ ⟩
    α→ _ ◀ ⟦ k ⟧₁ ∘ α← _ ∘ α← _ ∘ ⟦ f ⟧₁ ▶ (⟦ g ⟧₁ ▶ _) ∘ _            ≡⟨ refl⟩∘⟨ refl⟩∘⟨ extendl (▶-assoc .from .is-natural _ _ _) ⟩
    α→ _ ◀ ⟦ k ⟧₁ ∘ α← _ ∘ (⟦ f ⟧₁ ⊗ ⟦ g ⟧₁) ▶ _ ∘ α← _ ∘ _            ≡⟨ cat! (Hom X Z) ⟩
    α→ _ ◀ ⟦ k ⟧₁ ∘ eval₁-sound ((f `⊗ g) `⊗ h) k .to                  ∎

  fc-is-cont : {f g : Expr₁ X Y} → FrameCompare f g → Type
  fc-is-cont (f-swap _ _) = ⊤
  fc-is-cont (f-reduce _) = ⊤
  fc-is-cont f-drop       = ⊤
  fc-is-cont f-stop       = ⊥

  fc-embed
    : {f g : Expr₁ X Y} (cmp : FrameCompare f g) → fc-is-cont cmp → ⟦ f ⟧₁ ⇒ ⟦ g ⟧₁
  fc-embed (f-swap x y) _ = ⟦ x ⟧f ∘ ⟦ y ⟧f
  fc-embed (f-reduce x) _ = ⟦ x ⟧f
  fc-embed f-drop       _ = Hom.id

  fc-sound
    : {f g h : Expr₁ X Y} (x : Frame g h) (y : Frame f g)
    → {p : fc-is-cont (frame-compare x y)}
    → fc-embed (frame-compare x y) p ≡ ⟦ x ⟧f ∘ ⟦ y ⟧f
  fc-sound (f `▷ x) (f `▷ y) with frame-compare x y | fc-sound x y
  ... | f-swap _ _ | sound = ▶.weave sound
  ... | f-reduce _ | sound = ▶.expand sound
  ... | f-drop     | sound = sym (▶.annihilate (sym sound))
  fc-sound (x `◁ f) (y `◁ f) with frame-compare x y | fc-sound x y
  ... | f-swap _ _ | sound = ◀.weave sound
  ... | f-reduce _ | sound = ◀.expand sound
  ... | f-drop     | sound = sym (◀.annihilate (sym sound))
  fc-sound (f `▷ x)        (y `◁ g)        = compose.lrmap _ _
  fc-sound ((f `⊗ g) `▷ x) (`α← _ _ _)     = ▶-assoc .from .is-natural _ _ _
  fc-sound (f `▷ (g `▷ x)) (`α→ _ _ _)     = ▶-assoc .to .is-natural _ _ _
  fc-sound (`id `▷ x)      (`λ→ _)         = λ→nat _
  fc-sound (f `▷ x)        (`λ← _)         = λ←nat _
  fc-sound (`α→ _ _ _)     ((x `◁ f) `◁ g) = sym $ ◀-assoc .from .is-natural _ _ _
  fc-sound (`α← _ _ _)     (x `◁ (f `⊗ g)) = sym $ ◀-assoc .to .is-natural _ _ _
  fc-sound (`λ→ _)         (`λ← _)         = sym (λ≅ .invl)
  fc-sound (`λ← _)         (`λ→ _)         = sym (λ≅ .invr)
  fc-sound (`λ← _)         (`α→ _ _ _)     = sym triangle-λ←
  fc-sound (`α→ _ _ _)     (`α← _ _ _)     = sym (α≅ .invl)
  fc-sound (`α← _ _ _)     (`α→ _ _ _)     = sym (α≅ .invr)
  fc-sound (`α← _ _ _)     (`λ→ _)         = sym (lswizzle triangle-λ→ (α≅ .invr))

  pr-embed : {f g : Expr₁ X Y} → PushResult f g → ⟦ f ⟧₁ ⇒ ⟦ g ⟧₁
  pr-embed (p-cont x xs) = ⟦ x ⟧vv ∘ ⟦ xs ⟧f
  pr-embed (p-stop x)    = ⟦ x ⟧vv

  val₂-push-sound
    : {f g h : Expr₁ X Y} (x : Frame g h) (ys : Val₂ f g)
    → pr-embed (val₂-push x ys) ≡ ⟦ x ⟧f ∘ ⟦ ys ⟧vv
  val₂-push-sound x `id = id-comm-sym
  val₂-push-sound x (y ↑) with frame-compare x y | fc-sound x y
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
    → ⟦ val₂-merge xs ys ⟧vv ≡ ⟦ xs ⟧vv ∘ ⟦ ys ⟧vv
  val₂-merge-sound `id ys = sym (idl _)
  val₂-merge-sound (x ↑) ys with val₂-push x ys | val₂-push-sound x ys
  ... | p-stop _   | sound = sound
  ... | p-cont _ _ | sound = sound
  val₂-merge-sound (xs `∘ xs') ys =
    val₂-merge-sound xs (val₂-merge xs' ys) ∙ pushr (val₂-merge-sound xs' ys)

  val₂-eval-sound
    : {f g : Expr₁ X Y} {h : X ↦ Y} (xs : Val₂ f g) (k : h ⇒ ⟦ f ⟧₁)
    → val₂-eval xs k ≡ ⟦ xs ⟧vv ∘ k
  val₂-eval-sound `id k        = sym (idl _)
  val₂-eval-sound (x ↑) k      = refl
  val₂-eval-sound (xs `∘ ys) k =
    val₂-eval-sound xs (val₂-eval ys k) ∙ pushr (val₂-eval-sound ys k)

  nf₂-sound
    : {f g : Expr₁ X Y} (α : Expr₂ f g)
    → nf₁-sound g .to ∘ nf₂ α ≡ ⟦ α ⟧₂ ∘ nf₁-sound f .to
  nf₂-sound {f = f} {g} α =
    nf₁-sound g .to ∘ nf₂ α                          ≡⟨ refl⟩∘⟨ val₂-eval-sound (val₂-merge (eval₂ α) `id) Hom.id ∙ idr _ ⟩
    nf₁-sound g .to ∘ ⟦ val₂-merge (eval₂ α) `id ⟧vv ≡⟨ refl⟩∘⟨ val₂-merge-sound (eval₂ α) `id ∙ idr _ ⟩
    nf₁-sound g .to ∘ ⟦ eval₂ α ⟧vv                  ≡⟨ extendr (eval₂-sound α) ∙ sym (assoc _ _ _) ⟩
    ρ← ⟦ g ⟧₁ ∘ ⟦ α ⟧₂ ◀ id ∘ eval₁-sound f `id .to  ≡⟨ extendl (ρ←nat _) ⟩
    ⟦ α ⟧₂ ∘ nf₁-sound f .to                         ∎

  abstract
    solve : {f g : Expr₁ X Y} (α β : Expr₂ f g) → nf₂ α ≡ nf₂ β → ⟦ α ⟧₂ ≡ ⟦ β ⟧₂
    solve {f = f} {g} α β p =
      iso→epic (nf₁-sound f) _ _ $
      sym (nf₂-sound α) ∙ ap (nf₁-sound g .to ∘_) p ∙ nf₂-sound β


module Reflection where

  pattern category-args cat xs    = _ hm∷ _ hm∷ cat v∷ xs
  pattern functor-args functor xs =
    _ hm∷ _ hm∷ _ hm∷ _ hm∷ _ hm∷ _ hm∷ functor v∷ xs
  pattern iso-args f xs = _ hm∷ _ hm∷ _ h∷ _ h∷ _ h∷ f v∷ xs
  pattern nt-args nt xs = _ hm∷ _ hm∷ _ hm∷ _ hm∷ _ hm∷ _ hm∷ _ h∷ _ h∷ nt v∷ xs

  pattern “F₀” functor x =
    def (quote Functor.F₀) (functor-args functor (x v∷ []))

  pattern “F₁” functor x y f =
    def (quote Functor.F₁) (functor-args functor (x h∷ y h∷ f v∷ []))

  pattern “,” x y = con (quote _,_) (_ hm∷ _ hm∷ _ h∷ _ h∷ x v∷ y v∷ [])

  pattern “id₁” = def (quote Prebicategory.id) _

  pattern “compose” = def (quote Prebicategory.compose) _

  pattern “unitor-l” = def (quote Prebicategory.unitor-l) _

  pattern “unitor-r” = def (quote Prebicategory.unitor-r) _

  pattern “associator” = def (quote Prebicategory.associator) _

  pattern “to” f = def (quote Cm._≅_.to) (iso-args f [])

  pattern “from” f = def (quote Cm._≅_.from) (iso-args f [])

  pattern “η” f x = def (quote _=>_.η) (nt-args f (x v∷ []))

  pattern “⊗” f g = “F₀” (“F₀” “compose” f) g

  pattern “Hom” = def (quote Prebicategory.Hom) _

  pattern “id₂” f = def (quote Precategory.id) (category-args “Hom” (f h∷ []))

  pattern “∘” f g h α β =
    def (quote Precategory._∘_) (category-args “Hom” (f h∷ g h∷ h h∷ α v∷ β v∷ []))

  pattern “▶” f g₁ g₂ α = “F₁” (“F₀” “compose” f) g₁ g₂ α
  pattern “◀” f₁ f₂ α g = “η” (“F₁” “compose” f₁ f₂ α) g

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

    build-associator : Term → Name → Term → Term
    build-associator _ n (“,” f (“,” g h)) = con n (ef v∷ eg v∷ eh v∷ []) where
      ef = build-expr₁ f
      eg = build-expr₁ g
      eh = build-expr₁ h
    build-associator fallback _ _ = fallback

    build-def : Term → Term → Term → Term
    build-def f g α = con (quote NbE.Expr₂._↑) args where
      ef = build-expr₁ f
      eg = build-expr₁ g
      args = mk-hom-args cat (ef h∷ eg h∷ α v∷ [])

    build : Term → Term → Term → Term
    build _ _ (“id₂” f) = con (quote NbE.Expr₂.`id) (mk-hom-args cat (ef h∷ [])) where
      ef = build-expr₁ f
    build _ _ (“∘” f g h α β) = con (quote NbE.Expr₂._`∘_) (eα v∷ eβ v∷ []) where
      eα = build-expr₂ cat g h α
      eβ = build-expr₂ cat f g β
    build _ _ (“▶” f g₁ g₂ α) = con (quote NbE.Expr₂._`▶_) (build-expr₁ f v∷ build-expr₂ cat g₁ g₂ α v∷ [])
    build _ _ (“◀” g₁ g₂ α f) = con (quote NbE.Expr₂._`◀_) (build-expr₂ cat g₁ g₂ α v∷ build-expr₁ f v∷ [])
    build f g α@(“η” nnm na) with nnm
    ... | “from” “unitor-l”   = build-unitor (quote NbE.Expr₂.`λ←) na
    ... | “from” “unitor-r”   = build-unitor (quote NbE.Expr₂.`ρ←) na
    ... | “from” “associator” = build-associator (build-def f g α) (quote NbE.Expr₂.`α←) na
    ... | “to”   “unitor-l”   = build-unitor (quote NbE.Expr₂.`λ→) na
    ... | “to”   “unitor-r”   = build-unitor (quote NbE.Expr₂.`ρ→) na
    ... | “to”   “associator” = build-associator (build-def f g α) (quote NbE.Expr₂.`α→) na
    ... | _                   = build-def f g α
    build f g α = build-def f g α

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
    : f ▶ α→ (g , h , i) ∘ α→ (f , g ⊗ h , i) ∘ α→ (f , g , h) ◀ i
    ≡ α→ (f , g , h ⊗ i) ∘ α→ (f ⊗ g , h , i)
  test-pentagon-α→ = bicat! C

  test-triangle-ρ← : ρ← (f ⊗ g) ∘ α← (f , g , id) ≡ f ▶ ρ← g
  test-triangle-ρ← = bicat! C

  test-triangle-λ← : λ← (f ⊗ g) ∘ α→ (id , f , g) ≡ λ← f ◀ g
  test-triangle-λ← = bicat! C

  test-interchange : (α ∘ β) ◆ (γ ∘ δ) ≡ (α ◆ γ) ∘ (β ◆ δ)
  test-interchange = bicat! C

  test-interchange-whisker1 : (f ⊗ g) ▶ α ∘ δ ◀ g ≡ δ ◀ h ∘ i ▶ α
  test-interchange-whisker1 = bicat! C

  test-interchange-whisker2 : α ◀ i ∘ f ▶ β ∘ γ ≡ g ▶ β ∘ α ◀ h ∘ γ
  test-interchange-whisker2 = bicat! C

  test-exchange : (α ◆ β) ≡ (α ◀ f) ∘ (g ▶ β)
  test-exchange = bicat! C

  test-exchange2 : (α ◆ β) ≡ (g ▶ β) ∘ (α ◀ f)
  test-exchange2 = bicat! C
