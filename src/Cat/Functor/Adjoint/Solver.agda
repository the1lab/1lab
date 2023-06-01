open import Meta.Brackets
open import 1Lab.Prelude hiding (id; _∘_)
open import 1Lab.Reflection hiding (_∷r_)

open import Cat.Base
open import Cat.Functor.Adjoint

import Cat.Reasoning
import Cat.Functor.Reasoning

module Cat.Functor.Adjoint.Solver where

module NbE
  {oc ℓc od ℓd}
  {C : Precategory oc ℓc} {D : Precategory od ℓd}
  {L : Functor C D} {R : Functor D C}
  (adj : L ⊣ R)
  where
  private
    module C = Cat.Reasoning C
    module D = Cat.Reasoning D
    module L = Cat.Functor.Reasoning L
    module R = Cat.Functor.Reasoning R
    open _⊣_ adj

  --------------------------------------------------------------------------------
  -- Expressions

  data ‶C‶ : Type (oc ⊔ od)
  data ‶D‶ : Type (oc ⊔ od)

  data ‶C‶ where
    ‶_‶ : C.Ob → ‶C‶
    ‶R‶ : ‶D‶ → ‶C‶

  data ‶D‶ where
    ‶_‶ : D.Ob → ‶D‶
    ‶L‶ : ‶C‶ → ‶D‶

  C-ob : ‶C‶ → C.Ob
  D-ob : ‶D‶ → D.Ob

  C-ob ‶ x ‶ = x
  C-ob (‶R‶ x) = R.₀ (D-ob x)

  D-ob ‶ x ‶ = x
  D-ob (‶L‶ x) = L.₀ (C-ob x)

  instance
    ‶C‶-⟦-⟧ : ⟦-⟧-notation ‶C‶
    ‶C‶-⟦-⟧ = has-⟦-⟧ C.Ob C-ob

    ‶D‶-⟦-⟧ : ⟦-⟧-notation ‶D‶
    ‶D‶-⟦-⟧ = has-⟦-⟧ D.Ob D-ob

  data CExpr : ‶C‶ → ‶C‶ → Type (oc ⊔ od ⊔ ℓc ⊔ ℓd)
  data DExpr : ‶D‶ → ‶D‶ → Type (oc ⊔ od ⊔ ℓc ⊔ ℓd)

  data CExpr where
    ‶id‶ : ∀ {x} → CExpr x x
    _‶∘‶_ : ∀ {x y z} → CExpr y z → CExpr x y → CExpr x z
    ‶R‶ : ∀ {x y} → DExpr x y → CExpr (‶R‶ x) (‶R‶ y)
    ‶η‶ : ∀ x → CExpr x (‶R‶ (‶L‶ x))
    ‶_‶ : ∀ {x y} → C.Hom ⟦ x ⟧ ⟦ y ⟧ → CExpr x y

  data DExpr where
    ‶id‶ : ∀ {x} → DExpr x x
    _‶∘‶_ : ∀ {x y z} → DExpr y z → DExpr x y → DExpr x z
    ‶L‶ : ∀ {x y} → CExpr x y → DExpr (‶L‶ x) (‶L‶ y)
    ‶ε‶ : ∀ x → DExpr (‶L‶ (‶R‶ x)) x
    ‶_‶ : ∀ {x y} → D.Hom ⟦ x ⟧ ⟦ y ⟧ → DExpr x y

  C-hom : ∀ {x y} → CExpr x y → C.Hom ⟦ x ⟧ ⟦ y ⟧
  D-hom : ∀ {x y} → DExpr x y → D.Hom ⟦ x ⟧ ⟦ y ⟧

  C-hom ‶id‶ = C.id
  C-hom (f ‶∘‶ g) = C-hom f C.∘ C-hom g
  C-hom (‶R‶ f) = R.₁ (D-hom f)
  C-hom (‶η‶ x) = unit.η (C-ob x)
  C-hom ‶ f ‶ = f

  D-hom ‶id‶ = D.id
  D-hom (f ‶∘‶ g) = D-hom f D.∘ D-hom g
  D-hom (‶L‶ f) = L.₁ (C-hom f)
  D-hom (‶ε‶ x) = counit.ε (D-ob x)
  D-hom ‶ f ‶ = f

  instance
    CExpr-⟦-⟧ : ∀ {x y} → ⟦-⟧-notation (CExpr x y)
    CExpr-⟦-⟧ {x} {y} = has-⟦-⟧ (C.Hom ⟦ x ⟧ ⟦ y ⟧) C-hom

    DExpr-⟦-⟧ : ∀ {x y} → ⟦-⟧-notation (DExpr x y)
    DExpr-⟦-⟧ {x} {y} = has-⟦-⟧ (D.Hom ⟦ x ⟧ ⟦ y ⟧) D-hom

  --------------------------------------------------------------------------------
  -- Values

  data CFrame : ‶C‶ → ‶C‶ → Type (oc ⊔ od ⊔ ℓc ⊔ ℓd)
  data DFrame : ‶D‶ → ‶D‶ → Type (oc ⊔ od ⊔ ℓc ⊔ ℓd)

  data CFrame where
    khom : ∀ {x y} → C.Hom ⟦ x ⟧ ⟦ y ⟧ → CFrame x y
    krmap : ∀ {x y} → DFrame x y → CFrame (‶R‶ x) (‶R‶ y)
    kunit : ∀ x → CFrame x (‶R‶ (‶L‶ x))

  data DFrame where
    khom : ∀ {x y} → D.Hom ⟦ x ⟧ ⟦ y ⟧ → DFrame x y
    klmap : ∀ {x y} → CFrame x y → DFrame (‶L‶ x) (‶L‶ y)
    kcounit : ∀ x → DFrame (‶L‶ (‶R‶ x)) x

  data CValue : ‶C‶ → ‶C‶ → Type (oc ⊔ od ⊔ ℓc ⊔ ℓd)
  data DValue : ‶D‶ → ‶D‶ → Type (oc ⊔ od ⊔ ℓc ⊔ ℓd)

  data CValue where
    [] : ∀ {x} → CValue x x
    _∷_ : ∀ {x y z} → CFrame y z → CValue x y → CValue x z

  -- Uphold snoc list thought!
  data DValue where
    [] : ∀ {x} → DValue x x
    _∷r_ : ∀ {x y z} → DValue y z → DFrame x y → DValue x z

  infixr 20 _∷_
  infixl 20 _∷r_

  C-frame : ∀ {x y} → CFrame x y → C.Hom ⟦ x ⟧ ⟦ y ⟧
  D-frame : ∀ {x y} → DFrame x y → D.Hom ⟦ x ⟧ ⟦ y ⟧

  C-frame (khom f) = f
  C-frame (krmap k) = R.F₁ (D-frame k)
  C-frame (kunit x) = unit.η ⟦ x ⟧

  D-frame (khom f) = f
  D-frame (klmap k) = L.F₁ (C-frame k)
  D-frame (kcounit x) = counit.ε ⟦ x ⟧

  instance
    CFrame-⟦-⟧ : ∀ {x y} → ⟦-⟧-notation (CFrame x y)
    CFrame-⟦-⟧ {x} {y} = has-⟦-⟧ (C.Hom ⟦ x ⟧ ⟦ y ⟧) C-frame

    DFrame-⟦-⟧ : ∀ {x y} → ⟦-⟧-notation (DFrame x y)
    DFrame-⟦-⟧ {x} {y} = has-⟦-⟧ (D.Hom ⟦ x ⟧ ⟦ y ⟧) D-frame

  C-value : ∀ {x y} → CValue x y → C.Hom ⟦ x ⟧ ⟦ y ⟧
  C-value [] = C.id
  C-value (k ∷ v) = ⟦ k ⟧ C.∘ C-value v

  D-value : ∀ {x y} → DValue x y → D.Hom ⟦ x ⟧ ⟦ y ⟧
  D-value [] = D.id
  D-value (v ∷r k) = D-value v D.∘ ⟦ k ⟧

  instance
    CValue-⟦-⟧ : ∀ {x y} → ⟦-⟧-notation (CValue x y)
    CValue-⟦-⟧ {x} {y} = has-⟦-⟧ (C.Hom ⟦ x ⟧ ⟦ y ⟧) C-value

    DValue-⟦-⟧ : ∀ {x y} → ⟦-⟧-notation (DValue x y)
    DValue-⟦-⟧ {x} {y} = has-⟦-⟧ (D.Hom ⟦ x ⟧ ⟦ y ⟧) D-value

  --------------------------------------------------------------------------------
  -- Evaluation
  --
  -- The solver needs to accomplish 3 main goals:
  -- * Expanding 'L₁' and 'R₁'
  -- * Enact the 'zig' and 'zag' equations.
  -- * Apply naturality for 'ε' and 'η'
  --
  -- The first goal is handled by the shape of normal forms.
  -- To be able to enact the 'zig' and 'zag' equations, we need
  -- to get the unit/counit as close to one another as possible by applying
  -- naturality. This means floating the unit up the stack, and sinking the
  -- counit down the stack.
  -- This allows us to eliminate 'kcounit'/'kunit' pairs when we append stacks.

  -- Concatenate 2 CValues together, performing no simplification.
  _++c_ : ∀ {x y z} → CValue y z → CValue x y → CValue x z
  [] ++c v2 = v2
  (k ∷ v1) ++c v2 = k ∷ (v1 ++c v2)

  -- Concatenate 2 DValues together, performing no simplification.
  _++d_ : ∀ {x y z} → DValue y z → DValue x y → DValue x z
  v1 ++d [] = v1
  v1 ++d (v2 ∷r k) = (v1 ++d v2) ∷r k
  -- [] ++d v2 = v2
  -- (v1 ∷ʳ v1) ++d v2 = k ∷ (v1 ++d v2)


  -- Apply R₁ to a value.
  do-vrmap : ∀ {x y z} → DValue y z → CValue x (‶R‶ y) → CValue x (‶R‶ z)
  do-vrmap [] v2 = v2
  do-vrmap (v1 ∷r k) v2 = do-vrmap v1 (krmap k ∷ v2)

  -- Apply L₁ to a value.
  do-vlmap : ∀ {x y z}  → DValue (‶L‶ y) z → CValue x y  → DValue (‶L‶ x) z
  do-vlmap v1 [] = v1
  do-vlmap v1 (k ∷ v2) = do-vlmap (v1 ∷r klmap k) v2


  -- The meat of the solver: Float 'kunit' frames upwards, and sink 'kcounit' frames
  -- downward.
  enact-claws : ∀ {w x y z} → CFrame y z → CFrame x y → CValue w x → CValue w z
  enact-dlaws : ∀ {w x y z} → DValue y z → DFrame x y → DFrame w x → DValue w z
  push-cframe : ∀ {x y z} → CFrame y z → CValue x y → CValue x z
  push-dframe : ∀ {x y z} → DValue y z → DFrame x y → DValue x z

  enact-claws (khom f) k' v = khom f ∷ k' ∷ v
  enact-claws (krmap k) (khom f) v = krmap k ∷ khom f ∷ v
  enact-claws (krmap k) (krmap k') v = do-vrmap (enact-dlaws [] k k') [] ++c v -- Expand functor applications. We don't do extra simplification to avoid loops.
  enact-claws (krmap (khom f)) (kunit _) v = krmap (khom f) ∷ kunit _ ∷ v
  enact-claws (krmap (klmap k)) (kunit _) v = kunit _ ∷ push-cframe k v        -- Apply naturality, floating 'kunit' upwards.
  enact-claws (krmap (kcounit _)) (kunit _) v = v                              -- Enact the 'zag' equation.
  enact-claws (kunit _) k' v = kunit _ ∷ k' ∷ v

  enact-dlaws v k (khom f) = v ∷r k ∷r khom f
  enact-dlaws v (khom f) (klmap k) = v ∷r khom f ∷r klmap k
  enact-dlaws v (klmap k') (klmap k) = v ++d do-vlmap [] (enact-claws k' k []) -- Expand functor applications. We don't do extra simplification to avoid loops.
  enact-dlaws v (kcounit _) (klmap (khom f)) = v ∷r kcounit _ ∷r klmap (khom f)
  enact-dlaws v (kcounit _) (klmap (krmap k)) = push-dframe v k ∷r kcounit _   -- Apply naturality, sinking 'kcounit' downwards.
  enact-dlaws v (kcounit _) (klmap (kunit _)) = v                              -- Enact the 'zig' equation.
  enact-dlaws v k' (kcounit _) = v ∷r k' ∷r kcounit _

  push-cframe k [] = k ∷ []
  push-cframe k (k' ∷ v) = enact-claws k k' v

  push-dframe [] k = [] ∷r k
  push-dframe (v ∷r k') k = enact-dlaws v k' k

  -- Concatenate 2 stacks together, performing simplification via 'enact-claws'.
  do-cvcomp : ∀ {x y z} → CValue y z → CValue x y → CValue x z
  do-cvcomp [] v2 = v2
  do-cvcomp (k ∷ v1) v2 = push-cframe k (do-cvcomp v1 v2)

  -- Concatenate 2 stacks together, performing simplification via 'enact-dlaws'.
  do-dvcomp : ∀ {x y z} → DValue y z → DValue x y → DValue x z
  do-dvcomp v1 [] = v1
  do-dvcomp v1 (v2 ∷r k) = push-dframe (do-dvcomp v1 v2) k

  C-eval : ∀ {x y} → CExpr x y → CValue x y
  D-eval : ∀ {x y} → DExpr x y → DValue x y

  C-eval ‶id‶ = []
  C-eval (f ‶∘‶ g) = do-cvcomp (C-eval f) (C-eval g)
  C-eval (‶R‶ f) = do-vrmap (D-eval f) []
  C-eval (‶η‶ x) = kunit x ∷ []
  C-eval ‶ f ‶ = khom f ∷ []

  D-eval ‶id‶ = []
  D-eval (f ‶∘‶ g) = do-dvcomp (D-eval f) (D-eval g)
  D-eval (‶L‶ f) = do-vlmap [] (C-eval f)
  D-eval (‶ε‶ x) = [] ∷r kcounit x
  D-eval ‶ f ‶ = [] ∷r khom f

  --------------------------------------------------------------------------------
  -- Soundness

  vrmap-sound
    : ∀ {x y z} (v1 : DValue y z) (v2 : CValue x (‶R‶ y))
    → ⟦ do-vrmap v1 v2 ⟧ ≡ R.₁ ⟦ v1 ⟧ C.∘ ⟦ v2 ⟧
  vrmap-sound [] v2 = C.introl R.F-id
  vrmap-sound (v1 ∷r k) v2 =
    ⟦ do-vrmap v1 (krmap k ∷ v2) ⟧      ≡⟨ vrmap-sound v1 (krmap k ∷ v2) ⟩
    R.₁ ⟦ v1 ⟧ C.∘ R.₁ ⟦ k ⟧ C.∘ ⟦ v2 ⟧ ≡⟨ C.pulll (sym (R.F-∘ _ _)) ⟩
    R.₁ (⟦ v1 ⟧ D.∘ ⟦ k ⟧) C.∘ ⟦ v2 ⟧   ∎

  vlmap-sound
    : ∀ {x y z} (v1 : DValue (‶L‶ y) z) (v2 : CValue x y)
    → ⟦ do-vlmap v1 v2 ⟧ ≡ ⟦ v1 ⟧ D.∘ L.₁ ⟦ v2 ⟧
  vlmap-sound v1 [] = D.intror L.F-id
  vlmap-sound v1 (k ∷ v2) =
    ⟦ do-vlmap (v1 ∷r klmap k) v2 ⟧       ≡⟨ vlmap-sound (v1 ∷r klmap k) v2 ⟩
    (⟦ v1 ⟧ D.∘ L.₁ ⟦ k ⟧) D.∘ L.₁ ⟦ v2 ⟧ ≡⟨ D.pullr (sym (L.F-∘ _ _)) ⟩
    ⟦ v1 ⟧ D.∘ L.₁ (⟦ k ⟧ C.∘ ⟦ v2 ⟧)     ∎

  cvconcat-sound
    : ∀ {x y z}
    → (v1 : CValue y z) (v2 : CValue x y)
    → ⟦ v1 ++c v2 ⟧ ≡ ⟦ v1 ⟧ C.∘ ⟦ v2 ⟧
  cvconcat-sound [] v2 = sym (C.idl _)
  cvconcat-sound (k ∷ v1) v2 = C.pushr (cvconcat-sound v1 v2)

  dvconcat-sound
    : ∀ {x y z}
    → (v1 : DValue y z) (v2 : DValue x y)
    → ⟦ v1 ++d v2 ⟧ ≡ ⟦ v1 ⟧ D.∘ ⟦ v2 ⟧
  dvconcat-sound v1 [] = sym (D.idr _)
  dvconcat-sound v1 (v2 ∷r k) = D.pushl (dvconcat-sound v1 v2)

  enact-claws-sound
    : ∀ {w x y z} (k1 : CFrame y z) (k2 : CFrame x y) (v : CValue w x)
    → ⟦ enact-claws k1 k2 v ⟧ ≡ ⟦ k1 ⟧ C.∘ ⟦ k2 ⟧ C.∘ ⟦ v ⟧
  enact-dlaws-sound
    : ∀ {w x y z} (v : DValue y z) (k1 : DFrame x y) (k2 : DFrame w x)
    → ⟦ enact-dlaws v k1 k2 ⟧ ≡ (⟦ v ⟧ D.∘ ⟦ k1 ⟧) D.∘ ⟦ k2 ⟧
  push-cframe-sound
    : ∀ {x y z} → (k : CFrame y z) (v : CValue x y)
    → ⟦ push-cframe k v ⟧ ≡ ⟦ k ⟧ C.∘ ⟦ v ⟧
  push-dframe-sound
    : ∀ {x y z} → (v : DValue y z) (k : DFrame x y)
    → ⟦ push-dframe v k ⟧ ≡ ⟦ v ⟧ D.∘ ⟦ k ⟧

  enact-claws-sound (khom f) k2 v = refl
  enact-claws-sound (krmap k1) (khom f) v = refl
  enact-claws-sound (krmap k1) (krmap k2) v =
    ⟦ do-vrmap (enact-dlaws [] k1 k2) [] ++c v ⟧      ≡⟨ cvconcat-sound (do-vrmap (enact-dlaws [] k1 k2) []) v ⟩
    ⟦ do-vrmap (enact-dlaws [] k1 k2) [] ⟧ C.∘ ⟦ v ⟧  ≡⟨ vrmap-sound (enact-dlaws [] k1 k2) [] C.⟩∘⟨refl ⟩
    (R.₁ ⟦ enact-dlaws [] k1 k2 ⟧ C.∘ C.id) C.∘ ⟦ v ⟧ ≡⟨ (C.idr _) C.⟩∘⟨refl ⟩
    R.₁ ⟦ enact-dlaws [] k1 k2 ⟧ C.∘ ⟦ v ⟧            ≡⟨ R.pushl (enact-dlaws-sound [] k1 k2) ⟩
    R.₁ ⌜ D.id D.∘ ⟦ k1 ⟧ ⌝ C.∘ R.₁ ⟦ k2 ⟧ C.∘ ⟦ v ⟧  ≡⟨ ap! (D.idl _) ⟩
    R.₁ ⟦ k1 ⟧ C.∘ R.₁ ⟦ k2 ⟧ C.∘ ⟦ v ⟧ ∎
  enact-claws-sound (krmap (khom f)) (kunit _) v = refl
  enact-claws-sound (krmap (klmap k1)) (kunit _) v =
    unit.η _ C.∘ ⟦ push-cframe k1 v ⟧       ≡⟨ C.refl⟩∘⟨ push-cframe-sound k1 v ⟩
    unit.η _ C.∘ ⟦ k1 ⟧ C.∘ ⟦ v ⟧           ≡⟨ C.extendl (unit.is-natural _ _ _) ⟩
    R.₁ (L.₁ ⟦ k1 ⟧) C.∘ unit.η _ C.∘ ⟦ v ⟧ ∎
  enact-claws-sound (krmap (kcounit _)) (kunit _) v =
    ⟦ v ⟧                                   ≡⟨ C.insertl zag ⟩
    R.₁ (counit.ε _) C.∘ unit.η _ C.∘ ⟦ v ⟧ ∎
  enact-claws-sound (kunit _) k2 v = refl

  enact-dlaws-sound v k1 (khom f) = refl
  enact-dlaws-sound v (khom f) (klmap k2) = refl
  enact-dlaws-sound v (klmap k1) (klmap k2) =
    ⟦ v ++d do-vlmap [] (enact-claws k1 k2 []) ⟧       ≡⟨ dvconcat-sound v (do-vlmap [] (enact-claws k1 k2 [])) ⟩
    ⟦ v ⟧ D.∘ ⟦ do-vlmap [] (enact-claws k1 k2 []) ⟧   ≡⟨ D.refl⟩∘⟨ vlmap-sound [] (enact-claws k1 k2 []) ⟩
    ⟦ v ⟧ D.∘ D.id D.∘ L.₁ ⟦ enact-claws k1 k2 [] ⟧    ≡⟨ D.refl⟩∘⟨ D.idl _ ⟩
    ⟦ v ⟧ D.∘ L.₁ ⟦ enact-claws k1 k2 [] ⟧             ≡⟨ L.pushr (enact-claws-sound k1 k2 []) ⟩
    (⟦ v ⟧ D.∘ L.₁ ⟦ k1 ⟧) D.∘ L.₁ ⌜ ⟦ k2 ⟧ C.∘ C.id ⌝ ≡⟨ ap! (C.idr _) ⟩
    (⟦ v ⟧ D.∘ L.₁ ⟦ k1 ⟧) D.∘ L.₁ ⟦ k2 ⟧ ∎
  enact-dlaws-sound v (kcounit _) (klmap (khom f)) = refl
  enact-dlaws-sound v (kcounit _) (klmap (krmap k2)) =
    ⟦ push-dframe v k2 ⟧ D.∘ counit.ε _         ≡⟨ push-dframe-sound v k2 D.⟩∘⟨refl ⟩
    (⟦ v ⟧ D.∘ ⟦ k2 ⟧) D.∘ counit.ε _           ≡⟨ D.extendr (sym (counit.is-natural _ _ _)) ⟩
    (⟦ v ⟧ D.∘ counit.ε _) D.∘ L.₁ (R.₁ ⟦ k2 ⟧) ∎
  enact-dlaws-sound v (kcounit _) (klmap (kunit _)) =
    ⟦ v ⟧                                       ≡⟨ D.insertr zig ⟩
    ((⟦ v ⟧ D.∘ counit.ε _) D.∘ L.₁ (unit.η _)) ∎
  enact-dlaws-sound v k1 (kcounit _) = refl

  push-cframe-sound k [] = refl
  push-cframe-sound k (k' ∷ v) = enact-claws-sound k k' v

  push-dframe-sound [] k = refl
  push-dframe-sound (v ∷r k') k = enact-dlaws-sound v k' k

  cvcomp-sound
    : ∀ {x y z} (v1 : CValue y z) (v2 : CValue x y)
    → ⟦ do-cvcomp v1 v2 ⟧ ≡ ⟦ v1 ⟧ C.∘ ⟦ v2 ⟧
  cvcomp-sound [] v2 = sym (C.idl _)
  cvcomp-sound (k ∷ v1) v2 =
    ⟦ push-cframe k (do-cvcomp v1 v2) ⟧ ≡⟨ push-cframe-sound k (do-cvcomp v1 v2) ⟩
    ⟦ k ⟧ C.∘ ⟦ do-cvcomp v1 v2 ⟧       ≡⟨ C.pushr (cvcomp-sound v1 v2) ⟩
    (⟦ k ⟧ C.∘ ⟦ v1 ⟧) C.∘ ⟦ v2 ⟧       ∎

  dvcomp-sound
    : ∀ {x y z} (v1 : DValue y z) (v2 : DValue x y)
    → ⟦ do-dvcomp v1 v2 ⟧ ≡ ⟦ v1 ⟧ D.∘ ⟦ v2 ⟧
  dvcomp-sound v1 [] = sym (D.idr _)
  dvcomp-sound v1 (v2 ∷r k) =
    ⟦ push-dframe (do-dvcomp v1 v2) k ⟧ ≡⟨ push-dframe-sound (do-dvcomp v1 v2) k ⟩
    (⟦ do-dvcomp v1 v2 ⟧ D.∘ ⟦ k ⟧)     ≡⟨ D.pushl (dvcomp-sound v1 v2) ⟩
    ⟦ v1 ⟧ D.∘ ⟦ v2 ⟧ D.∘ ⟦ k ⟧ ∎

  C-eval-sound : ∀ {x y} (e : CExpr x y) → ⟦ C-eval e ⟧ ≡ ⟦ e ⟧
  D-eval-sound : ∀ {x y} (e : DExpr x y) → ⟦ D-eval e ⟧ ≡ ⟦ e ⟧

  C-eval-sound ‶id‶ = refl
  C-eval-sound (e1 ‶∘‶ e2) =
    ⟦ do-cvcomp (C-eval e1) (C-eval e2) ⟧ ≡⟨ cvcomp-sound (C-eval e1) (C-eval e2) ⟩
    (⟦ C-eval e1 ⟧ C.∘ ⟦ C-eval e2 ⟧)     ≡⟨ ap₂ C._∘_ (C-eval-sound e1) (C-eval-sound e2) ⟩
    ⟦ e1 ⟧ C.∘ ⟦ e2 ⟧                     ∎
  C-eval-sound (‶R‶ e) =
    ⟦ do-vrmap (D-eval e) [] ⟧ ≡⟨ vrmap-sound (D-eval e) [] ⟩
    R.₁ ⟦ D-eval e ⟧ C.∘ C.id  ≡⟨ C.idr _ ⟩
    R.₁ ⟦ D-eval e ⟧           ≡⟨ ap R.₁ (D-eval-sound e) ⟩
    R.₁ ⟦ e ⟧                  ∎
  C-eval-sound (‶η‶ _) = C.idr _
  C-eval-sound ‶ x ‶ = C.idr _

  D-eval-sound ‶id‶ = refl
  D-eval-sound (e1 ‶∘‶ e2) =
    ⟦ do-dvcomp (D-eval e1) (D-eval e2) ⟧ ≡⟨ dvcomp-sound (D-eval e1) (D-eval e2) ⟩
    (⟦ D-eval e1 ⟧ D.∘ ⟦ D-eval e2 ⟧)     ≡⟨ ap₂ D._∘_ (D-eval-sound e1) (D-eval-sound e2) ⟩
    ⟦ e1 ⟧ D.∘ ⟦ e2 ⟧                     ∎
  D-eval-sound (‶L‶ e) =
    ⟦ do-vlmap [] (C-eval e) ⟧ ≡⟨ vlmap-sound [] (C-eval e) ⟩
    D.id D.∘ L.₁ ⟦ C-eval e ⟧  ≡⟨ D.idl _ ⟩
    L.₁ ⟦ C-eval e ⟧           ≡⟨ ap L.₁ (C-eval-sound e) ⟩
    L.₁ ⟦ e ⟧ ∎
  D-eval-sound (‶ε‶ _) = D.idl _
  D-eval-sound ‶ x ‶ = D.idl _

  abstract
    C-solve : ∀ {x y} (e1 e2 : CExpr x y) → ⟦ C-eval e1 ⟧ ≡ ⟦ C-eval e2 ⟧ → ⟦ e1 ⟧ ≡ ⟦ e2 ⟧
    C-solve e1 e2 p = sym (C-eval-sound e1) ·· p ·· C-eval-sound e2

    D-solve : ∀ {x y} (e1 e2 : DExpr x y) → ⟦ D-eval e1 ⟧ ≡ ⟦ D-eval e2 ⟧ → ⟦ e1 ⟧ ≡ ⟦ e2 ⟧
    D-solve e1 e2 p = sym (D-eval-sound e1) ·· p ·· D-eval-sound e2

module Reflection where

  pattern category-args cat args =
    _ hm∷ _ hm∷ cat v∷ args

  pattern functor-args functor args =
    _ hm∷ _ hm∷ _ hm∷ _ hm∷ _ hm∷ _ hm∷ functor v∷ args

  pattern nat-trans-args nt args =
    _ hm∷ _ hm∷ _ hm∷ _ hm∷
    _ hm∷ _ hm∷
    _ hm∷ _ hm∷
    nt v∷ args

  pattern adjoint-args adj args =
    _ hm∷ _ hm∷ _ hm∷ _ hm∷
    _ hm∷ _ hm∷
    _ hm∷ _ hm∷
    adj v∷ args
    
  pattern “id” C =
    def (quote Precategory.id) (category-args C (_ h∷ []))


  pattern “∘” C f g =
    def (quote Precategory._∘_) (category-args C (_ h∷ _ h∷ _ h∷ f v∷ g v∷ []))

  pattern “F₀” F x =
    def (quote Functor.F₀) (functor-args F (x v∷ []))

  pattern “F₁” F f =
    def (quote Functor.F₁) (functor-args F (_ h∷ _ h∷ f v∷ []))

  pattern “η” adj x =
    def (quote _=>_.η) (nat-trans-args (def (quote _⊣_.unit) (adjoint-args adj [])) (x v∷ []))

  pattern “ε” adj x =
    def (quote _=>_.η) (nat-trans-args (def (quote _⊣_.counit) (adjoint-args adj [])) (x v∷ []))

  pattern “Hom” C x y =
    def (quote Precategory.Hom) (category-args C (x v∷ y v∷ []))

  mk-nbe-args : Term → List (Arg Term) → List (Arg Term)
  mk-nbe-args adj args =
    unknown h∷ unknown h∷ unknown h∷ unknown h∷
    unknown h∷ unknown h∷
    unknown h∷ unknown h∷
    adj v∷ args

  unapply-hom : Term → TC (Maybe (Term × Term × Term))
  unapply-hom red@(“Hom” C x y) = do
    pure (just (C , x , y))
  unapply-hom tm = reduce tm >>= λ where
    tm@(meta _ _) → do
      C ← new-meta (def (quote Precategory) (unknown v∷ unknown v∷ []))
      x ← new-meta (def (quote Precategory.Ob) (infer-hidden 2 (C v∷ [])))
      y ← new-meta (def (quote Precategory.Ob) (infer-hidden 2 (C v∷ [])))
      unify tm (def (quote Precategory.Hom) (infer-hidden 2 (C v∷ x v∷ y v∷ [])))
      traverse wait-for-type (x ∷ y ∷ [])
      pure (just (C , x , y))
    tm@(“Hom” C x y) →
      pure (just (C , x , y))
    _ → returnTC nothing

  get-hom-boundary : Term → TC (Term × Term)
  get-hom-boundary tm = unapply-hom tm >>= λ where
    (just (_ , src , tgt)) → pure (src , tgt)
    nothing → typeError "Couldn't get hom boundary."

  “C-solve” : Term → Term → Term → Term
  “C-solve” adj lhs rhs =
    def (quote NbE.C-solve) (mk-nbe-args adj $ infer-hidden 2 (lhs v∷ rhs v∷ “refl” v∷ []))

  “D-solve” : Term → Term → Term → Term
  “D-solve” adj lhs rhs =
    def (quote NbE.D-solve) (mk-nbe-args adj $ infer-hidden 2 (lhs v∷ rhs v∷ “refl” v∷ []))

  record Adj-terms : Type where
    field
      C : Term
      D : Term
      L : Term
      R : Term
      adjoint : Term

  open Adj-terms

  build-C-obj-expr : Adj-terms → Term → TC Term
  build-D-obj-expr : Adj-terms → Term → TC Term

  build-C-obj-expr tms t@(“F₀” F x) =
    catchTC
      (do unify (tms .R) F
          x ← build-D-obj-expr tms x
          returnTC $ con (quote NbE.‶C‶.‶R‶) (x v∷ []))
      (returnTC $ con (quote NbE.‶C‶.‶_‶) (t v∷ []))
  build-C-obj-expr tms x =
    returnTC $ con (quote NbE.‶C‶.‶_‶) (x v∷ [])

  build-D-obj-expr tms t@(“F₀” F x) =
    catchTC
      (do unify (tms .L) F
          x ← build-C-obj-expr tms x
          returnTC $ con (quote NbE.‶D‶.‶L‶) (x v∷ []))
      (returnTC $ con (quote NbE.‶D‶.‶_‶) (t v∷ []))
  build-D-obj-expr tms x = do
    returnTC $ con (quote NbE.‶D‶.‶_‶) (x v∷ [])

  {-# TERMINATING #-}
  build-C-expr : Adj-terms → Term → TC Term
  build-D-expr : Adj-terms → Term → TC Term

  build-C-expr tms (“id” cat) =
    returnTC $ con (quote NbE.CExpr.‶id‶) []
  build-C-expr tms (“∘” cat f g) = do
    f ← build-C-expr tms f
    g ← build-C-expr tms g
    returnTC $ con (quote NbE.CExpr._‶∘‶_) (f v∷ g v∷ [])
  build-C-expr tms t@(“F₁” F f) =
    catchTC
      (do unify (tms .R) F
          f ← build-D-expr tms f
          returnTC $ con (quote NbE.CExpr.‶R‶) (f v∷ []))
      (returnTC $ con (quote NbE.CExpr.‶_‶) (t v∷ []))
  build-C-expr tms t@(“η” adj x) =
    catchTC
      (do unify (tms .adjoint) adj
          x ← build-C-obj-expr tms x
          returnTC $ con (quote NbE.CExpr.‶η‶) (x v∷ []))
      (returnTC $ con (quote NbE.CExpr.‶_‶) (t v∷ []))
  build-C-expr tms f = do
    x , y ← get-hom-boundary =<< inferType f
    x ← build-C-obj-expr tms =<< normalise x
    y ← build-C-obj-expr tms =<< normalise y
    returnTC $ con (quote NbE.CExpr.‶_‶) (infer-hidden 9 $ (x h∷ y h∷ f v∷ []))

  build-D-expr tms (“id” cat) =
    returnTC $ con (quote NbE.DExpr.‶id‶) []
  build-D-expr tms (“∘” cat f g) = do
    f ← build-D-expr tms f
    g ← build-D-expr tms g
    returnTC $ con (quote NbE.DExpr._‶∘‶_) (f v∷ g v∷ [])
  build-D-expr tms t@(“F₁” F f) =
    catchTC
      (do unify (tms .L) F
          f ← build-C-expr tms f
          returnTC $ con (quote NbE.DExpr.‶L‶) (f v∷ []))
      (returnTC $ con (quote NbE.DExpr.‶_‶) (t v∷ []))
  build-D-expr tms t@(“ε” adj x) =
    catchTC
      (do unify (tms .adjoint) adj
          x ← build-D-obj-expr tms x
          returnTC $ con (quote NbE.DExpr.‶ε‶) (x v∷ []))
      (returnTC $ con (quote NbE.DExpr.‶_‶) (t v∷ []))
  build-D-expr tms f = do
    x , y ← get-hom-boundary =<< inferType f
    x ← build-D-obj-expr tms =<< normalise x
    y ← build-D-obj-expr tms =<< normalise y
    returnTC $ con (quote NbE.DExpr.‶_‶) (infer-hidden 9 $ (x h∷ y h∷ f v∷ []))

  -- We are conservative when blocking reduction, and unfold on-demand
  -- in the expression builder.
  dont-reduce : List Name
  dont-reduce =
    quote Precategory.id ∷ quote Precategory._∘_ ∷
    quote Functor.F₀ ∷ quote Functor.F₁ ∷
    quote _=>_.η ∷
    quote _⊣_.unit ∷ quote _⊣_.counit ∷ []

  solve-left-macro
    : ∀ {oc ℓc od ℓd} {C : Precategory oc ℓc} {D : Precategory od ℓd}
    → {L : Functor C D} {R : Functor D C}
    → L ⊣ R
    → Term → TC ⊤
  solve-left-macro {C = C} {D = D} {L = L} {R = R} adj hole =
    withNormalisation false $
    withReduceDefs (false , dont-reduce) $ do
    C-tm ← quoteTC C
    D-tm ← quoteTC D
    L-tm ← quoteTC L
    R-tm ← quoteTC R
    adj-tm ← quoteTC adj
    goal ← inferType hole >>= reduce
    just (lhs , rhs) ← get-boundary goal
      where nothing → typeError $ strErr "Can't determine boundary: " ∷
                                  termErr goal ∷ []
    let tms = record { C = C-tm ; D = D-tm ; L = L-tm ; R = R-tm ; adjoint = adj-tm }
    elhs ← build-D-expr tms =<< normalise lhs
    erhs ← build-D-expr tms =<< normalise rhs
    noConstraints $ unify hole (“D-solve” adj-tm elhs erhs)

  solve-right-macro
    : ∀ {oc ℓc od ℓd} {C : Precategory oc ℓc} {D : Precategory od ℓd}
    → {L : Functor C D} {R : Functor D C}
    → L ⊣ R
    → Term → TC ⊤
  solve-right-macro {C = C} {D = D} {L = L} {R = R} adj hole =
    withNormalisation false $
    withReduceDefs (false , dont-reduce) $ do
    C-tm ← quoteTC C
    D-tm ← quoteTC D
    L-tm ← quoteTC L
    R-tm ← quoteTC R
    adj-tm ← quoteTC adj
    goal ← inferType hole >>= reduce
    just (lhs , rhs) ← get-boundary goal
      where nothing → typeError $ strErr "Can't determine boundary: " ∷
                                  termErr goal ∷ []
    let tms = record { C = C-tm ; D = D-tm ; L = L-tm ; R = R-tm ; adjoint = adj-tm }
    elhs ← build-C-expr tms =<< normalise lhs
    erhs ← build-C-expr tms =<< normalise rhs
    noConstraints $ unify hole (“C-solve” adj-tm elhs erhs)

macro
  left-adjoint!
    : ∀ {oc ℓc od ℓd} {C : Precategory oc ℓc} {D : Precategory od ℓd}
    → {L : Functor C D} {R : Functor D C}
    → L ⊣ R
    → Term → TC ⊤
  left-adjoint! = Reflection.solve-left-macro

  right-adjoint!
    : ∀ {oc ℓc od ℓd} {C : Precategory oc ℓc} {D : Precategory od ℓd}
    → {L : Functor C D} {R : Functor D C}
    → L ⊣ R
    → Term → TC ⊤
  right-adjoint! = Reflection.solve-right-macro

private
  module _
    {oc ℓc od ℓd} {C : Precategory oc ℓc} {D : Precategory od ℓd}
    {L : Functor C D} {R : Functor D C}
    (adj : L ⊣ R) where
    module C = Precategory C
    module D = Precategory D
    module L = Functor L
    module R = Functor R
    open _⊣_ adj

    manual-test : ∀ {x y} → (f : C.Hom x (R.₀ y)) → L-adjunct adj (R-adjunct adj f) ≡ f
    manual-test {x} {y} f = C-solve adj (‶R‶ (‶ε‶ ‶ y ‶ ‶∘‶ ‶L‶ ‶ f ‶) ‶∘‶ ‶η‶ ‶ x ‶) ‶ f ‶ refl
      where open NbE

    manual-test' : ∀ {x y} → (f : D.Hom (L.₀ x) y) → R-adjunct adj (L-adjunct adj f) ≡ f
    manual-test' {x} {y} f = D-solve adj (‶ε‶ ‶ y ‶ ‶∘‶ ‶L‶ (‶R‶ ‶ f ‶ ‶∘‶ ‶η‶ ‶ x ‶)) ‶ f ‶ refl
      where open NbE

    reflection-test : ∀ {x y} → (f : C.Hom x (R.₀ y)) → L-adjunct adj (R-adjunct adj f) ≡ f
    reflection-test f = right-adjoint! adj

    reflection-test' : ∀ {x y} → (f : D.Hom (L.₀ x) y) → R-adjunct adj (L-adjunct adj f) ≡ f
    reflection-test' f = left-adjoint! adj

    R-adjunct-natural₂'
      : ∀ {a b c d} (f : D.Hom a b) (g : C.Hom c d) (x : C.Hom d (R.F₀ a))
      → R-adjunct adj (R.₁ f C.∘ x C.∘ g) ≡ f D.∘ R-adjunct adj x D.∘ L.₁ g
    R-adjunct-natural₂' _ _ _ = left-adjoint! adj
