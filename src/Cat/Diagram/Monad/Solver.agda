module Cat.Diagram.Monad.Solver where

open import 1Lab.Prelude hiding (id; _∘_; refl⟩∘⟨_; _⟩∘⟨refl)
open import 1Lab.Reflection hiding (_++_)

open import Cat.Base
open import Cat.Diagram.Monad

import Cat.Functor.Reasoning as FR
import Cat.Reasoning as CR

open import Data.List hiding (_++_)

module NbE {o h} {𝒞 : Precategory o h} (M : Monad 𝒞) where
  open CR 𝒞
  module M = FR (Monad.M M)
  open Monad M

  --------------------------------------------------------------------------------
  -- NOTE: Object Expressions
  -- We can't index everything by 'Ob', as Agda will (rightfully) assume that M₀ is not injective,
  -- which then inhibits on our ability to pattern match on things.
  -- Therefore, we introduce a reflected type of object expressions,
  -- which solves the injectivity issue.

  data ‶Ob‶ : Type o where
    ‶_‶   : Ob → ‶Ob‶
    ‶M₀‶ : ‶Ob‶ → ‶Ob‶

  ⟦_⟧ₒ : ‶Ob‶ → Ob
  ⟦ ‶ X ‶ ⟧ₒ = X
  ⟦ ‶M₀‶ X ⟧ₒ = M₀ ⟦ X ⟧ₒ

  private variable
    W X Y Z : ‶Ob‶

  data ‶Hom‶ : ‶Ob‶ → ‶Ob‶ → Type (o ⊔ h) where
    ‶M₁‶  : ‶Hom‶ X Y → ‶Hom‶ (‶M₀‶ X) (‶M₀‶ Y)
    ‶η‶   : (X : ‶Ob‶) → ‶Hom‶ X (‶M₀‶ X)
    ‶μ‶   : (X : ‶Ob‶) → ‶Hom‶ (‶M₀‶ (‶M₀‶ X)) (‶M₀‶ X)
    _‶∘‶_ : ‶Hom‶ Y Z → ‶Hom‶ X Y → ‶Hom‶ X Z
    ‶id‶  : ‶Hom‶ X X
    _↑    : ∀ {X Y} → Hom X Y → ‶Hom‶ ‶ X ‶ ‶ Y ‶

  ⟦_⟧ₕ : ‶Hom‶ X Y → Hom ⟦ X ⟧ₒ ⟦ Y ⟧ₒ
  ⟦ ‶M₁‶ f ⟧ₕ = M₁ ⟦ f ⟧ₕ
  ⟦ ‶η‶ X ⟧ₕ = unit.η ⟦ X ⟧ₒ
  ⟦ ‶μ‶ X ⟧ₕ = mult.η ⟦ X ⟧ₒ
  ⟦ e1 ‶∘‶ e2 ⟧ₕ = ⟦ e1 ⟧ₕ ∘ ⟦ e2 ⟧ₕ
  ⟦ ‶id‶ ⟧ₕ = id
  ⟦ f ↑ ⟧ₕ = f

  --------------------------------------------------------------------------------
  -- Values

  data Frame : ‶Ob‶ → ‶Ob‶ → Type (o ⊔ h) where
    khom  : ∀ {X Y} → Hom X Y → Frame ‶ X ‶ ‶ Y ‶
    kmap  : Frame X Y → Frame (‶M₀‶ X) (‶M₀‶ Y)
    kunit : (X : ‶Ob‶) → Frame X (‶M₀‶ X)
    kmult : (X : ‶Ob‶) → Frame (‶M₀‶ (‶M₀‶ X)) (‶M₀‶ X)

  data Value : ‶Ob‶ → ‶Ob‶ → Type (o ⊔ h) where
    [] : Value X X
    _∷_ : Frame Y Z → Value X Y → Value X Z

  infixr 20 _∷_

  ⟦_⟧ₖ : Frame X Y → Hom ⟦ X ⟧ₒ ⟦ Y ⟧ₒ
  ⟦ khom f ⟧ₖ = f
  ⟦ kmap k ⟧ₖ = M₁ ⟦ k ⟧ₖ
  ⟦ kunit X ⟧ₖ = unit.η ⟦ X ⟧ₒ
  ⟦ kmult X ⟧ₖ = mult.η ⟦ X ⟧ₒ

  ⟦_⟧ᵥ : Value X Y → Hom ⟦ X ⟧ₒ ⟦ Y ⟧ₒ
  ⟦ [] ⟧ᵥ = id
  ⟦ k ∷ v ⟧ᵥ = ⟦ k ⟧ₖ ∘ ⟦ v ⟧ᵥ

  --------------------------------------------------------------------------------
  -- Evaluation
  --
  -- The evaluation strategy here is a bit subtle. The naive option
  -- is to push the 'kunit' frames all the way to the bottom of the stack,
  -- but this makes enacting the 'μ ∘ η' equations inneficient, as that
  -- means we will also have to push the 'kmult' frames all the way to the bottom
  -- as well.
  --
  -- Instead, what we do is push the 'kmap' frames past all of the 'kunit' and 'kmult'
  -- frames, which ensures that all of the 'kunit' and 'kmult' frames remain on the top
  -- of the stack. This makes it easier to enact the equations in question, as
  -- we don't have to dig nearly as far.

  -- Concatenate 2 values together, performing no simplification.
  _++_ : Value Y Z → Value X Y → Value X Z
  [] ++ v2 = v2
  (k ∷ v1) ++ v2 = k ∷ (v1 ++ v2)

  -- Apply M₁ to a value.
  do-vmap : Value X Y → Value (‶M₀‶ X) (‶M₀‶ Y)
  do-vmap [] = []
  do-vmap (f ∷ v) = kmap f ∷ do-vmap v

  enact-laws : Frame Y Z → Frame X Y → Value W X → Value W Z
  push-frm : Frame Y Z → Value X Y → Value X Z

  -- The meat of the solver! This is responsible for enacting the
  -- monad equations (hence the name).
  -- There are 2 important phases to this function: 'kunit' and 'kmult'
  -- floating, and the subsequent elimination of those frames.
  --
  -- When we push a 'kmap' frame, we check to see if the head of the stack
  -- is a 'kunit' or 'kmult'; if so, we float those outwards so that they
  -- always remain at the top of the stack.
  --
  -- Subsequently, when pushing a 'kmult' frame, we need to enact
  -- equations. As the relevant frames are /always/ on the top of the stack,
  -- we can simply apply the relevant equations, and potentially keep pushing
  -- frames down.
  enact-laws (khom f) k' v = khom f ∷ k' ∷ v
  enact-laws (kmap k) (kmap k') v = do-vmap (enact-laws k k' []) ++ v
  enact-laws (kmap k) (kunit _) v = kunit _ ∷ push-frm k v
  enact-laws (kmap k) (kmult _) v = kmult _ ∷ push-frm (kmap (kmap k)) v
  enact-laws (kunit _) k' v = kunit _ ∷ k' ∷ v
  enact-laws (kmult _) (kmap (kmap k')) v = kmult _ ∷ kmap (kmap k') ∷ v
  enact-laws (kmult _) (kmap (kunit _)) v = v
  enact-laws (kmult _) (kmap (kmult _)) v = kmult _ ∷ push-frm (kmult _) v
  enact-laws (kmult _) (kunit _) v = v
  enact-laws (kmult _) (kmult _) v = kmult _ ∷ kmult _ ∷ v

  -- Small shim, used to enact a law against a potentially empty stack.
  push-frm k [] = k ∷ []
  push-frm k (k' ∷ v) = enact-laws k k' v

  -- Concatenate 2 stacks together, performing simplification via 'enact-laws'.
  do-vcomp : Value Y Z → Value X Y → Value X Z
  do-vcomp [] v2 = v2
  do-vcomp (k ∷ v1) v2 = push-frm k (do-vcomp v1 v2)

  eval : ‶Hom‶ X Y → Value X Y
  eval (‶M₁‶ e) = do-vmap (eval e)
  eval (‶η‶ X) = kunit X ∷ []
  eval (‶μ‶ X) = kmult X ∷ []
  eval (e1 ‶∘‶ e2) = do-vcomp (eval e1) (eval e2)
  eval ‶id‶ = []
  eval (f ↑) = khom f ∷ []

  --------------------------------------------------------------------------------
  -- Soundness

  vmap-sound : ∀ (v : Value X Y) → ⟦ do-vmap v ⟧ᵥ ≡ M₁ ⟦ v ⟧ᵥ
  vmap-sound [] = sym M-id
  vmap-sound (k ∷ v) =
    M₁ ⟦ k ⟧ₖ ∘ ⟦ do-vmap v ⟧ᵥ ≡⟨ refl⟩∘⟨ vmap-sound v ⟩
    M₁ ⟦ k ⟧ₖ M.𝒟.∘ M₁ ⟦ v ⟧ᵥ  ≡˘⟨ M-∘ ⟦ k ⟧ₖ ⟦ v ⟧ᵥ ⟩
    M₁ (⟦ k ⟧ₖ ∘ ⟦ v ⟧ᵥ) ∎

  vconcat-sound : ∀ (v1 : Value Y Z) → (v2 : Value X Y) → ⟦ v1 ++ v2 ⟧ᵥ ≡ ⟦ v1 ⟧ᵥ ∘ ⟦ v2 ⟧ᵥ
  vconcat-sound [] v2 = sym (idl ⟦ v2 ⟧ᵥ)
  vconcat-sound (k ∷ v1) v2 = pushr (vconcat-sound v1 v2)

  enact-laws-sound : ∀ (k1 : Frame Y Z) → (k2 : Frame X Y) → (v : Value W X) → ⟦ enact-laws k1 k2 v ⟧ᵥ ≡ ⟦ k1 ⟧ₖ ∘ ⟦ k2 ⟧ₖ ∘ ⟦ v ⟧ᵥ
  push-frm-sound   : ∀ (k : Frame Y Z) → (v : Value X Y) → ⟦ push-frm k v ⟧ᵥ ≡ ⟦ k ⟧ₖ ∘ ⟦ v ⟧ᵥ

  enact-laws-sound (khom x) k2 v = refl
  enact-laws-sound (kmap k1) (kmap k2) v =
    ⟦ do-vmap (enact-laws k1 k2 []) ++ v ⟧ᵥ     ≡⟨ vconcat-sound (do-vmap (enact-laws k1 k2 [])) v ⟩
    ⟦ do-vmap (enact-laws k1 k2 []) ⟧ᵥ ∘ ⟦ v ⟧ᵥ ≡⟨ vmap-sound (enact-laws k1 k2 []) ⟩∘⟨refl ⟩
    M₁ ⟦ enact-laws k1 k2 [] ⟧ᵥ M.𝒟.∘ ⟦ v ⟧ᵥ    ≡⟨ M.pushl (enact-laws-sound k1 k2 []) ⟩
    M₁ ⟦ k1 ⟧ₖ ∘ M₁ (⟦ k2 ⟧ₖ ∘ id) ∘ ⟦ v ⟧ᵥ     ≡⟨ refl⟩∘⟨ (M.⟨ idr ⟦ k2 ⟧ₖ ⟩ ⟩∘⟨refl) ⟩
    M₁ ⟦ k1 ⟧ₖ ∘ M₁ ⟦ k2 ⟧ₖ ∘ ⟦ v ⟧ᵥ            ∎
  enact-laws-sound (kmap {Y = Y} k1) (kunit X) v =
    unit.η ⟦ Y ⟧ₒ ∘ ⟦ push-frm k1 v ⟧ᵥ    ≡⟨ refl⟩∘⟨ push-frm-sound k1 v ⟩
    unit.η ⟦ Y ⟧ₒ ∘ ⟦ k1 ⟧ₖ ∘ ⟦ v ⟧ᵥ      ≡⟨ extendl (unit.is-natural ⟦ X ⟧ₒ ⟦ Y ⟧ₒ ⟦ k1 ⟧ₖ) ⟩
    M.F₁ ⟦ k1 ⟧ₖ ∘ unit.η ⟦ X ⟧ₒ ∘ ⟦ v ⟧ᵥ ∎
  enact-laws-sound (kmap {Y = Y} k1) (kmult X) v =
    mult.η ⟦ Y ⟧ₒ ∘ ⟦ push-frm (kmap (kmap k1)) v ⟧ᵥ ≡⟨ refl⟩∘⟨ push-frm-sound (kmap (kmap k1)) v ⟩
    mult.η ⟦ Y ⟧ₒ ∘ M₁ (M₁ ⟦ k1 ⟧ₖ) ∘ ⟦ v ⟧ᵥ         ≡⟨ extendl (mult.is-natural ⟦ X ⟧ₒ ⟦ Y ⟧ₒ ⟦ k1 ⟧ₖ) ⟩
    M.F₁ ⟦ k1 ⟧ₖ ∘ mult.η ⟦ X ⟧ₒ ∘ ⟦ v ⟧ᵥ            ∎
  enact-laws-sound (kunit X) k2 v = refl
  enact-laws-sound (kmult X) (kmap (kmap k2)) v = refl
  enact-laws-sound (kmult X) (kmap (kunit .X)) v = insertl left-ident
  enact-laws-sound (kmult X) (kmap (kmult .X)) v =
    mult.η ⟦ X ⟧ₒ ∘ ⟦ push-frm (kmult (‶M₀‶ X)) v ⟧ᵥ ≡⟨ refl⟩∘⟨ push-frm-sound (kmult (‶M₀‶ X)) v ⟩
    mult.η ⟦ X ⟧ₒ ∘ mult.η (M₀ ⟦ X ⟧ₒ) ∘ ⟦ v ⟧ᵥ      ≡⟨ extendl (sym mult-assoc) ⟩
    mult.η ⟦ X ⟧ₒ ∘ M₁ (mult.η ⟦ X ⟧ₒ) ∘ ⟦ v ⟧ᵥ ∎
  enact-laws-sound (kmult X) (kunit _) v = insertl right-ident
  enact-laws-sound (kmult X) (kmult _) v = refl

  push-frm-sound k [] = refl
  push-frm-sound k (k' ∷ v) = enact-laws-sound k k' v

  vcomp-sound : ∀ (v1 : Value Y Z) → (v2 : Value X Y) → ⟦ do-vcomp v1 v2 ⟧ᵥ ≡ ⟦ v1 ⟧ᵥ ∘ ⟦ v2 ⟧ᵥ
  vcomp-sound [] v2 = sym (idl ⟦ v2 ⟧ᵥ)
  vcomp-sound (k ∷ v1) v2 =
    ⟦ push-frm k (do-vcomp v1 v2) ⟧ᵥ ≡⟨ push-frm-sound k (do-vcomp v1 v2) ⟩
    ⟦ k ⟧ₖ ∘ ⟦ do-vcomp v1 v2 ⟧ᵥ ≡⟨ pushr (vcomp-sound v1 v2) ⟩
    (⟦ k ⟧ₖ ∘ ⟦ v1 ⟧ᵥ) ∘ ⟦ v2 ⟧ᵥ ∎

  eval-sound : ∀ (e : ‶Hom‶ X Y) → ⟦ eval e ⟧ᵥ ≡ ⟦ e ⟧ₕ
  eval-sound (‶M₁‶ e) =
    ⟦ do-vmap (eval e) ⟧ᵥ ≡⟨ vmap-sound (eval e) ⟩
    M₁ ⟦ eval e ⟧ᵥ        ≡⟨ M.⟨ eval-sound e ⟩ ⟩
    M₁ ⟦ e ⟧ₕ ∎
  eval-sound (‶η‶ X) = idr (unit.η ⟦ X ⟧ₒ)
  eval-sound (‶μ‶ X) = idr (mult.η ⟦ X ⟧ₒ)
  eval-sound (e1 ‶∘‶ e2) =
    ⟦ do-vcomp (eval e1) (eval e2) ⟧ᵥ ≡⟨ vcomp-sound (eval e1) (eval e2) ⟩
    ⟦ eval e1 ⟧ᵥ ∘ ⟦ eval e2 ⟧ᵥ       ≡⟨ ap₂ _∘_ (eval-sound e1) (eval-sound e2) ⟩
    ⟦ e1 ⟧ₕ ∘ ⟦ e2 ⟧ₕ                 ∎
  eval-sound ‶id‶ = refl
  eval-sound (f ↑) = idr f

  abstract
    solve : ∀ (e1 e2 : ‶Hom‶ X Y) → ⟦ eval e1 ⟧ᵥ ≡ ⟦ eval e2 ⟧ᵥ → ⟦ e1 ⟧ₕ ≡ ⟦ e2 ⟧ₕ
    solve e1 e2 p = sym (eval-sound e1) ·· p ·· (eval-sound e2)

module Reflection where

  pattern category-args xs =
    _ hm∷ _ hm∷ _ v∷ xs

  pattern functor-args functor xs =
    _ hm∷ _ hm∷ _ hm∷ _ hm∷ _ hm∷ _ hm∷ functor v∷ xs

  pattern nat-trans-args nt args =
    _ hm∷ _ hm∷ _ hm∷ _ hm∷
    _ hm∷ _ hm∷
    _ hm∷ _ hm∷
    nt v∷ args


  pattern monad-args monad xs =
    _ hm∷ _ hm∷ _ hm∷ monad v∷ xs

  pattern monad-fn-args monad xs =
    _ h∷ _ h∷ _ h∷ monad v∷ xs

  pattern “id” =
    def (quote Precategory.id) (category-args (_ h∷ []))

  pattern “∘” f g =
    def (quote Precategory._∘_) (category-args (_ h∷ _ h∷ _ h∷ f v∷ g v∷ []))

  pattern “M₀” monad x =
    def (quote Monad.M₀) (monad-fn-args monad (x v∷ []))

  pattern “M₁” monad f =
    def (quote Monad.M₁) (monad-fn-args monad (_ h∷ _ h∷ f v∷ []))

  pattern “η” monad x =
    def (quote _=>_.η) (nat-trans-args (def (quote Monad.unit) (monad-args monad [])) (x v∷ []))

  pattern “μ” monad x =
    def (quote _=>_.η) (nat-trans-args (def (quote Monad.mult) (monad-args monad [])) (x v∷ []))

  mk-monad-args : Term → List (Arg Term) → List (Arg Term)
  mk-monad-args monad args = unknown h∷ unknown h∷ unknown h∷ monad v∷ args

  “solve” : Term → Term → Term → Term
  “solve” monad lhs rhs =
    def (quote NbE.solve) (mk-monad-args monad $ infer-hidden 2 $ lhs v∷ rhs v∷ def (quote refl) [] v∷ [])

  build-object-expr : Term → Term → TC Term
  build-object-expr monad (“M₀” monad' x) = do
    unify monad monad'
    x ← build-object-expr monad x
    pure $ con (quote NbE.‶M₀‶) (x v∷ [])
  build-object-expr monad x =
    pure $ con (quote NbE.‶_‶) (x v∷ [])

  build-hom-expr : Term → Term → TC Term
  build-hom-expr monad “id” =
    pure $ con (quote NbE.‶id‶) []
  build-hom-expr monad (“∘” f g) = do
    f ← build-hom-expr monad f
    g ← build-hom-expr monad g
    pure $ con (quote NbE._‶∘‶_) (f v∷ g v∷ [])
  build-hom-expr monad (“M₁” monad' f) = do
    unify monad monad'
    f ← build-hom-expr monad f
    pure $ con (quote NbE.‶M₁‶) (f v∷ [])
  build-hom-expr monad (“η” monad' x) = do
    unify monad monad'
    x ← build-object-expr monad x
    pure $ con (quote NbE.‶η‶) (x v∷ [])
  build-hom-expr monad (“μ” monad' x) = do
    x ← build-object-expr monad x
    unify monad monad'
    pure $ con (quote NbE.‶μ‶) (x v∷ [])
  build-hom-expr monad f =
    pure $ con (quote NbE._↑) (f v∷ [])

  dont-reduce : List Name
  dont-reduce =
    quote Precategory.id ∷ quote Precategory._∘_ ∷
    quote Functor.F₀ ∷ quote Functor.F₁ ∷
    quote _=>_.η ∷
    quote Monad.M ∷ quote Monad.unit ∷ quote Monad.mult ∷ []

  solve-macro : ∀ {o h} {𝒞 : Precategory o h} → Monad 𝒞 → Term → TC ⊤
  solve-macro monad hole =
    withNormalisation false $
    withReduceDefs (false , dont-reduce) $ do
      monad-tm ← quoteTC monad
      goal ← infer-type hole >>= reduce
      just (lhs , rhs) ← get-boundary goal
        where nothing → typeError $ strErr "Can't determine boundary: " ∷
                                    termErr goal ∷ []
      elhs ← build-hom-expr monad-tm lhs
      erhs ← build-hom-expr monad-tm rhs
      noConstraints $ unify hole (“solve” monad-tm elhs erhs)

macro
  monad! : ∀ {o h} {𝒞 : Precategory o h} → Monad 𝒞 → Term → TC ⊤
  monad! monad = Reflection.solve-macro monad

private module Test {o h} {𝒞 : Precategory o h} (monad : Monad 𝒞) where
  open Precategory 𝒞
  open Monad monad

  variable
    A B C : Ob

  test : ∀ {f : Hom B C} {g : Hom A B}
         → mult.η C ∘ M₁ (M₁ (f ∘ g)) ∘ unit.η (M₀ A) ≡ M₁ f ∘ M₁ (id ∘ g)
  test = monad! monad

  test-assoc : ∀ X → mult.η X ∘ M₁ (mult.η X) ≡ mult.η X ∘ mult.η (M₀ X)
  test-assoc X = monad! monad

  test-nested : ∀ X → M₁ (mult.η X ∘ unit.η (M₀ X)) ≡ id
  test-nested _ = monad! monad

  test-separate : ∀ X → M₁ (mult.η X) ∘ M₁ (unit.η (M₀ X)) ≡ id
  test-separate _ = monad! monad
