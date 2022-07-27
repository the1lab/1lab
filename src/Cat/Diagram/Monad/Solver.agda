module Cat.Diagram.Monad.Solver where

open import 1Lab.Prelude hiding (id; _∘_)
open import 1Lab.Reflection

open import Cat.Base
open import Cat.Diagram.Monad

import Cat.Functor.Reasoning as FR
import Cat.Reasoning as CR

module NbE {o h} {𝒞 : Precategory o h} (M : Monad 𝒞) where
  open CR 𝒞
  module M = FR (Monad.M M)
  open Monad M

  --------------------------------------------------------------------------------
  -- NOTE: Object Expressions
  -- We can′t index everyting by 'Ob', as Agda will (rightfully) assume that M₀ is not injective,
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
    X Y Z : ‶Ob‶

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
    vid : Value X X
    vcomp : Frame Y Z → Value X Y → Value X Z

  ⟦_⟧ₖ : Frame X Y → Hom ⟦ X ⟧ₒ ⟦ Y ⟧ₒ
  ⟦ khom f ⟧ₖ = f
  ⟦ kmap k ⟧ₖ = M₁ ⟦ k ⟧ₖ
  ⟦ kunit X ⟧ₖ = unit.η ⟦ X ⟧ₒ
  ⟦ kmult X ⟧ₖ = mult.η ⟦ X ⟧ₒ

  ⟦_⟧ᵥ : Value X Y → Hom ⟦ X ⟧ₒ ⟦ Y ⟧ₒ
  ⟦ vid ⟧ᵥ = id
  ⟦ vcomp k v ⟧ᵥ = ⟦ k ⟧ₖ ∘ ⟦ v ⟧ᵥ

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

  do-vmap : Value X Y → Value (‶M₀‶ X) (‶M₀‶ Y)
  do-vmap vid = vid
  do-vmap (vcomp f v) = vcomp (kmap f) (do-vmap v)

  push-unit : Value X Y → Value X (‶M₀‶ Y)
  push-unit vid = vcomp (kunit _) vid
  push-unit (vcomp k v) = vcomp (kmap k) (push-unit v)

  push-kmap : Frame Y Z → Value X (‶M₀‶ Y) → Value X (‶M₀‶ Z)
  push-kmult : Value X (‶M₀‶ (‶M₀‶ Y)) → Value X (‶M₀‶ Y)
  push-frm : Frame Y Z → Value X Y → Value X Z

  push-kmap k vid = vcomp (kmap k) vid
  push-kmap k (vcomp (kmap k') v) = vcomp (kmap k) (vcomp (kmap k') v)
  push-kmap k (vcomp (kunit _) v) = vcomp (kunit _) (push-frm k v)
  push-kmap k (vcomp (kmult _) v) = vcomp (kmult _) (push-kmap (kmap k) v)

  push-kmult vid = vcomp (kmult _) vid
  push-kmult (vcomp (kmap (kmap k)) v) = vcomp (kmult _) (vcomp (kmap (kmap k)) v)
  push-kmult (vcomp (kmap (kunit _)) v) = v
  push-kmult (vcomp (kmap (kmult _)) v) = vcomp (kmult _) (vcomp (kmult _) v)
  push-kmult (vcomp (kunit _) v) = v
  push-kmult (vcomp (kmult _) v) = vcomp (kmult _) (vcomp (kmult _) v)

  push-frm (khom f) v = vcomp (khom f) v
  push-frm (kmap k) v = push-kmap k v
  push-frm (kunit _) v = vcomp (kunit _) v
  push-frm (kmult _) v = push-kmult v

  do-vcomp : Value Y Z → Value X Y → Value X Z
  do-vcomp vid v2 = v2
  do-vcomp (vcomp k v1) v2 = push-frm k (do-vcomp v1 v2)

  eval : ‶Hom‶ X Y → Value X Y
  eval (‶M₁‶ e) = do-vmap (eval e)
  eval (‶η‶ X) = vcomp (kunit X) vid
  eval (‶μ‶ X) = vcomp (kmult X) vid
  eval (e1 ‶∘‶ e2) = do-vcomp (eval e1) (eval e2)
  eval ‶id‶ = vid
  eval (f ↑) = vcomp (khom f) vid

  --------------------------------------------------------------------------------
  -- Soundness

  vmap-sound : ∀ (v : Value X Y) → ⟦ do-vmap v ⟧ᵥ ≡ M₁ ⟦ v ⟧ᵥ
  vmap-sound vid = sym M-id
  vmap-sound (vcomp k v) =
    M₁ ⟦ k ⟧ₖ ∘ ⟦ do-vmap v ⟧ᵥ ≡⟨ refl⟩∘⟨ vmap-sound v ⟩
    M₁ ⟦ k ⟧ₖ M.𝒟.∘ M₁ ⟦ v ⟧ᵥ  ≡˘⟨ M-∘ ⟦ k ⟧ₖ ⟦ v ⟧ᵥ ⟩
    M₁ (⟦ k ⟧ₖ ∘ ⟦ v ⟧ᵥ) ∎

  push-kmap-sound  : ∀ (k : Frame Y Z) → (v : Value X (‶M₀‶ Y)) → ⟦ push-kmap k v ⟧ᵥ ≡ M₁ ⟦ k ⟧ₖ ∘ ⟦ v ⟧ᵥ
  push-kmult-sound : (v : Value X (‶M₀‶ (‶M₀‶ Y))) → ⟦ push-kmult v ⟧ᵥ ≡ mult.η ⟦ Y ⟧ₒ ∘ ⟦ v ⟧ᵥ
  push-frm-sound   : ∀ (k : Frame Y Z) → (v : Value X Y) → ⟦ push-frm k v ⟧ᵥ ≡ ⟦ k ⟧ₖ ∘ ⟦ v ⟧ᵥ

  push-kmap-sound k vid = refl
  push-kmap-sound k (vcomp (kmap k') v) = refl
  push-kmap-sound {Y = Y} {Z = Z} {X = X} k (vcomp (kunit Y) v) =
    unit.η ⟦ Z ⟧ₒ ∘ ⟦ push-frm k v ⟧ᵥ      ≡⟨ refl⟩∘⟨ push-frm-sound k v ⟩
    unit.η ⟦ Z ⟧ₒ  ∘ ⟦ k ⟧ₖ ∘ ⟦ v ⟧ᵥ       ≡⟨ extendl (unit.is-natural ⟦ Y ⟧ₒ ⟦ Z ⟧ₒ ⟦ k ⟧ₖ) ⟩
    M₁ ⟦ k ⟧ₖ ∘ unit.η ⟦ Y ⟧ₒ ∘ ⟦ v ⟧ᵥ     ∎
  push-kmap-sound {Y = Y} {Z = Z} {X = X} k (vcomp (kmult Y) v) =
    mult.η ⟦ Z ⟧ₒ ∘ ⟦ push-kmap (kmap k) v ⟧ᵥ ≡⟨ refl⟩∘⟨ push-kmap-sound (kmap k) v ⟩
    mult.η ⟦ Z ⟧ₒ ∘ M₁ (M₁ ⟦ k ⟧ₖ) ∘ ⟦ v ⟧ᵥ   ≡⟨ extendl (mult.is-natural ⟦ Y ⟧ₒ ⟦ Z ⟧ₒ ⟦ k ⟧ₖ) ⟩
    M₁ ⟦ k ⟧ₖ ∘ mult.η ⟦ Y ⟧ₒ ∘ ⟦ v ⟧ᵥ        ∎

  push-kmult-sound vid = refl
  push-kmult-sound (vcomp (kmap (kmap k)) v) = refl
  push-kmult-sound (vcomp (kmap (kunit _)) v) = insertl left-ident
  push-kmult-sound (vcomp (kmap (kmult _)) v) = extendl (sym mult-assoc)
  push-kmult-sound (vcomp (kunit _) v) = insertl right-ident
  push-kmult-sound (vcomp (kmult _) v) = refl

  push-frm-sound (khom f) v = refl
  push-frm-sound (kmap k) v = push-kmap-sound k v
  push-frm-sound (kunit X) v = refl
  push-frm-sound (kmult X) v = push-kmult-sound v

  vcomp-sound : ∀ (v1 : Value Y Z) → (v2 : Value X Y) → ⟦ do-vcomp v1 v2 ⟧ᵥ ≡ ⟦ v1 ⟧ᵥ ∘ ⟦ v2 ⟧ᵥ
  vcomp-sound vid v2 = sym (idl ⟦ v2 ⟧ᵥ)
  vcomp-sound (vcomp k v1) v2 =
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
    _ h0∷ _ h0∷ _ v∷ xs

  pattern functor-args functor xs =
    _ h0∷ _ h0∷ _ h0∷ _ h0∷ _ h0∷ _ h0∷ functor v∷ xs

  pattern nat-trans-args nt args =
    _ h0∷ _ h0∷ _ h0∷ _ h0∷
    _ h0∷ _ h0∷
    _ h0∷ _ h0∷
    nt v∷ args
   

  pattern monad-args monad xs =
    _ h0∷ _ h0∷ _ h0∷ monad v∷ xs

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
  mk-monad-args monad args = unknown h0∷ unknown h0∷ unknown h0∷ monad v∷ args

  “solve” : Term → Term → Term → Term
  “solve” monad lhs rhs =
    def (quote NbE.solve) (mk-monad-args monad $ infer-hidden 2 $ lhs v∷ rhs v∷ def (quote refl) [] v∷ [])

  build-object-expr : Term → Term → TC Term
  build-object-expr monad (“M₀” monad' x) = do
    unify monad monad'
    x ← build-object-expr monad x
    returnTC $ con (quote NbE.‶M₀‶) (x v∷ [])
  build-object-expr monad x =
    returnTC $ con (quote NbE.‶_‶) (x v∷ [])

  build-hom-expr : Term → Term → TC Term
  build-hom-expr monad “id” =
    returnTC $ con (quote NbE.‶id‶) []
  build-hom-expr monad (“∘” f g) = do
    f ← build-hom-expr monad f
    g ← build-hom-expr monad g
    returnTC $ con (quote NbE._‶∘‶_) (f v∷ g v∷ [])
  build-hom-expr monad (“M₁” monad' f) = do
    unify monad monad'
    f ← build-hom-expr monad f
    returnTC $ con (quote NbE.‶M₁‶) (f v∷ [])
  build-hom-expr monad (“η” monad' x) = do
    unify monad monad'
    x ← build-object-expr monad x
    returnTC $ con (quote NbE.‶η‶) (x v∷ [])
  build-hom-expr monad (“μ” monad' x) = do
    x ← build-object-expr monad x
    unify monad monad'
    returnTC $ con (quote NbE.‶μ‶) (x v∷ [])
  build-hom-expr monad f =
    returnTC $ con (quote NbE._↑) (f v∷ [])

  dont-reduce : List Name
  dont-reduce =
    quote Precategory.id ∷ quote Precategory._∘_ ∷
    quote Functor.F₀ ∷ quote Functor.F₁ ∷
    quote _=>_.η ∷
    quote Monad.M ∷ quote Monad.unit ∷ quote Monad.mult ∷ []

  solve-macro : ∀ {o h} {𝒞 : Precategory o h} → Monad 𝒞 → Term → TC ⊤
  solve-macro monad hole =
    withNormalisation false $
    dontReduceDefs dont-reduce $ do
      monad-tm ← quoteTC monad
      goal ← inferType hole >>= reduce
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
     
