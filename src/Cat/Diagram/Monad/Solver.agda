module Cat.Diagram.Monad.Solver where

open import 1Lab.Prelude hiding (id; _∘_)
open import 1Lab.Reflection hiding (_++_)

open import Cat.Base
open import Cat.Reflection
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
  -- We can′t index everything by 'Ob', as Agda will (rightfully) assume that M₀ is not injective,
  -- which then inhibits on our ability to pattern match on things.
  -- Therefore, we introduce a reflected type of object expressions,
  -- which solves the injectivity issue.

  data ‶Ob‶ : Typeω where
    ‶_‶   : Ob → ‶Ob‶
    ‶M₀‶ : ‶Ob‶ → ‶Ob‶

  ⟦_⟧ₒ : ‶Ob‶ → Ob
  ⟦ ‶ X ‶ ⟧ₒ = X
  ⟦ ‶M₀‶ X ⟧ₒ = M₀ ⟦ X ⟧ₒ

  private variable
    W X Y Z : ‶Ob‶

  data ‶Hom‶ : ‶Ob‶ → ‶Ob‶ → Typeω where
    ‶M₁‶  : ‶Hom‶ X Y → ‶Hom‶ (‶M₀‶ X) (‶M₀‶ Y)
    ‶η‶   : (X : ‶Ob‶) → ‶Hom‶ X (‶M₀‶ X)
    ‶μ‶   : (X : ‶Ob‶) → ‶Hom‶ (‶M₀‶ (‶M₀‶ X)) (‶M₀‶ X)
    _‶∘‶_ : ‶Hom‶ Y Z → ‶Hom‶ X Y → ‶Hom‶ X Z
    ‶id‶  : ‶Hom‶ X X
    ↑    : ∀ X Y → Hom ⟦ X ⟧ₒ ⟦ Y ⟧ₒ → ‶Hom‶ X Y

  ⟦_⟧ₕ : ‶Hom‶ X Y → Hom ⟦ X ⟧ₒ ⟦ Y ⟧ₒ
  ⟦ ‶M₁‶ f ⟧ₕ = M₁ ⟦ f ⟧ₕ
  ⟦ ‶η‶ X ⟧ₕ = unit.η ⟦ X ⟧ₒ
  ⟦ ‶μ‶ X ⟧ₕ = mult.η ⟦ X ⟧ₒ
  ⟦ e1 ‶∘‶ e2 ⟧ₕ = ⟦ e1 ⟧ₕ ∘ ⟦ e2 ⟧ₕ
  ⟦ ‶id‶ ⟧ₕ = id
  ⟦ ↑ x y f ⟧ₕ = f

  --------------------------------------------------------------------------------
  -- Values

  data Frame : ‶Ob‶ → ‶Ob‶ → Typeω where
    khom  : ∀ {X Y} → Hom ⟦ X ⟧ₒ ⟦ Y ⟧ₒ → Frame X Y
    kmap  : Frame X Y → Frame (‶M₀‶ X) (‶M₀‶ Y)
    kunit : (X : ‶Ob‶) → Frame X (‶M₀‶ X)
    kmult : (X : ‶Ob‶) → Frame (‶M₀‶ (‶M₀‶ X)) (‶M₀‶ X)

  data Value : ‶Ob‶ → ‶Ob‶ → Typeω where
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
  enact-laws (kmap k) (khom f) v = kmap k ∷ khom f ∷ v
  enact-laws (kmap k) (kmap k') v = do-vmap (enact-laws k k' []) ++ v      -- Functoriality
  enact-laws (kmap k) (kunit _) v = kunit _ ∷ push-frm k v                 -- Naturality
  enact-laws (kmap k) (kmult _) v = kmult _ ∷ push-frm (kmap (kmap k)) v   -- Naturality
  enact-laws (kunit _) k' v = kunit _ ∷ k' ∷ v
  enact-laws (kmult _) (khom f) v = kmult _ ∷ khom f ∷ v
  enact-laws (kmult _) (kmap (khom f)) v = kmult _ ∷ kmap (khom f) ∷ v
  enact-laws (kmult _) (kmap (kmap k')) v = kmult _ ∷ kmap (kmap k') ∷ v
  enact-laws (kmult _) (kmap (kunit _)) v = v                              -- Left Identity
  enact-laws (kmult _) (kmap (kmult _)) v = kmult _ ∷ push-frm (kmult _) v -- Associativity
  enact-laws (kmult _) (kunit _) v = v                                     -- Right Identity
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
  eval (↑ x y f) = khom f ∷ []

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

  enact-laws-sound (khom f) k' v = refl
  enact-laws-sound (kmap k1) (khom f) v = refl
  enact-laws-sound (kmap k1) (kmap k2) v =
    ⟦ do-vmap (enact-laws k1 k2 []) ++ v ⟧ᵥ     ≡⟨ vconcat-sound (do-vmap (enact-laws k1 k2 [])) v ⟩
    ⟦ do-vmap (enact-laws k1 k2 []) ⟧ᵥ ∘ ⟦ v ⟧ᵥ ≡⟨ vmap-sound (enact-laws k1 k2 []) ⟩∘⟨refl ⟩
    M₁ ⟦ enact-laws k1 k2 [] ⟧ᵥ M.𝒟.∘ ⟦ v ⟧ᵥ    ≡⟨ M.pushl (enact-laws-sound k1 k2 []) ⟩
    M₁ ⟦ k1 ⟧ₖ ∘ M₁ (⟦ k2 ⟧ₖ ∘ id) ∘ ⟦ v ⟧ᵥ     ≡⟨ refl⟩∘⟨ (M.⟨ idr ⟦ k2 ⟧ₖ ⟩ ⟩∘⟨refl) ⟩
    M₁ ⟦ k1 ⟧ₖ ∘ M₁ ⟦ k2 ⟧ₖ ∘ ⟦ v ⟧ᵥ            ∎
  enact-laws-sound (kmap k1) (kunit _) v =
    unit.η _ ∘ ⟦ push-frm k1 v ⟧ᵥ    ≡⟨ refl⟩∘⟨ push-frm-sound k1 v ⟩
    unit.η _ ∘ ⟦ k1 ⟧ₖ ∘ ⟦ v ⟧ᵥ      ≡⟨ extendl (unit.is-natural _ _ ⟦ k1 ⟧ₖ) ⟩
    M.F₁ ⟦ k1 ⟧ₖ ∘ unit.η _ ∘ ⟦ v ⟧ᵥ ∎
  enact-laws-sound (kmap k1) (kmult _) v =
    mult.η _ ∘ ⟦ push-frm (kmap (kmap k1)) v ⟧ᵥ ≡⟨ refl⟩∘⟨ push-frm-sound (kmap (kmap k1)) v ⟩
    mult.η _ ∘ M₁ (M₁ ⟦ k1 ⟧ₖ) ∘ ⟦ v ⟧ᵥ         ≡⟨ extendl (mult.is-natural _ _ ⟦ k1 ⟧ₖ) ⟩
    M.F₁ ⟦ k1 ⟧ₖ ∘ mult.η _ ∘ ⟦ v ⟧ᵥ            ∎
  enact-laws-sound (kunit _) k2 v = refl
  enact-laws-sound (kmult _) (khom f) v = refl
  enact-laws-sound (kmult _) (kmap (khom f)) v = refl
  enact-laws-sound (kmult _) (kmap (kmap k2)) v = refl
  enact-laws-sound (kmult _) (kmap (kunit _)) v = insertl left-ident
  enact-laws-sound (kmult _) (kmap (kmult _)) v =
    mult.η _ ∘ ⟦ push-frm (kmult _) v ⟧ᵥ ≡⟨ refl⟩∘⟨ push-frm-sound (kmult _) v ⟩
    mult.η _ ∘ mult.η (M₀ _) ∘ ⟦ v ⟧ᵥ    ≡⟨ extendl (sym mult-assoc) ⟩
    mult.η _ ∘ M₁ (mult.η _) ∘ ⟦ v ⟧ᵥ    ∎
  enact-laws-sound (kmult _) (kunit _) v = insertl right-ident
  enact-laws-sound (kmult _) (kmult _) v = refl

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
  eval-sound (↑ x y f) = idr f

  abstract
    solve : ∀ (e1 e2 : ‶Hom‶ X Y) → ⟦ eval e1 ⟧ᵥ ≡ ⟦ eval e2 ⟧ᵥ → ⟦ e1 ⟧ₕ ≡ ⟦ e2 ⟧ₕ
    solve e1 e2 p = sym (eval-sound e1) ·· p ·· (eval-sound e2)

module Reflection where

  pattern monad-args monad xs =
    _ hm∷ _ hm∷ _ hm∷ monad v∷ xs

  mk-monad-args : Term → List (Arg Term) → List (Arg Term)
  mk-monad-args monad xs = infer-hidden 3 $ monad v∷ xs

  record Monad-terms : Type where
    field
      cat : Term
      monad : Term

    functor : Term
    functor = def (quote Monad.M) (mk-monad-args monad [])

    functor-tms : Functor-terms
    functor-tms = record
      { c-cat = cat
      ; d-cat = cat
      ; functor = functor
      }

    unit-tms : Nat-trans-terms
    unit-tms = record
      { c-cat = cat
      ; d-cat = cat
      ; F-functor = “Id” cat
      ; G-functor = functor
      ; nat-trans = def (quote Monad.unit) (mk-monad-args monad [])
      }

    mult-tms : Nat-trans-terms
    mult-tms = record
      { c-cat = cat
      ; d-cat = cat
      ; F-functor = functor “F∘” functor
      ; G-functor = functor
      ; nat-trans = def (quote Monad.mult) (mk-monad-args monad [])
      }

  open Monad-terms

  quote-monad-terms : ∀ {o ℓ} {C : Precategory o ℓ} → Monad C → TC Monad-terms
  quote-monad-terms {C = C} M = do
    cat ← quoteTC C
    monad ← quoteTC M
    pure (record { cat = cat ; monad = monad })

  match-M₀ : Monad-terms → Term → TC Term
  match-M₀ m tm = match-F₀ (functor-tms m) tm

  match-M₁ : Monad-terms → Term → TC Term
  match-M₁ m tm = match-F₁ (functor-tms m) tm

  match-unit : Monad-terms → Term → TC Term
  match-unit m tm = match-η (unit-tms m) tm

  match-mult : Monad-terms → Term → TC Term
  match-mult m tm = match-η (mult-tms m) tm

  “solve” : Term → Term → Term → Term
  “solve” monad lhs rhs =
    def (quote NbE.solve) (mk-monad-args monad $ infer-hidden 2 $ lhs v∷ rhs v∷ def (quote refl) [] v∷ [])

  {-# TERMINATING #-}
  build-object-expr : Monad-terms → Term → TC Term
  build-object-expr m tm =
    (do
       x ← match-M₀ m tm
       x ← build-object-expr m x
       pure $ con (quote NbE.‶M₀‶) (x v∷ []))
    <|>
    (pure $ con (quote NbE.‶_‶) (tm v∷ []))

  build-neu-hom-expr : Monad-terms → Term → TC Term
  build-neu-hom-expr m f = do
    x , y ← get-hom-objects (m .cat) =<< inferType f
    debugPrint "tactic" 50
      [ "Building neutral hom expression: " , termErr f
      , "\n  Has type: Hom (" , termErr x , ") (" , termErr y , ")"
      ]
    x ← build-object-expr m =<< normalise x
    y ← build-object-expr m =<< normalise y
    returnTC $ con (quote NbE.↑) (x v∷ y v∷ f v∷ [])

  {-# TERMINATING #-}
  build-hom-expr : Monad-terms → Term → TC Term
  build-hom-expr m tm =
    (do
       match-id (m .cat) tm
       pure (con (quote NbE.‶id‶) []))
    <|>
    (do
       f , g ← match-∘ (m .cat) tm
       f ← build-hom-expr m f
       g ← build-hom-expr m g
       pure (con (quote NbE._‶∘‶_) (f v∷ g v∷ [])))
    <|>
    (do
       f ← match-M₁ m tm
       f ← build-hom-expr m f
       pure (con (quote NbE.‶M₁‶) (f v∷ [])))
    <|>
    (do
       x ← match-unit m tm
       x ← build-object-expr m x
       pure (con (quote NbE.‶η‶) (x v∷ [])))
    <|>
    (do
       x ← match-mult m tm
       x ← build-object-expr m x
       pure (con (quote NbE.‶μ‶) (x v∷ [])))
    <|>
    (build-neu-hom-expr m tm)

  solve-macro : ∀ {o h} {𝒞 : Precategory o h} → Monad 𝒞 → Term → TC ⊤
  solve-macro M hole = do
    monad-tms ← quote-monad-terms M
    goal ← inferType hole >>= reduce
    just (lhs , rhs) ← get-boundary goal
      where nothing → typeError $ strErr "Can't determine boundary: " ∷
                                  termErr goal ∷ []
    elhs ← build-hom-expr monad-tms =<< normalise lhs
    erhs ← build-hom-expr monad-tms =<< normalise rhs
    catchTC
      (noConstraints $ unify hole (“solve” (monad-tms .monad) elhs erhs))
      (typeError $
        strErr "Could not solve monad equation:\n  "
        ∷ termErr lhs ∷ strErr " ≡ " ∷ termErr rhs
        ∷ "\nReflected representation:\nRHS: "
        ∷ termErr elhs ∷ strErr "\nLHS: " ∷ termErr erhs
        ∷ [])

macro
  monad! : ∀ {o h} {C : Precategory o h} → Monad C → Term → TC ⊤
  monad! M = Reflection.solve-macro M

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

  test-type : ∀ {x y} → (f : Hom x (M₀ y)) → mult.η y ∘ M₁ f ∘ unit.η x ≡ f
  test-type _ = monad! monad
