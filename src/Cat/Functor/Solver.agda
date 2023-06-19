open import 1Lab.Reflection
open import 1Lab.Reflection.Solver
open import 1Lab.Prelude

open import Cat.Base
open import Cat.Reflection

open import Data.List

import Cat.Reasoning as Cat

module Cat.Functor.Solver where


module NbE {o h o′ h′} {𝒞 : Precategory o h} {𝒟 : Precategory o′ h′} (F : Functor 𝒞 𝒟) where
  private
    module 𝒞 = Cat 𝒞
    module 𝒟 = Cat 𝒟
    open Functor F

    variable
      A B C : 𝒞.Ob
      X Y Z : 𝒟.Ob

  data CExpr : 𝒞.Ob → 𝒞.Ob → Typeω where
    _‶∘‶_ : CExpr B C → CExpr A B → CExpr A C
    ‶id‶  : CExpr A A
    _↑    : 𝒞.Hom A B → CExpr A B

  data DExpr : 𝒟.Ob → 𝒟.Ob → Typeω where
    ‶F₁‶  : CExpr A B → DExpr (F₀ A) (F₀ B)
    _‶∘‶_ : DExpr Y Z → DExpr X Y → DExpr X Z
    ‶id‶  : DExpr X X
    _↑    : 𝒟.Hom X Y → DExpr X Y

  uncexpr : CExpr A B → 𝒞.Hom A B
  uncexpr (e1 ‶∘‶ e2) = uncexpr e1 𝒞.∘ uncexpr e2
  uncexpr ‶id‶ = 𝒞.id
  uncexpr (f ↑) = f

  undexpr : DExpr X Y → 𝒟.Hom X Y
  undexpr (‶F₁‶ e) = F₁ (uncexpr e)
  undexpr (e1 ‶∘‶ e2) = undexpr e1 𝒟.∘ undexpr e2
  undexpr ‶id‶ = 𝒟.id
  undexpr (f ↑) = f

  --------------------------------------------------------------------------------
  -- Values

  data CValue : 𝒞.Ob → 𝒞.Ob → Typeω where
    vid : CValue A A
    vcomp : 𝒞.Hom B C → CValue A B → CValue A C

  data Frame : 𝒟.Ob → 𝒟.Ob → Typeω where
    vhom : 𝒟.Hom X Y → Frame X Y
    vfmap : 𝒞.Hom A B → Frame (F₀ A) (F₀ B)

  data DValue : 𝒟.Ob → 𝒟.Ob → Typeω where
    vid   : DValue X X
    vcomp : Frame Y Z → DValue X Y → DValue X Z

  uncvalue : CValue A B → 𝒞.Hom A B
  uncvalue vid = 𝒞.id
  uncvalue (vcomp f v) = f 𝒞.∘ uncvalue v

  unframe : Frame X Y → 𝒟.Hom X Y
  unframe (vhom f) = f
  unframe (vfmap f) = F₁ f

  undvalue : DValue X Y → 𝒟.Hom X Y
  undvalue vid = 𝒟.id
  undvalue (vcomp f v) = unframe f 𝒟.∘ undvalue v

  --------------------------------------------------------------------------------
  -- Evaluation

  do-cvcomp : CValue B C → CValue A B → CValue A C
  do-cvcomp vid v2 = v2
  do-cvcomp (vcomp f v1) v2 = vcomp f (do-cvcomp v1 v2)

  ceval : CExpr A B → CValue A B
  ceval (e1 ‶∘‶ e2) = do-cvcomp (ceval e1) (ceval e2)
  ceval ‶id‶ = vid
  ceval (f ↑) = vcomp f vid

  do-dvcomp : DValue Y Z → DValue X Y → DValue X Z
  do-dvcomp vid v2 = v2
  do-dvcomp (vcomp f v1) v2 = vcomp f (do-dvcomp v1 v2)

  do-vfmap : CValue A B → DValue (F₀ A) (F₀ B)
  do-vfmap vid = vid
  do-vfmap (vcomp f v) = vcomp (vfmap f) (do-vfmap v)

  deval : DExpr X Y → DValue X Y
  deval (‶F₁‶ e) = do-vfmap (ceval e)
  deval (e1 ‶∘‶ e2) = do-dvcomp (deval e1) (deval e2)
  deval ‶id‶ = vid
  deval (f ↑) = vcomp (vhom f) vid

  --------------------------------------------------------------------------------
  -- Soundness

  do-cvcomp-sound : ∀ (v1 : CValue B C) → (v2 : CValue A B) → uncvalue (do-cvcomp v1 v2) ≡ uncvalue v1 𝒞.∘ uncvalue v2
  do-cvcomp-sound vid v2 = sym (𝒞.idl (uncvalue v2))
  do-cvcomp-sound (vcomp f v1) v2 = 𝒞.pushr (do-cvcomp-sound v1 v2)

  ceval-sound : ∀ (e : CExpr A B) → uncvalue (ceval e) ≡ uncexpr e
  ceval-sound (e1 ‶∘‶ e2) =
    uncvalue (do-cvcomp (ceval e1) (ceval e2))    ≡⟨ do-cvcomp-sound (ceval e1) (ceval e2) ⟩
    (uncvalue (ceval e1) 𝒞.∘ uncvalue (ceval e2)) ≡⟨ ap₂ 𝒞._∘_ (ceval-sound e1) (ceval-sound e2) ⟩
    uncexpr e1 𝒞.∘ uncexpr e2                     ∎
  ceval-sound ‶id‶ = refl
  ceval-sound (f ↑) = 𝒞.idr f

  do-vfmap-sound : ∀ (v : CValue A B) → undvalue (do-vfmap v) ≡ F₁ (uncvalue v)
  do-vfmap-sound vid = sym F-id
  do-vfmap-sound (vcomp f v) =
    F₁ f 𝒟.∘ undvalue (do-vfmap v) ≡⟨ ap (F₁ f 𝒟.∘_) (do-vfmap-sound v) ⟩
    F₁ f 𝒟.∘ F₁ (uncvalue v)       ≡˘⟨ F-∘ f (uncvalue v) ⟩
    F₁ (f 𝒞.∘ uncvalue v)          ∎

  do-dvcomp-sound : ∀ (v1 : DValue Y Z) → (v2 : DValue X Y) → undvalue (do-dvcomp v1 v2) ≡ undvalue v1 𝒟.∘ undvalue v2
  do-dvcomp-sound vid v2 = sym (𝒟.idl (undvalue v2))
  do-dvcomp-sound (vcomp f v1) v2 = 𝒟.pushr (do-dvcomp-sound v1 v2)

  deval-sound : ∀ (e : DExpr X Y) → undvalue (deval e) ≡ undexpr e
  deval-sound (‶F₁‶ e) =
    undvalue (do-vfmap (ceval e)) ≡⟨ do-vfmap-sound (ceval e) ⟩
    F₁ (uncvalue (ceval e))       ≡⟨ ap F₁ (ceval-sound e ) ⟩
    F₁ (uncexpr e)                ∎
  deval-sound (e1 ‶∘‶ e2) =
    undvalue (do-dvcomp (deval e1) (deval e2))  ≡⟨ do-dvcomp-sound (deval e1) (deval e2) ⟩
    undvalue (deval e1) 𝒟.∘ undvalue (deval e2) ≡⟨ ap₂ 𝒟._∘_ (deval-sound e1) (deval-sound e2) ⟩
    undexpr e1 𝒟.∘ undexpr e2                   ∎
  deval-sound ‶id‶ = refl
  deval-sound (f ↑) = 𝒟.idr f

  abstract
    solve : (e1 e2 : DExpr X Y) → undvalue (deval e1) ≡ undvalue (deval e2) → undexpr e1 ≡ undexpr e2
    solve e1 e2 p  = sym (deval-sound e1) ·· p ·· (deval-sound e2)

  nf : DExpr X Y → 𝒟.Hom X Y
  nf e = undvalue (deval e)

module Reflection where
  open Functor-terms

  invoke-solver : Functor-terms → Term → Term → Term
  invoke-solver func lhs rhs =
    def (quote NbE.solve) (functor-args (func .functor) $ infer-hidden 2 $ lhs v∷ rhs v∷ “refl” v∷ [])

  invoke-normaliser : Functor-terms → Term → Term
  invoke-normaliser func e =
    def (quote NbE.solve) (functor-args (func .functor) $ infer-hidden 2 $ e v∷ [])

  {-# TERMINATING #-}
  build-cexpr : Functor-terms → Term → TC Term
  build-cexpr func tm =
    (do
       match-id (func .c-cat) tm
       pure (con (quote NbE.CExpr.‶id‶) []))
    <|>
    (do
       f , g ← match-∘ (func .c-cat) tm
       f ← build-cexpr func f
       g ← build-cexpr func g
       pure (con (quote NbE.CExpr._‶∘‶_) (f v∷ g v∷ [])))
    <|>
    (pure (con (quote NbE.CExpr._↑) (tm v∷ [])))

  {-# TERMINATING #-}
  build-dexpr : Functor-terms → Term → TC Term
  build-dexpr func tm =
    (do
       match-id (func .d-cat) tm
       pure (con (quote NbE.DExpr.‶id‶) []))
    <|>
    (do
       f , g ← match-∘ (func .d-cat) tm
       f ← build-dexpr func f
       g ← build-dexpr func g
       pure (con (quote NbE.DExpr._‶∘‶_) (f v∷ g v∷ [])))
    <|>
    (do
       f ← match-F₁ func tm
       f ← build-cexpr func f
       pure (con (quote NbE.DExpr.‶F₁‶) (f v∷ [])))
    <|>
    (pure (con (quote NbE.DExpr._↑) (tm v∷ [])))

  functor-solver
    : ∀ {o h o′ h′} {C : Precategory o h} {D : Precategory o′ h′}
    → Functor C D
    → TC Simple-solver
  functor-solver F = do
    func ← quote-functor-terms F
    pure (simple-solver [] (build-dexpr func) (invoke-solver func) (invoke-normaliser func))
macro
  repr-functor!
    : ∀ {o h o′ h′} {𝒞 : Precategory o h} {𝒟 : Precategory o′ h′}
    → Functor 𝒞 𝒟
    → Term → Term → TC ⊤
  repr-functor! F = mk-simple-repr (Reflection.functor-solver F)

  simpl-functor!
    : ∀ {o h o′ h′} {𝒞 : Precategory o h} {𝒟 : Precategory o′ h′}
    → Functor 𝒞 𝒟
    → Term → Term → TC ⊤
  simpl-functor! F = mk-simple-normalise (Reflection.functor-solver F)

  functor!
    : ∀ {o h o′ h′} {𝒞 : Precategory o h} {𝒟 : Precategory o′ h′}
    → Functor 𝒞 𝒟
    → Term → TC ⊤
  functor! F = mk-simple-solver (Reflection.functor-solver F)

private module Test {o h o′ h′} {𝒞 : Precategory o h} {𝒟 : Precategory o′ h′} (F : Functor 𝒞 𝒟) where
  module 𝒞 = Cat 𝒞
  module 𝒟 = Cat 𝒟
  open Functor F

  variable
    A B : 𝒞.Ob
    X Y : 𝒟.Ob
    a b c : 𝒞.Hom A B
    x y z : 𝒟.Hom X Y

  simple-test : F₁ a ≡ F₁ a
  simple-test = functor! F

  test : (x 𝒟.∘ F₁ (𝒞.id 𝒞.∘ 𝒞.id)) 𝒟.∘ F₁ a 𝒟.∘ F₁ (𝒞.id 𝒞.∘ b) ≡ 𝒟.id 𝒟.∘ x 𝒟.∘ F₁ (a 𝒞.∘ b)
  test = functor! F

  test-F₀ : (f : 𝒟.Hom (F₀ A) (F₀ B)) → f 𝒟.∘ F₁ 𝒞.id ≡ f
  test-F₀ f = functor! F
