open import 1Lab.Reflection

open import Cat.Prelude

import Cat.Reasoning as Cr
import Cat.Solver as Cs

module Cat.Functor.Solver where

open Functor

module NbE where
  open Cs.NbE using (`id ; _↑ ; _`∘_)

  private
    module CE = Cs.NbE
    variable
      o o' h h' : Level
      𝒟 : Precategory o h

  CExpr : (𝒞 : Precategory o h) → ⌞ 𝒞 ⌟ → ⌞ 𝒞 ⌟ → Type (o ⊔ h)
  CExpr = CE.Expr

  data FExpr : (𝒟 : Precategory o h) → ⌞ 𝒟 ⌟ → ⌞ 𝒟 ⌟ → Typeω where
    `F₁
      : (𝒞 : Precategory o h) (F : Functor 𝒞 𝒟) {A B : ⌞ 𝒞 ⌟}
      → FExpr 𝒞 A B → FExpr 𝒟 (F .F₀ A) (F .F₀ B)
    _`∘_ : {X Y Z : ⌞ 𝒟 ⌟} → FExpr 𝒟 Y Z → FExpr 𝒟 X Y → FExpr 𝒟 X Z
    `id  : {X : ⌞ 𝒟 ⌟} → FExpr 𝒟 X X
    _↑   : {X Y : ⌞ 𝒟 ⌟} → Cr.Hom 𝒟 X Y → FExpr 𝒟 X Y

  unfexpr : (𝒟 : Precategory o h) {X Y : ⌞ 𝒟 ⌟} → FExpr 𝒟 X Y → Cr.Hom 𝒟 X Y
  unfexpr 𝒟 (`F₁ 𝒞 F e) = F .F₁ (unfexpr 𝒞 e)
  unfexpr 𝒟 (e1 `∘ e2)  = unfexpr 𝒟 e1 ∘ unfexpr 𝒟 e2 where open Precategory 𝒟
  unfexpr 𝒟 `id         = Cr.id 𝒟
  unfexpr 𝒟 (f ↑)       = f

  --------------------------------------------------------------------------------
  -- Evaluation

  do-fmap
    : (𝒞 : Precategory o h) (𝒟 : Precategory o' h') (F : Functor 𝒞 𝒟)
    → {A B : ⌞ 𝒞 ⌟} → CExpr 𝒞 A B → CExpr 𝒟 (F .F₀ A) (F .F₀ B)
  do-fmap 𝒞 𝒟 F `id       = `id
  do-fmap 𝒞 𝒟 F (e `∘ e₁) = do-fmap 𝒞 𝒟 F e `∘ do-fmap 𝒞 𝒟 F e₁
  do-fmap 𝒞 𝒟 F (f ↑)     = F .F₁ f ↑

  eval : (𝒟 : Precategory o h) {X Y : ⌞ 𝒟 ⌟} → FExpr 𝒟 X Y → CExpr 𝒟 X Y
  eval 𝒟 (`F₁ 𝒞 F e) = do-fmap 𝒞 𝒟 F (eval 𝒞 e)
  eval 𝒟 (e1 `∘ e2)  = eval 𝒟 e1 `∘ eval 𝒟 e2
  eval 𝒟 `id         = `id
  eval 𝒟 (f ↑)       = f ↑

  nf : (𝒟 : Precategory o h) {X Y : ⌞ 𝒟 ⌟} → FExpr 𝒟 X Y → Cr.Hom 𝒟 X Y
  nf 𝒟 e = CE.nf 𝒟 (eval 𝒟 e)

  --------------------------------------------------------------------------------
  -- Soundness

  do-fmap-sound
    : (𝒞 : Precategory o h) (𝒟 : Precategory o' h') (F : Functor 𝒞 𝒟) {A B : ⌞ 𝒞 ⌟}
    → (v : CE.Expr 𝒞 A B) → CE.embed 𝒟 (do-fmap 𝒞 𝒟 F v) ≡ F .F₁ (CE.embed 𝒞 v)
  do-fmap-sound 𝒞 𝒟 F `id       = sym (F .F-id)
  do-fmap-sound 𝒞 𝒟 F (v `∘ v₁) =
    CE.embed 𝒟 (do-fmap 𝒞 𝒟 F v) 𝒟.∘ CE.embed 𝒟 (do-fmap 𝒞 𝒟 F v₁) ≡⟨ ap₂ 𝒟._∘_ (do-fmap-sound 𝒞 𝒟 F v) (do-fmap-sound 𝒞 𝒟 F v₁) ⟩
    F .F₁ (CE.embed 𝒞 v) 𝒟.∘ F .F₁ (CE.embed 𝒞 v₁)                    ≡˘⟨ F .F-∘ _ _ ⟩
    F .F₁ (CE.embed 𝒞 v 𝒞.∘ CE.embed 𝒞 v₁)                            ∎
    where
      module 𝒟 = Precategory 𝒟
      module 𝒞 = Precategory 𝒞
  do-fmap-sound 𝒞 𝒟 F (x ↑) = refl

  eval-sound
    : (𝒟 : Precategory o h) {X Y : ⌞ 𝒟 ⌟} → (e : FExpr 𝒟 X Y)
    → CE.embed 𝒟 (eval 𝒟 e) ≡ unfexpr 𝒟 e
  eval-sound 𝒟 (`F₁ 𝒞 F v) =
    do-fmap-sound 𝒞 𝒟 F (eval 𝒞 v) ∙ ap (F .F₁) (eval-sound 𝒞 v)
  eval-sound 𝒟 (e `∘ e₁) = ap₂ _∘_ (eval-sound 𝒟 e) (eval-sound 𝒟 e₁)
    where open Precategory 𝒟
  eval-sound 𝒟 `id   = refl
  eval-sound 𝒟 (f ↑) = refl

  nf-sound
    : (𝒟 : Precategory o h) {X Y : ⌞ 𝒟 ⌟} (e : FExpr 𝒟 X Y) → nf 𝒟 e ≡ unfexpr 𝒟 e
  nf-sound 𝒟 e = CE.eval-sound 𝒟 (eval 𝒟 e) ∙ eval-sound 𝒟 e

  abstract
    solve
      : (𝒟 : Precategory o h) {X Y : ⌞ 𝒟 ⌟} → (e1 e2 : FExpr 𝒟 X Y)
      → nf 𝒟 e1 ≡ nf 𝒟 e2 → unfexpr 𝒟 e1 ≡ unfexpr 𝒟 e2
    solve 𝒟 e1 e2 p = sym (nf-sound 𝒟 e1) ∙∙ p ∙∙ (nf-sound 𝒟 e2)

module Reflection where

  pattern category-args xs = _ hm∷ _ hm∷ _ v∷ xs

  pattern functor-args cat functor xs =
    _ hm∷ _ hm∷ cat hm∷ _ hm∷ _ hm∷ _ hm∷ functor v∷ xs

  pattern “id” =
    def (quote Precategory.id) (category-args (_ h∷ []))

  pattern “∘” f g =
    def (quote Precategory._∘_) (category-args (_ h∷ _ h∷ _ h∷ f v∷ g v∷ []))

  pattern “F₁” cat functor f =
    def (quote Functor.F₁) (functor-args cat functor (_ h∷ _ h∷ f v∷ []))

  “solve” : Term → Term → Term → Term
  “solve” cat lhs rhs =
    def (quote NbE.solve) (cat v∷ lhs v∷ rhs v∷ def (quote refl) [] v∷ [])

  build-fexpr : Term → Term
  build-fexpr “id”      = con (quote NbE.FExpr.`id) []
  build-fexpr (“∘” f g) = con (quote NbE.FExpr._`∘_)
    (build-fexpr f v∷ build-fexpr g v∷ [])
  build-fexpr (“F₁” cat functor f) = con (quote NbE.FExpr.`F₁)
    (cat v∷ functor v∷ build-fexpr f v∷ [])
  build-fexpr f = con (quote NbE.FExpr._↑) (f v∷ [])

  dont-reduce : List Name
  dont-reduce = quote Precategory.id ∷ quote Precategory._∘_ ∷ quote Functor.F₁ ∷ []

module _ {o h} (𝒟 : Precategory o h) {x y : ⌞ 𝒟 ⌟} {h1 h2 : 𝒟 .Precategory.Hom x y} where
  open Reflection
  functor-worker : Term → TC ⊤
  functor-worker hole =
   withNormalisation true $
   withReduceDefs (false , dont-reduce) $ do
     `h1 ← wait-for-type =<< quoteTC h1
     `h2 ← quoteTC h2
     `𝒟 ← quoteTC 𝒟
     let
       elhs = build-fexpr `h1
       erhs = build-fexpr `h2
     noConstraints $ unify hole (“solve” `𝒟 elhs erhs)

  functor-wrapper : {@(tactic functor-worker) p : h1 ≡ h2} → h1 ≡ h2
  functor-wrapper {p = p} = p

macro
  functor! : Term → Term → TC ⊤
  functor! cat = flip unify (def (quote functor-wrapper) (cat v∷ []))

private
  module Test
    {o h} {𝒞 𝒟 ℰ : Precategory o h} (F : Functor 𝒞 𝒟) (G : Functor 𝒟 ℰ) where
    module 𝒞 = Precategory 𝒞
    module 𝒟 = Precategory 𝒟
    module ℰ = Precategory ℰ

    variable
      A B : 𝒞.Ob
      a b : 𝒞.Hom A B

    test
      : G .F₁ (F .F₁ a 𝒟.∘ 𝒟.id) ℰ.∘ G .F₁ (F .F₁ (b 𝒞.∘ 𝒞.id)) ℰ.∘ ℰ.id
      ≡ G .F₁ (F .F₁ (a 𝒞.∘ b))
    test = functor! ℰ
