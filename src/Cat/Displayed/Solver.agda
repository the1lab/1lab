module Cat.Displayed.Solver where

open import Data.List

open import 1Lab.Reflection
open import 1Lab.Reflection.Solver
open import 1Lab.Prelude hiding (id; _∘_)

open import Cat.Base
open import Cat.Reflection
open import Cat.Displayed.Base
open import Cat.Displayed.Reflection

import Cat.Solver
import Cat.Displayed.Reasoning as Dr

module NbE {o′ ℓ′ o′′ ℓ′′}
           {B : Precategory o′ ℓ′}
           (E : Displayed B o′′ ℓ′′)
           where

  open Displayed E
  module B = Precategory B
  open Dr E
  open Cat.Solver.NbE

  private variable
    a b c d e : B.Ob
    f g h i j : B.Hom a b
    a′ b′ c′ d′ e′ : Ob[ a ]
    f′ g′ h′ i′ j′ : Hom[ f ] a′ b′

  data Expr[_] : ∀ {a b} (f : Expr B a b) (a′ : Ob[ a ]) (b′ : Ob[ b ]) → Typeω where
    `id  : {a′ : Ob[ a ]} → Expr[ `id ] a′ a′
    _`∘_ : ∀ {a′ b′ c′} {f : Expr B b c} {g : Expr B a b}
           → Expr[ f ] b′ c′ → Expr[ g ] a′ b′ → Expr[ f `∘ g ] a′ c′
    _↑ : ∀ {a′ b′} {f : Expr B a b} → Hom[ embed B f ] a′ b′ → Expr[ f ] a′ b′
    `hom[_]_ : ∀ {a b} {a′ b′} {f g : Expr B a b} → embed B f ≡ embed B g → Expr[ f ] a′ b′ → Expr[ g ] a′ b′

  unexpr[_] : (d : Expr B a b) → Expr[ d ] a′ b′ → Hom[ embed B d ] a′ b′
  unexpr[ d ] (`hom[ p ] e)   = hom[ p ] (unexpr[ _ ] e)
  unexpr[ `id ] `id           = id′
  unexpr[ d `∘ d₁ ] (e `∘ e₁) = unexpr[ d ] e ∘′ unexpr[ d₁ ] e₁
  unexpr[ _ ] (hom ↑)         = hom

  data Stack[_] : ∀ {a b} → B.Hom a b → Ob[ a ] → Ob[ b ] → Typeω where
    [] : ∀ {a} {a′ : Ob[ a ]} → Stack[ B.id ] a′ a′
    _∷_ : ∀ {a b c a′ b′ c′} {f : B.Hom b c} {g : B.Hom a b} → Hom[ f ] b′ c′ → Stack[ g ] a′ b′ → Stack[ f B.∘ g ] a′ c′

  record Value[_] {a b} (f : B.Hom a b) (a′ : Ob[ a ]) (b′ : Ob[ b ]) : Typeω where
    constructor vsubst
    field
      {mor} : B.Hom a b
      vpath : mor ≡ f
      homs  : Stack[ mor ] a′ b′

  open Value[_]

  vid : Value[ B.id ] a′ a′
  vid = vsubst refl []

  vcomp′ : Hom[ f ] b′ c′ → Value[ g ] a′ b′ → Value[ f B.∘ g ] a′ c′
  vcomp′ {f = f} f′ (vsubst p homs) = vsubst (ap (f B.∘_) p) (f′ ∷ homs)

  vhom[_] : f ≡ g → Value[ f ] a′ b′ → Value[ g ] a′ b′
  vhom[_] p (vsubst q homs) = vsubst (q ∙ p) homs

  abstract
    adjust-k : ∀ {a b c} {f g : Expr B b c} {k : B.Hom a b} → embed B f ≡ embed B g → eval B f k ≡ eval B g k
    adjust-k {f = f'} {g = g'} {f} p = eval-sound-k B f' f ∙ ap (B._∘ _) p ∙ sym (eval-sound-k B g' f)

  eval′ : ∀ {e : Expr B b c} → Expr[ e ] b′ c′ → Value[ f ] a′ b′ → Value[ eval B e f ] a′ c′
  eval′ `id v′                    = v′
  eval′ (e₁′ `∘ e₂′) v′           = eval′ e₁′ (eval′ e₂′ v′)
  eval′ {e = e} (_↑ {f = f} f′) v′ =
    vhom[ sym (eval-sound-k B e _) ] (vcomp′ f′ v′)
  eval′ {f = f} (`hom[_]_ {f = f'} {g = g'} p e′) v′ =
    vhom[ adjust-k {f = f'} {g = g'} p ] (eval′ e′ v′)

  stack→map : Stack[ f ] a′ b′ → Hom[ f ] a′ b′
  stack→map [] = id′
  stack→map (x ∷ x₁) = x ∘′ stack→map x₁

  ⟦_⟧ : Value[ f ] a′ b′ → Hom[ f ] a′ b′
  ⟦ vsubst path homs ⟧ = hom[ path ] (stack→map homs)

  vid-sound : ⟦ vid {a′ = a′} ⟧ ≡ id′
  vid-sound = transport-refl _

  vcomp′-sound
    : (f′ : Hom[ f ] b′ c′) (v : Value[ g ] a′ b′)
    → ⟦ vcomp′ f′ v ⟧ ≡ f′ ∘′ ⟦ v ⟧
  vcomp′-sound f′ v = sym (whisker-r _)

  vhom-sound
    : (p : f ≡ g) (v : Value[ f ] a′ b′)
    → ⟦ vhom[ p ] v ⟧ ≡[ sym p ] ⟦ v ⟧
  vhom-sound p v = to-pathp⁻ (sym (hom[]-∙ _ _))

  nf′ : ∀ {f : Expr B a b} → Expr[ f ] a′ b′ → Hom[ nf B f ] a′ b′
  nf′ f = ⟦ eval′ f vid ⟧

  abstract
    eval′-sound-k
      : {e : Expr B a b} (e′ : Expr[ e ] b′ c′) (v : Value[ f ] a′ b′)
      → ⟦ eval′ e′ v ⟧ ≡[ eval-sound-k B e f ] unexpr[ e ] e′ ∘′ ⟦ v ⟧
    eval′-sound-k `id v = symP (idl′ ⟦ v ⟧)
    eval′-sound-k {e = f `∘ g} (f′ `∘ g′) v =
      ⟦ eval′ f′ (eval′ g′ v) ⟧                 ≡[]⟨ eval′-sound-k f′ _ ⟩
      unexpr[ f ] f′ ∘′ ⟦ eval′ g′ v ⟧          ≡[]⟨ (λ i → unexpr[ f ] f′ ∘′ eval′-sound-k g′ v i) ⟩
      unexpr[ f ] f′ ∘′ unexpr[ g ] g′ ∘′ ⟦ v ⟧ ≡[]⟨ assoc′ _ _ _ ⟩
      unexpr[ f `∘ g ] (f′ `∘ g′) ∘′ ⟦ v ⟧      ∎
    eval′-sound-k (x ↑) v = vhom-sound _ (vcomp′ x v) ▷ vcomp′-sound x v
    eval′-sound-k (`hom[_]_ {f = f} {g = g} p e′) v = cast[] $
      ⟦ vhom[ adjust-k {f = f} {g = g} p ] (eval′ e′ v) ⟧ ≡[]⟨ vhom-sound (adjust-k {f = f} {g = g} p) (eval′ e′ v) ⟩
      ⟦ eval′ e′ v ⟧                                      ≡[]⟨ eval′-sound-k e′ v ⟩
      unexpr[ f ] e′ ∘′ ⟦ v ⟧                             ≡[]⟨ to-pathp (sym (whisker-l p)) ⟩
      hom[ p ] (unexpr[ f ] e′) ∘′ ⟦ v ⟧                  ∎

    eval′-sound
      : (e : Expr B a b) (e′ : Expr[ e ] a′ b′)
      → nf′ e′ ≡[ eval-sound B e ] unexpr[ e ] e′
    eval′-sound e e′ = eval′-sound-k e′ vid
      ∙[] ap (unexpr[ e ] e′ ∘′_) vid-sound ◁ idr′ _

  abstract
    solve′ : ∀ {f g : Expr B a b} (f′ : Expr[ f ] a′ b′) (g′ : Expr[ g ] a′ b′)
               {q : embed B f ≡ embed B g}
             → (p : nf B f ≡ nf B g)
             → nf′ f′ ≡[ p ] nf′ g′
             → unexpr[ f ] f′ ≡[ q ] unexpr[ g ] g′
    solve′ {f = f} {g = g} f′ g′ p p′ = cast[] $
      unexpr[ f ] f′ ≡[]˘⟨ eval′-sound f f′ ⟩
      nf′ f′         ≡[]⟨ p′ ⟩
      nf′ g′         ≡[]⟨ eval′-sound g g′ ⟩
      unexpr[ g ] g′ ∎

module Reflection where
  module Cat = Cat.Solver.Reflection

  build-neu-expr : Displayed-terms → Term → TC Term
  build-neu-expr dtm tm = do
    f , x′ , y′ ← get-hom[]-objects dtm =<< inferType tm
    debugPrint "tactic" 50
      [ "Building neutral hom expression: " , termErr tm
      , "\n  Has type: Hom[ " , termErr f , " ] (" , termErr x′ , ") (" , termErr y′ , ")"
      ]
    f ← Cat.build-expr cat f
    pure (con (quote NbE._↑) (infer-hidden 8 (x′ h∷ y′ h∷ f h∷ tm v∷ [])))
    where open Displayed-terms dtm

  {-# TERMINATING #-}
  build-expr : Displayed-terms → Term → TC Term
  build-expr dtm tm =
    (do
       match-id′ dtm tm
       pure $ con (quote NbE.`id) [])
    <|>
    (do
       f , g , f′ , g′ ← match-∘′ dtm tm
       f ← Cat.build-expr cat f
       g ← Cat.build-expr cat g
       f′ ← build-expr dtm f′
       g′ ← build-expr dtm g′
       pure $ con (quote NbE._`∘_) (infer-hidden 12 $ f h∷ g h∷ f′ v∷ g′ v∷ []))
    <|>
    (do
       f , g , p , f′ ← match-hom[] dtm tm
       f ← Cat.build-expr cat f
       g ← Cat.build-expr cat g
       f′ ← build-expr dtm f′
       pure $ con (quote NbE.`hom[_]_) (infer-hidden 10 $ f h∷ g h∷ p v∷ f′ v∷ []))
    <|>
    (build-neu-expr dtm tm)
    where open Displayed-terms dtm

  invoke-solver : Displayed-terms → Term → Term → Term
  invoke-solver dtm lhs rhs =
    def (quote NbE.solve′) (displayed-args disp (infer-hidden 6 $ lhs v∷ rhs v∷ “refl” v∷ “reindex” v∷ []))
    where
      open Displayed-terms dtm
      “reindex” = def (quote Dr.reindex) (disp v∷ unknown v∷ unknown v∷ [])

  invoke-normaliser : Displayed-terms → Term → Term
  invoke-normaliser dtm tm =
    def (quote NbE.nf′) (displayed-args disp (infer-hidden 5 $ tm v∷ []))
    where open Displayed-terms dtm

  displayed-solver
    : ∀ {o′ ℓ′ o′′ ℓ′′} {B : Precategory o′ ℓ′}
    → Displayed B o′′ ℓ′′
    → TC Simple-solver
  displayed-solver E = do
    dtm ← quote-displayed-terms E
    pure (simple-solver (quote Dr.hom[] ∷ []) (build-expr dtm) (invoke-solver dtm) (invoke-normaliser dtm))

macro
  repr-disp!
    : ∀ {o′ ℓ′ o′′ ℓ′′} {B : Precategory o′ ℓ′}
    → Displayed B o′′ ℓ′′
    → Term → Term → TC ⊤
  repr-disp! E = mk-simple-repr (Reflection.displayed-solver E)

  simpl-disp!
    : ∀ {o′ ℓ′ o′′ ℓ′′} {B : Precategory o′ ℓ′}
    → Displayed B o′′ ℓ′′
    → Term → Term → TC ⊤
  simpl-disp! E = mk-simple-normalise (Reflection.displayed-solver E)

  disp!
    : ∀ {o′ ℓ′ o′′ ℓ′′} {B : Precategory o′ ℓ′}
    → Displayed B o′′ ℓ′′
    → Term → TC ⊤
  disp! E = mk-simple-solver (Reflection.displayed-solver E)

private module Test {o ℓ o′ ℓ′} {B : Precategory o ℓ} (E : Displayed B o′ ℓ′) where
  open Precategory B
  open Displayed E
  open Dr E

  private variable
    x y z : Ob
    x′ y′ z′ : Ob[ x ]
    f g h : Hom x y
    f′ g′ h′ : Hom[ f ] x′ y′


  test : ∀ (f′ : Hom[ f ] y′ z′)
       → f′ ≡ hom[ idl f ] (id′ ∘′ f′)
  test {f = f} f′ = disp! E
