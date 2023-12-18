module Algebra.Group.Solver where

open import 1Lab.Prelude
open import Data.List hiding (lookup)
open import Data.Fin
open import Data.Nat
open import Data.Dec

open import Algebra.Group.Cat.Base
open import Algebra.Group

open import 1Lab.Reflection
open import 1Lab.Reflection.Solver
open import 1Lab.Reflection.Variables

module _ {ℓ} {A : Type ℓ} (G : Group-on A) where
  open Group-on G

  data Expr (n : Nat) : Type ℓ where
    _‶⋆‶_  : (e1 : Expr n) → (e2 : Expr n) → Expr n
    ‶unit‶ : Expr n
    _‶⁻¹‶  : (e : Expr n) → Expr n
    ‶_‶    : Fin n → Expr n

  private variable
    n : Nat

  ⟦_⟧ₑ : Expr n → Vec A n → A
  ⟦ e1 ‶⋆‶ e2 ⟧ₑ ρ = ⟦ e1 ⟧ₑ ρ ⋆ ⟦ e2 ⟧ₑ ρ
  ⟦ ‶unit‶ ⟧ₑ ρ = unit
  ⟦ e ‶⁻¹‶ ⟧ₑ ρ = ⟦ e ⟧ₑ ρ ⁻¹
  ⟦ ‶ x ‶ ⟧ₑ ρ = lookup ρ x

  --------------------------------------------------------------------------------
  -- Values

  data Value (n : Nat) : Type where
    vunit   : Value n
    vmul    : Fin n → Value n → Value n
    vmul⁻¹  : Fin n → Value n → Value n

  ⟦_⟧ᵥ : Value n → Vec A n → A
  ⟦ vunit ⟧ᵥ ρ = unit
  ⟦ vmul x v ⟧ᵥ ρ = lookup ρ x ⋆ ⟦ v ⟧ᵥ ρ
  ⟦ vmul⁻¹ x v ⟧ᵥ ρ = lookup ρ x ⁻¹ ⋆ ⟦ v ⟧ᵥ ρ

  --------------------------------------------------------------------------------
  -- Evaluation

  push : Fin n → Value n → Value n
  push n (vmul⁻¹ n' v) with n ≡? n'
  ... | yes _ = v
  ... | no _  = vmul n (vmul⁻¹ n' v)
  push n v = vmul n v

  push-inv : Fin n → Value n → Value n
  push-inv n (vmul n' v) with n ≡? n'
  ... | yes _ = v
  ... | no _  = vmul⁻¹ n (vmul n' v)
  push-inv n v = vmul⁻¹ n v

  do-mul : Value n → Value n → Value n
  do-mul vunit v2 = v2
  do-mul (vmul x v1) v2 = push x (do-mul v1 v2)
  do-mul (vmul⁻¹ x v1) v2 = push-inv x (do-mul v1 v2)

  do-inv-aux : Value n → Value n → Value n
  do-inv-aux vunit acc = acc
  do-inv-aux (vmul x v) acc = do-inv-aux v (vmul⁻¹ x acc)
  do-inv-aux (vmul⁻¹ x v) acc = do-inv-aux v (vmul x acc)

  do-inv : Value n → Value n
  do-inv v = do-inv-aux v vunit

  eval : Expr n → Value n
  eval (e1 ‶⋆‶ e2) = do-mul (eval e1) (eval e2)
  eval ‶unit‶ = vunit
  eval (e ‶⁻¹‶) = do-inv (eval e)
  eval ‶ x ‶ = vmul x vunit

  --------------------------------------------------------------------------------
  -- Soundness

  push-sound : ∀ x v → (ρ : Vec A n) → ⟦ push x v ⟧ᵥ ρ ≡ lookup ρ x ⋆ ⟦ v ⟧ᵥ ρ
  push-sound x vunit ρ = refl
  push-sound x (vmul x' v) ρ = refl
  push-sound x (vmul⁻¹ x' v) ρ with x ≡? x'
  ... | yes x≡x' =
    ⟦ v ⟧ᵥ ρ                                  ≡˘⟨ idl ⟩
    unit ⋆ ⟦ v ⟧ᵥ ρ                           ≡˘⟨ ap (_⋆ ⟦ v ⟧ᵥ ρ) inverser ⟩
    (lookup ρ x ⋆ (lookup ρ x) ⁻¹) ⋆ ⟦ v ⟧ᵥ ρ ≡⟨ ap (λ ϕ → (lookup ρ x ⋆ (lookup ρ ϕ) ⁻¹) ⋆ ⟦ v ⟧ᵥ ρ) x≡x' ⟩
    (lookup ρ x ⋆ lookup ρ x' ⁻¹) ⋆ ⟦ v ⟧ᵥ ρ  ≡˘⟨ associative ⟩
    lookup ρ x ⋆ (lookup ρ x') ⁻¹ ⋆ ⟦ v ⟧ᵥ ρ ∎
  ... | no _ = refl

  push-inv-sound : ∀ x v → (ρ : Vec A n) → ⟦ push-inv x v ⟧ᵥ ρ ≡ lookup ρ x ⁻¹ ⋆ ⟦ v ⟧ᵥ ρ
  push-inv-sound x vunit ρ = refl
  push-inv-sound x (vmul x' v) ρ with x ≡? x'
  ... | yes x≡x' =
    ⟦ v ⟧ᵥ ρ                                  ≡˘⟨ idl ⟩
    (unit ⋆ ⟦ v ⟧ᵥ ρ)                         ≡˘⟨ ap (_⋆ ⟦ v ⟧ᵥ ρ) inversel ⟩
    ((lookup ρ x) ⁻¹ ⋆ lookup ρ x) ⋆ ⟦ v ⟧ᵥ ρ ≡⟨  ap (λ ϕ → ((lookup ρ x) ⁻¹ ⋆ lookup ρ ϕ) ⋆ ⟦ v ⟧ᵥ ρ) x≡x' ⟩
    (lookup ρ x ⁻¹ ⋆ lookup ρ x') ⋆ ⟦ v ⟧ᵥ ρ  ≡˘⟨ associative ⟩
    (lookup ρ x) ⁻¹ ⋆ lookup ρ x' ⋆ ⟦ v ⟧ᵥ ρ  ∎
  ... | no _     = refl
  push-inv-sound x (vmul⁻¹ x' v) ρ = refl

  do-mul-sound : ∀ v1 v2 → (ρ : Vec A n) → ⟦ do-mul v1 v2 ⟧ᵥ ρ ≡ ⟦ v1 ⟧ᵥ ρ ⋆ ⟦ v2 ⟧ᵥ ρ
  do-mul-sound vunit v2 ρ = sym idl
  do-mul-sound (vmul x v1) v2 ρ =
    ⟦ push x (do-mul v1 v2) ⟧ᵥ ρ         ≡⟨ push-sound x (do-mul v1 v2) ρ ⟩
    lookup ρ x ⋆ ⟦ do-mul v1 v2 ⟧ᵥ ρ     ≡⟨ ap (lookup ρ x ⋆_) (do-mul-sound v1 v2 ρ) ⟩
    lookup ρ x ⋆ ⟦ v1 ⟧ᵥ ρ ⋆ ⟦ v2 ⟧ᵥ ρ   ≡⟨ associative ⟩
    (lookup ρ x ⋆ ⟦ v1 ⟧ᵥ ρ) ⋆ ⟦ v2 ⟧ᵥ ρ ∎
  do-mul-sound (vmul⁻¹ x v1) v2 ρ =
    ⟦ push-inv x (do-mul v1 v2) ⟧ᵥ ρ        ≡⟨ push-inv-sound x (do-mul v1 v2) ρ ⟩
    lookup ρ x ⁻¹ ⋆ ⟦ do-mul v1 v2 ⟧ᵥ ρ     ≡⟨ ap (lookup ρ x ⁻¹ ⋆_) (do-mul-sound v1 v2 ρ) ⟩
    lookup ρ x ⁻¹ ⋆ ⟦ v1 ⟧ᵥ ρ ⋆ ⟦ v2 ⟧ᵥ ρ   ≡⟨ associative ⟩
    (lookup ρ x ⁻¹ ⋆ ⟦ v1 ⟧ᵥ ρ) ⋆ ⟦ v2 ⟧ᵥ ρ ∎

  do-inv-aux-mul   : ∀ v1 x v2 → (ρ : Vec A n) → ⟦ do-inv-aux v1 (vmul x v2) ⟧ᵥ ρ ≡ ⟦ v1 ⟧ᵥ ρ ⁻¹ ⋆ lookup ρ x ⋆ ⟦ v2 ⟧ᵥ ρ
  do-inv-aux-mul⁻¹ : ∀ v1 x v2 → (ρ : Vec A n) → ⟦ do-inv-aux v1 (vmul⁻¹ x v2) ⟧ᵥ ρ ≡ ⟦ v1 ⟧ᵥ ρ ⁻¹ ⋆ lookup ρ x ⁻¹ ⋆ ⟦ v2 ⟧ᵥ ρ

  do-inv-aux-mul vunit x v2 ρ =
    lookup ρ x ⋆ ⟦ v2 ⟧ᵥ ρ                 ≡˘⟨ idl ⟩
    unit ⋆ lookup ρ x ⋆ ⟦ v2 ⟧ᵥ ρ          ≡˘⟨ ap (_⋆ lookup ρ x ⋆ ⟦ v2 ⟧ᵥ ρ) inv-unit ⟩
    unit ⁻¹ ⋆ lookup ρ x ⋆ ⟦ v2 ⟧ᵥ ρ       ∎
  do-inv-aux-mul (vmul x' v1) x v2 ρ =
    ⟦ do-inv-aux v1 (vmul⁻¹ x' (vmul x v2)) ⟧ᵥ ρ                 ≡⟨ do-inv-aux-mul⁻¹ v1 x' (vmul x v2) ρ ⟩
    (⟦ v1 ⟧ᵥ ρ) ⁻¹ ⋆ (lookup ρ x') ⁻¹ ⋆ lookup ρ x ⋆ ⟦ v2 ⟧ᵥ ρ   ≡⟨ associative ⟩
    ((⟦ v1 ⟧ᵥ ρ) ⁻¹ ⋆ (lookup ρ x') ⁻¹) ⋆ lookup ρ x ⋆ ⟦ v2 ⟧ᵥ ρ ≡˘⟨ ap (_⋆ lookup ρ x ⋆ ⟦ v2 ⟧ᵥ ρ) inv-comm ⟩
    (lookup ρ x' ⋆ ⟦ v1 ⟧ᵥ ρ) ⁻¹ ⋆ lookup ρ x ⋆ ⟦ v2 ⟧ᵥ ρ        ∎
  do-inv-aux-mul (vmul⁻¹ x' v1) x v2 ρ =
    ⟦ do-inv-aux v1 (vmul x' (vmul x v2)) ⟧ᵥ ρ                  ≡⟨ do-inv-aux-mul v1 x' (vmul x v2) ρ ⟩
    ⟦ v1 ⟧ᵥ ρ ⁻¹ ⋆ lookup ρ x' ⋆ lookup ρ x ⋆ ⟦ v2 ⟧ᵥ ρ         ≡˘⟨ ap (λ ϕ → ⟦ v1 ⟧ᵥ ρ ⁻¹ ⋆ ϕ ⋆ lookup ρ x ⋆ ⟦ v2 ⟧ᵥ ρ) inv-inv ⟩
    ⟦ v1 ⟧ᵥ ρ ⁻¹ ⋆ lookup ρ x' ⁻¹ ⁻¹ ⋆ lookup ρ x ⋆ ⟦ v2 ⟧ᵥ ρ   ≡⟨ associative ⟩
    (⟦ v1 ⟧ᵥ ρ ⁻¹ ⋆ lookup ρ x' ⁻¹ ⁻¹) ⋆ lookup ρ x ⋆ ⟦ v2 ⟧ᵥ ρ ≡˘⟨ ap (_⋆ lookup ρ x ⋆ ⟦ v2 ⟧ᵥ ρ) inv-comm ⟩
    (lookup ρ x' ⁻¹ ⋆ ⟦ v1 ⟧ᵥ ρ) ⁻¹ ⋆ lookup ρ x ⋆ ⟦ v2 ⟧ᵥ ρ    ∎

  do-inv-aux-mul⁻¹ vunit x v2 ρ =
    lookup ρ x ⁻¹ ⋆ ⟦ v2 ⟧ᵥ ρ           ≡˘⟨ idl ⟩
    unit ⋆ lookup ρ x ⁻¹ ⋆ ⟦ v2 ⟧ᵥ ρ    ≡˘⟨ ap (_⋆ lookup ρ x ⁻¹ ⋆ ⟦ v2 ⟧ᵥ ρ) inv-unit ⟩
    unit ⁻¹ ⋆ lookup ρ x ⁻¹ ⋆ ⟦ v2 ⟧ᵥ ρ ∎
  do-inv-aux-mul⁻¹ (vmul x' v1) x v2 ρ =
    ⟦ do-inv-aux v1 (vmul⁻¹ x' (vmul⁻¹ x v2)) ⟧ᵥ ρ              ≡⟨ do-inv-aux-mul⁻¹ v1 x' (vmul⁻¹ x v2) ρ ⟩
    ⟦ v1 ⟧ᵥ ρ ⁻¹ ⋆ lookup ρ x' ⁻¹ ⋆ lookup ρ x ⁻¹ ⋆ ⟦ v2 ⟧ᵥ ρ   ≡⟨ associative ⟩
    (⟦ v1 ⟧ᵥ ρ ⁻¹ ⋆ lookup ρ x' ⁻¹) ⋆ lookup ρ x ⁻¹ ⋆ ⟦ v2 ⟧ᵥ ρ ≡˘⟨ ap (_⋆ lookup ρ x ⁻¹ ⋆ ⟦ v2 ⟧ᵥ ρ) inv-comm ⟩
    (lookup ρ x' ⋆ ⟦ v1 ⟧ᵥ ρ) ⁻¹ ⋆ lookup ρ x ⁻¹ ⋆ ⟦ v2 ⟧ᵥ ρ    ∎
  do-inv-aux-mul⁻¹ (vmul⁻¹ x' v1) x v2 ρ =
    ⟦ do-inv-aux v1 (vmul x' (vmul⁻¹ x v2)) ⟧ᵥ ρ                   ≡⟨ do-inv-aux-mul v1 x' (vmul⁻¹ x v2) ρ ⟩
    ⟦ v1 ⟧ᵥ ρ ⁻¹ ⋆ lookup ρ x' ⋆ lookup ρ x ⁻¹ ⋆ ⟦ v2 ⟧ᵥ ρ         ≡˘⟨ ap (λ ϕ →  ⟦ v1 ⟧ᵥ ρ ⁻¹ ⋆ ϕ ⋆ lookup ρ x ⁻¹ ⋆ ⟦ v2 ⟧ᵥ ρ) inv-inv ⟩
    ⟦ v1 ⟧ᵥ ρ ⁻¹ ⋆ lookup ρ x' ⁻¹ ⁻¹ ⋆ lookup ρ x ⁻¹ ⋆ ⟦ v2 ⟧ᵥ ρ   ≡⟨ associative ⟩
    (⟦ v1 ⟧ᵥ ρ ⁻¹ ⋆ lookup ρ x' ⁻¹ ⁻¹) ⋆ lookup ρ x ⁻¹ ⋆ ⟦ v2 ⟧ᵥ ρ ≡˘⟨ ap (_⋆ lookup ρ x ⁻¹ ⋆ ⟦ v2 ⟧ᵥ ρ) inv-comm ⟩
    (lookup ρ x' ⁻¹ ⋆ ⟦ v1 ⟧ᵥ ρ) ⁻¹ ⋆ lookup ρ x ⁻¹ ⋆ ⟦ v2 ⟧ᵥ ρ    ∎

  do-inv-sound : ∀ v → (ρ : Vec A n) → ⟦ do-inv v ⟧ᵥ ρ ≡ ⟦ v ⟧ᵥ ρ ⁻¹
  do-inv-sound vunit ρ = sym inv-unit
  do-inv-sound (vmul x v) ρ =
    ⟦ do-inv-aux v (vmul⁻¹ x vunit) ⟧ᵥ ρ  ≡⟨ do-inv-aux-mul⁻¹ v x vunit ρ ⟩
    ⟦ v ⟧ᵥ ρ ⁻¹ ⋆ lookup ρ x ⁻¹ ⋆ unit    ≡⟨ ap (⟦ v ⟧ᵥ ρ ⁻¹ ⋆_) idr ⟩
    ⟦ v ⟧ᵥ ρ ⁻¹ — lookup ρ x              ≡˘⟨ inv-comm ⟩
    (lookup ρ x ⋆ ⟦ v ⟧ᵥ ρ) ⁻¹            ∎
  do-inv-sound (vmul⁻¹ x v) ρ =
    ⟦ do-inv-aux v (vmul x vunit) ⟧ᵥ ρ ≡⟨ do-inv-aux-mul v x vunit ρ ⟩
    ⟦ v ⟧ᵥ ρ ⁻¹ ⋆ lookup ρ x ⋆ unit    ≡⟨ ap (⟦ v ⟧ᵥ ρ ⁻¹ ⋆_) idr ⟩
    ⟦ v ⟧ᵥ ρ ⁻¹ ⋆ lookup ρ x           ≡˘⟨ ap (⟦ v ⟧ᵥ ρ ⁻¹ ⋆_) inv-inv ⟩
    ⟦ v ⟧ᵥ ρ ⁻¹ ⋆ (lookup ρ x ⁻¹) ⁻¹   ≡˘⟨ inv-comm ⟩
    ((lookup ρ x) ⁻¹ ⋆ ⟦ v ⟧ᵥ ρ) ⁻¹    ∎

  eval-sound : ∀ e → (ρ : Vec A n) → ⟦ eval e ⟧ᵥ ρ ≡ ⟦ e ⟧ₑ ρ
  eval-sound (e1 ‶⋆‶ e2) ρ =
    ⟦ do-mul (eval e1) (eval e2) ⟧ᵥ ρ ≡⟨ do-mul-sound (eval e1) (eval e2) ρ ⟩
    ⟦ eval e1 ⟧ᵥ ρ ⋆ ⟦ eval e2 ⟧ᵥ ρ   ≡⟨ ap₂ _⋆_ (eval-sound e1 ρ) (eval-sound e2 ρ) ⟩
    ⟦ e1 ⟧ₑ ρ ⋆ ⟦ e2 ⟧ₑ ρ ∎
  eval-sound ‶unit‶ ρ = refl
  eval-sound (e ‶⁻¹‶) ρ =
    ⟦ do-inv (eval e) ⟧ᵥ ρ ≡⟨ do-inv-sound (eval e) ρ ⟩
    ⟦ eval e ⟧ᵥ ρ ⁻¹       ≡⟨ ap (_⁻¹) (eval-sound e ρ) ⟩
    ⟦ e ⟧ₑ ρ ⁻¹ ∎
  eval-sound ‶ x ‶ ρ = idr

  abstract
    solve : (e1 e2 : Expr n) → (ρ : Vec A n) → ⟦ eval e1 ⟧ᵥ ρ ≡ ⟦ eval e2 ⟧ᵥ ρ → ⟦ e1 ⟧ₑ ρ ≡ ⟦ e2 ⟧ₑ ρ
    solve e1 e2 ρ p = sym (eval-sound e1 ρ) ·· p ·· eval-sound e2 ρ

  expand : (e : Expr n) → Vec A n → A
  expand e ρ = ⟦ eval e ⟧ᵥ ρ

module Reflection where
  pattern is-group-args args = (_ hm∷ _ hm∷ _ hm∷ _ v∷ args)
  pattern group-args args = (_ hm∷ _ hm∷ _ v∷ args)

  pattern “unit” = def (quote is-group.unit) (is-group-args [])
  pattern “⋆” x y = def (quote Group-on._⋆_) (group-args (x v∷ y v∷ []))
  pattern “inverse” x = def (quote is-group.inverse) (is-group-args (x v∷ []))

  mk-group-args : Term → List (Arg Term) → List (Arg Term)
  mk-group-args grp args = unknown h∷ unknown h∷ grp v∷ args

  “solve” : Term → Term → Term → Term → Term
  “solve” grp lhs rhs env = def (quote solve) (mk-group-args grp $ lhs v∷ rhs v∷ env v∷ def (quote refl) [] v∷ [])

  “expand” : Term → Term → Term → Term
  “expand” grp e env = def (quote expand) (mk-group-args grp $ e v∷ env v∷ [])

  build-expr : ∀ {ℓ} {A : Type ℓ} → Variables A → Term → TC (Term × Variables A)
  build-expr vs “unit” =
    pure $ con (quote ‶unit‶) [] , vs
  build-expr vs (“⋆” t1 t2) = do
    e1 , vs ← build-expr vs t1
    e2 , vs ← build-expr vs t2
    pure $ con (quote _‶⋆‶_) (e1 v∷ e2 v∷ []) , vs
  build-expr vs (“inverse” t) = do
    e , vs ← build-expr vs t
    pure $ con (quote _‶⁻¹‶) (e v∷ []) , vs
  build-expr vs tm = do
    (v , vs) ← bind-var vs tm
    pure $ con (quote ‶_‶) (v v∷ []) , vs

  dont-reduce : List Name
  dont-reduce = quote is-group.unit ∷ quote Group-on._⋆_ ∷ quote is-group.inverse ∷ []

  group-solver : ∀ {ℓ} {A : Type ℓ} → Group-on A → TC (VariableSolver A)
  group-solver {A = A} grp = do
    grp-tm ← quoteTC grp
    pure (var-solver {A = A} dont-reduce build-expr (“solve” grp-tm) (“expand” grp-tm))

  repr-macro : ∀ {ℓ} {A : Type ℓ} → Group-on A → Term → Term → TC ⊤
  repr-macro {A = A} grp tm hole = do
    solver ← group-solver grp
    mk-var-repr solver tm

  expand-macro : ∀ {ℓ} {A : Type ℓ} → Group-on A → Term → Term → TC ⊤
  expand-macro {A = A} grp tm hole = do
    solver ← group-solver grp
    mk-var-normalise solver tm hole

  solve-macro : ∀ {ℓ} {A : Type ℓ} → Group-on A → Term → TC ⊤
  solve-macro {A = A} grp hole = do
    solver ← group-solver grp
    mk-var-solver solver hole

macro
  repr-group! : ∀ {ℓ} → Group ℓ → Term → Term → TC ⊤
  repr-group! (_ , grp) tm = Reflection.repr-macro grp tm

  simpl-group! : ∀ {ℓ} → Group ℓ → Term → Term → TC ⊤
  simpl-group! (_ , grp) tm = Reflection.expand-macro grp tm

  group-on! : ∀ {ℓ} {A : Type ℓ} → Group-on A → Term → TC ⊤
  group-on! grp = Reflection.solve-macro grp

  group! : ∀ {ℓ} → Group ℓ → Term → TC ⊤
  group! (_ , grp) = Reflection.solve-macro grp

private module TestGroup-on {ℓ} {A : Type ℓ} (grp : Group-on A) where
  open Group-on grp

  test : ∀ (x y : A) → (x ⋆ inverse y) ⋆ y ⋆ y ≡ x ⋆ (unit ⋆ y)
  test x y = group-on! grp

private module TestGroup {ℓ} (grp : Group ℓ) where
  A : Type ℓ
  A = ⌞ grp ⌟

  open Group-on (snd grp)

  test : ∀ (x y : A) → (x ⋆ inverse y) ⋆ y ⋆ y ≡ x ⋆ (unit ⋆ y)
  test x y = group! grp
