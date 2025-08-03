open import Cat.Diagram.Product.Solver
open import Cat.Diagram.Exponential
open import Cat.Functor.Adjoint.Hom
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Functor.Adjoint
open import Cat.Prelude

import Cat.CartesianClosed.Lambda as L
import Cat.Functor.Bifunctor as Bifunctor
import Cat.Reasoning

module Cat.CartesianClosed.Solver
  {o ℓ}
  (C : Precategory o ℓ) (fp : has-products C) (term : Terminal C)
  (cc : Cartesian-closed C fp term)
  where

open Binary-products C fp
open Cartesian-closed cc
open Cat.Reasoning C
open L C fp term cc
open Terminal term

private variable
  Γ Δ Θ : Cx
  τ σ ρ : Ty

data Mor : Ty → Ty → Type (o ⊔ ℓ) where
  `_    : ∀ {x y} → Hom ⟦ x ⟧ᵗ ⟦ y ⟧ᵗ → Mor x y
  `id   : Mor σ σ
  _`∘_  : Mor σ ρ → Mor τ σ → Mor τ ρ
  `π₁   : Mor (τ `× σ) τ
  `π₂   : Mor (τ `× σ) σ
  _`,_  : Mor τ σ → Mor τ ρ → Mor τ (σ `× ρ)
  app   : Mor ((τ `⇒ σ) `× τ) σ
  lam   : Mor (τ `× σ) ρ → Mor τ (σ `⇒ ρ)

infixr 20 _`∘_
infixr 19 _`,_
infix 21 `_

⟦_⟧ᵐ : Mor τ σ → Hom ⟦ τ ⟧ᵗ ⟦ σ ⟧ᵗ
⟦ ` x ⟧ᵐ     = x
⟦ `id ⟧ᵐ     = id
⟦ m `∘ m₁ ⟧ᵐ = ⟦ m ⟧ᵐ ∘ ⟦ m₁ ⟧ᵐ
⟦ `π₁ ⟧ᵐ     = π₁
⟦ `π₂ ⟧ᵐ     = π₂
⟦ m `, m₁ ⟧ᵐ = ⟨ ⟦ m ⟧ᵐ , ⟦ m₁ ⟧ᵐ ⟩
⟦ app ⟧ᵐ     = ev
⟦ lam m ⟧ᵐ   = ƛ ⟦ m ⟧ᵐ

tickᵖ : ∀ {x y h} (m : Hom ⟦ x ⟧ᵗ ⟦ y ⟧ᵗ) → Tyᵖ x Γ h → Tyᵖ y Γ (m ∘ h)

tickᵖ {y = τ L.`× σ} m a = tyᵖ⟨ pullr refl ⟩ (tickᵖ (π₁ ∘ m) a) , tyᵖ⟨ pullr refl ⟩ (tickᵖ (π₂ ∘ m) a)

tickᵖ {x = x} {y = τ L.`⇒ σ} m a ρ y = tyᵖ⟨ pullr (Product.unique (fp _ _) (pulll π₁∘⟨⟩ ∙ extendr π₁∘⟨⟩) (pulll π₂∘⟨⟩ ∙ π₂∘⟨⟩)) ⟩
  (tickᵖ {x = x `× τ} (ev ∘ ⟨ m ∘ π₁ , π₂ ⟩) (tyᵖ⟨ sym π₁∘⟨⟩ ⟩ (ren-tyᵖ ρ a) , tyᵖ⟨ sym π₂∘⟨⟩ ⟩ y))

tickᵖ {x = x} {y = L.` τ}    m a = hom {Δ = ∅ , x} (m ∘ π₂) (∅ , reifyᵖ a) , pullr π₂∘⟨⟩ ∙ ap (m ∘_) (reifyᵖ-correct a)

morᵖ : ∀ {h} (e : Mor τ σ) (ρ : Tyᵖ τ Γ h) → Tyᵖ σ Γ (⟦ e ⟧ᵐ ∘ h)
morᵖ (` x) = tickᵖ x

morᵖ `id         ρ = tyᵖ⟨ introl refl ⟩ ρ
morᵖ (f `∘ g)    ρ = tyᵖ⟨ pulll refl ⟩ (morᵖ f (morᵖ g ρ))

morᵖ `π₁ (x , y) = x
morᵖ `π₂ (x , y) = y

morᵖ (e `, f) ρ = tyᵖ⟨ sym (pulll π₁∘⟨⟩) ⟩ (morᵖ e ρ) , tyᵖ⟨ sym (pulll π₂∘⟨⟩) ⟩ (morᵖ f ρ)
morᵖ app (f , x) = tyᵖ⟨ ap (ev ∘_) (sym (Product.unique (fp _ _) (intror refl) refl)) ⟩ (f stop x)
morᵖ {h = h} (lam e) t r {h'} a = tyᵖ⟨ sym p ⟩ (morᵖ e (tyᵖ⟨ sym π₁∘⟨⟩ ⟩ (ren-tyᵖ r t) , tyᵖ⟨ sym π₂∘⟨⟩ ⟩ a)) where
  p =
    ev ∘ ⟨ ((ƛ ⟦ e ⟧ᵐ) ∘ h) ∘ ⟦ r ⟧ʳ , h' ⟩
      ≡⟨ ap (ev ∘_) (sym (Product.unique (fp _ _) (pulll π₁∘⟨⟩ ∙ pullr π₁∘⟨⟩ ∙ pulll refl) (pulll π₂∘⟨⟩ ∙ pullr π₂∘⟨⟩ ∙ idl _))) ⟩
    ev ∘ (ƛ ⟦ e ⟧ᵐ ⊗₁ id) ∘ ⟨ h ∘ ⟦ r ⟧ʳ , h' ⟩
      ≡⟨ pulll (commutes _) ⟩
    ⟦ e ⟧ᵐ ∘ ⟨ h ∘ ⟦ r ⟧ʳ , h' ⟩
      ∎

mor-nf : Mor τ σ → Nf (∅ , τ) σ
mor-nf m = reifyᵖ (morᵖ m (reflectᵖ (var stop)))

mor-nf-sound : (m : Mor τ σ) → ⟦ m ⟧ᵐ ≡ ⟦ mor-nf m ⟧ₙ ∘ ⟨ ! , id ⟩
mor-nf-sound m = sym (pushl (reifyᵖ-correct (morᵖ m (reflectᵖ (var stop)))) ∙ elimr π₂∘⟨⟩)

worker : (m m' : Mor τ σ) → mor-nf m ≡ mor-nf m' → ⟦ m ⟧ᵐ ≡ ⟦ m' ⟧ᵐ
worker m m' p = mor-nf-sound m ∙∙ ap₂ _∘_ (ap ⟦_⟧ₙ p) refl ∙∙ sym (mor-nf-sound m')

module _ (S : Ob) where
  T : Functor C C
  T = Bifunctor.Left ([-,-] C fp term cc) S F∘ opFʳ (Bifunctor.Left ([-,-] C fp term cc) S)

  open _=>_

  test : ∀ {X Y Z} → (f : Hom X (Y ⊗₀ Z)) → f ≡ ⟨ π₁ ∘ f , π₂ ∘ f ⟩
  test {X} {Y} {Z} f = let `f = ` f in worker {τ = ` X} {σ = (` Y) `× (` Z)} `f (`π₁ `∘ `f `, `π₂ `∘ `f) refl

  test' : ∀ {X Y Z} → (f : Hom X (Exp.B^A Y Z)) → f ≡ ƛ (unlambda f)
  test' {X} {Y} {Z} f = worker {τ = ` X} {σ = (` Y) `⇒ (` Z)} (` f) (lam (app `∘ (` f `∘ `π₁ `, `id `∘ `π₂))) refl

  adj : opFʳ (Bifunctor.Left ([-,-] C fp term cc) S) ⊣ Bifunctor.Left ([-,-] C fp term cc) S
  adj = hom-iso→adjoints tr a λ {a} {b} {c} {d} g h x →
    let
      `h : Mor (` c) (` d)
      `h = ` h
      `g : Mor (` b) (` a)
      `g = ` g
    in
    worker
      (`tr ((lam (`id `∘ app `∘ (`π₁ `, `h `∘ `π₂)) `∘ ` x) `∘ `g))
      (lam (`id `∘ app `∘ (`π₁ `, `g `∘ `π₂)) `∘ `tr (` x) `∘ `h)
      refl
    where
    `tr : ∀ {x y} → Mor y (x `⇒ (` S)) → Mor x (y `⇒ (` S))
    `tr f = lam (app `∘ (f `∘ `π₂ `, `π₁ ))

    tr : ∀ {x y} → Hom y (Exp.B^A x S) → Hom x (Exp.B^A y S)
    tr {x} {y} f = ⟦ `tr {x = ` x} {y = ` y} (` f) ⟧ᵐ

    a : ∀ {x y} → is-equiv (tr {x} {y})
    a {x} {y} = is-iso→is-equiv record where
      from   = tr
      linv m = worker (`tr (`tr {x = ` x} {` y} (` m))) (` m) refl
      rinv m = worker (`tr (`tr {x = ` y} {` x} (` m))) (` m) refl

    -- b : hom-iso-natural tr
    -- b = {!   !}

  -- unit : Id => T
  -- unit .η x        = ƛ (ev ∘ ⟨ π₂ , π₁ ⟩)
  -- unit .is-natural x y f = worker {τ = ` x} {σ = ((` y) `⇒ (` S)) `⇒ (` S)}
  --   (lam (app `∘ (`π₂ `, `π₁)) `∘ (` f))
  --   (lam (`id `∘ (app `∘ (`π₁ `, (lam (`id `∘ (app `∘ (`π₁ `, ((` f) `∘ `π₂)))) `∘ `π₂))))
  --     `∘ (lam (app `∘ (`π₂ `, `π₁))))
  --   {!   !}
