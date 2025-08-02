open import Cat.Diagram.Product.Solver
open import Cat.Diagram.Exponential
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
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
  `_    : ∀ {x y} → Hom x y → Mor (` x) (` y)
  `id   : Mor σ σ
  _`∘_  : Mor σ ρ → Mor τ σ → Mor τ ρ
  `π₁   : Mor (τ `× σ) τ
  `π₂   : Mor (τ `× σ) σ
  _`,_  : Mor τ σ → Mor τ ρ → Mor τ (σ `× ρ)
  app   : Mor ((τ `⇒ σ) `× τ) σ
  lam   : Mor (τ `× σ) ρ → Mor τ (σ `⇒ ρ)

⟦_⟧ᵐ : Mor τ σ → Hom ⟦ τ ⟧ᵗ ⟦ σ ⟧ᵗ
⟦ ` x ⟧ᵐ     = x
⟦ `id ⟧ᵐ     = id
⟦ m `∘ m₁ ⟧ᵐ = ⟦ m ⟧ᵐ ∘ ⟦ m₁ ⟧ᵐ
⟦ `π₁ ⟧ᵐ     = π₁
⟦ `π₂ ⟧ᵐ     = π₂
⟦ m `, m₁ ⟧ᵐ = ⟨ ⟦ m ⟧ᵐ , ⟦ m₁ ⟧ᵐ ⟩
⟦ app ⟧ᵐ     = ev
⟦ lam m ⟧ᵐ   = ƛ ⟦ m ⟧ᵐ

morᵖ : ∀ {h} (e : Mor τ σ) (ρ : Tyᵖ τ Γ h) → Tyᵖ σ Γ (⟦ e ⟧ᵐ ∘ h)
morᵖ (` x) (n , p) = hom {Δ = ∅ , _} (x ∘ π₂) (∅ L., (ne n)) , pullr π₂∘⟨⟩ ∙ ap (x ∘_) p

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

  unit : Id => T
  unit .η x        = ƛ (ev ∘ ⟨ π₂ , π₁ ⟩)
  unit .is-natural x y f = worker {τ = ` x} {σ = ((` y) `⇒ (` S)) `⇒ (` S)}
    (lam (app `∘ (`π₂ `, `π₁)) `∘ (` f))
    (lam (`id `∘ (app `∘ (`π₁ `, (lam (`id `∘ (app `∘ (`π₁ `, ((` f) `∘ `π₂)))) `∘ `π₂))))
      `∘ (lam (app `∘ (`π₂ `, `π₁))))
    refl
