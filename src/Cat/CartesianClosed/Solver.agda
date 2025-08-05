open import Cat.Diagram.Exponential
open import Cat.Functor.Adjoint.Hom
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Functor.Adjoint
open import Cat.Cartesian
open import Cat.Prelude

import Cat.CartesianClosed.Lambda as L
import Cat.Functor.Bifunctor as Bifunctor
import Cat.Reasoning

module Cat.CartesianClosed.Solver
  {o ℓ} {C : Precategory o ℓ} (cart : Cartesian-category C)
  (cc : Cartesian-closed C cart)
  where

open Cartesian-category cart
open Cartesian-closed cc
open L C cart cc

private variable
  Γ Δ Θ : Cx
  τ σ ρ : Ty

data Mor : Ty → Ty → Type (o ⊔ ℓ) where
  `_   : ∀ {x y} → Hom ⟦ x ⟧ᵗ ⟦ y ⟧ᵗ → Mor x y
  `id  : Mor σ σ
  _`∘_ : Mor σ ρ → Mor τ σ → Mor τ ρ
  `π₁  : Mor (τ `× σ) τ
  `π₂  : Mor (τ `× σ) σ
  _`,_ : Mor τ σ → Mor τ ρ → Mor τ (σ `× ρ)
  `ev  : Mor ((τ `⇒ σ) `× τ) σ
  `!   : Mor τ `⊤
  `ƛ   : Mor (τ `× σ) ρ → Mor τ (σ `⇒ ρ)

infixr 20 _`∘_
infixr 19 _`,_
infix 21 `_

⟦_⟧ᵐ : Mor τ σ → Hom ⟦ τ ⟧ᵗ ⟦ σ ⟧ᵗ
⟦ ` x     ⟧ᵐ = x
⟦ `id     ⟧ᵐ = id
⟦ m `∘ m₁ ⟧ᵐ = ⟦ m ⟧ᵐ ∘ ⟦ m₁ ⟧ᵐ
⟦ `π₁     ⟧ᵐ = π₁
⟦ `π₂     ⟧ᵐ = π₂
⟦ m `, m₁ ⟧ᵐ = ⟨ ⟦ m ⟧ᵐ , ⟦ m₁ ⟧ᵐ ⟩
⟦ `ev     ⟧ᵐ = ev
⟦ `ƛ m    ⟧ᵐ = ƛ ⟦ m ⟧ᵐ
⟦ `!      ⟧ᵐ = !

private
  tickᵖ : ∀ {x y h} (m : Hom ⟦ x ⟧ᵗ ⟦ y ⟧ᵗ) → Tyᵖ x Γ h → Tyᵖ y Γ (m ∘ h)

  tickᵖ {y = τ L.`× σ} m a =
      tyᵖ⟨ pullr refl ⟩ (tickᵖ (π₁ ∘ m) a)
    , tyᵖ⟨ pullr refl ⟩ (tickᵖ (π₂ ∘ m) a)

  tickᵖ {x = x} {y = τ L.`⇒ σ} m a ρ y =
    tyᵖ⟨ pullr (Product.unique (products _ _) (pulll π₁∘⟨⟩ ∙ extendr π₁∘⟨⟩) (pulll π₂∘⟨⟩ ∙ π₂∘⟨⟩)) ⟩
    (tickᵖ {x = x `× τ} (ev ∘ ⟨ m ∘ π₁ , π₂ ⟩)
      (tyᵖ⟨ sym π₁∘⟨⟩ ⟩ (ren-tyᵖ ρ a) , tyᵖ⟨ sym π₂∘⟨⟩ ⟩ y))

  tickᵖ {x = x} {y = L.` τ} m a =
    hom {Δ = ∅ , x} (m ∘ π₂) (∅ , reifyᵖ a) ,
    pullr π₂∘⟨⟩ ∙ ap (m ∘_) (reifyᵖ-correct a)

  tickᵖ {x = x} {y = L.`⊤} m a = lift tt

  morᵖ : ∀ {h} (e : Mor τ σ) (ρ : Tyᵖ τ Γ h) → Tyᵖ σ Γ (⟦ e ⟧ᵐ ∘ h)
  morᵖ (` x) = tickᵖ x

  morᵖ `id         ρ = tyᵖ⟨ introl refl ⟩ ρ
  morᵖ (f `∘ g)    ρ = tyᵖ⟨ pulll refl ⟩ (morᵖ f (morᵖ g ρ))

  morᵖ `π₁      ρ = ρ .fst
  morᵖ `π₂      ρ = ρ .snd
  morᵖ (e `, f) ρ = tyᵖ⟨ sym (pulll π₁∘⟨⟩) ⟩ (morᵖ e ρ) , tyᵖ⟨ sym (pulll π₂∘⟨⟩) ⟩ (morᵖ f ρ)

  morᵖ `!       ρ = lift tt

  morᵖ `ev (f , x) = tyᵖ⟨ ap (ev ∘_) (sym (Product.unique (products _ _) (intror refl) refl)) ⟩ (f stop x)
  morᵖ {h = h} (`ƛ e) t r {h'} a = tyᵖ⟨ sym p ⟩ (morᵖ e (tyᵖ⟨ sym π₁∘⟨⟩ ⟩ (ren-tyᵖ r t) , tyᵖ⟨ sym π₂∘⟨⟩ ⟩ a)) where
    p =
      ev ∘ ⟨ ((ƛ ⟦ e ⟧ᵐ) ∘ h) ∘ ⟦ r ⟧ʳ , h' ⟩
        ≡⟨ ap (ev ∘_) (sym (Product.unique (products _ _) (pulll π₁∘⟨⟩ ∙ pullr π₁∘⟨⟩ ∙ pulll refl) (pulll π₂∘⟨⟩ ∙ pullr π₂∘⟨⟩ ∙ idl _))) ⟩
      ev ∘ (ƛ ⟦ e ⟧ᵐ ⊗₁ id) ∘ ⟨ h ∘ ⟦ r ⟧ʳ , h' ⟩
        ≡⟨ pulll (commutes _) ⟩
      ⟦ e ⟧ᵐ ∘ ⟨ h ∘ ⟦ r ⟧ʳ , h' ⟩
        ∎

  mor-nf : Mor τ σ → Nf (∅ , τ) σ
  mor-nf m = reifyᵖ (morᵖ m (reflectᵖ (var stop)))

  mor-nf-sound : (m : Mor τ σ) → ⟦ m ⟧ᵐ ≡ ⟦ mor-nf m ⟧ₙ ∘ ⟨ ! , id ⟩
  mor-nf-sound m = sym (pushl (reifyᵖ-correct (morᵖ m (reflectᵖ (var stop)))) ∙ elimr π₂∘⟨⟩)

solve : (m m' : Mor τ σ) → mor-nf m ≡ mor-nf m' → ⟦ m ⟧ᵐ ≡ ⟦ m' ⟧ᵐ
solve m m' p = mor-nf-sound m ∙∙ ap₂ _∘_ (ap ⟦_⟧ₙ p) refl ∙∙ sym (mor-nf-sound m')

module _ (S : Ob) where
  T : Functor C C
  T = Bifunctor.Left ([-,-] C cart cc) S F∘ opFʳ (Bifunctor.Left ([-,-] C cart cc) S)

  open _=>_

  t1 : ∀ {X Y Z} → (f : Hom X (Y ⊗₀ Z)) → f ≡ ⟨ π₁ ∘ f , π₂ ∘ f ⟩
  t1 {X} {Y} {Z} f = let `f = ` f in solve {τ = ` X} {σ = (` Y) `× (` Z)} `f (`π₁ `∘ `f `, `π₂ `∘ `f) refl

  t2 : ∀ {X Y Z} → (f : Hom X [ Y , Z ]) → f ≡ ƛ (unlambda f)
  t2 {X} {Y} {Z} f = solve {τ = ` X} {σ = (` Y) `⇒ (` Z)} (` f) (`ƛ (`ev `∘ (` f `∘ `π₁ `, `id `∘ `π₂))) refl

  t3 : ∀ {X Y Z} (f g : Hom (X ⊗₀ [ Y , Z ]) top) → f ≡ g
  t3 {X} {Y} {Z} f g = solve {τ = (` X) `× ((` Y) `⇒ (` Z))} {σ = `⊤} (` f) (` g) refl

  adj : opFʳ (Bifunctor.Left ([-,-] C cart cc) S) ⊣ Bifunctor.Left ([-,-] C cart cc) S
  adj = hom-iso→adjoints tr eqv nat where
    `tr : ∀ {x y} → Mor y (x `⇒ (` S)) → Mor x (y `⇒ (` S))
    `tr f = `ƛ (`ev `∘ (f `∘ `π₂ `, `π₁ ))

    tr : ∀ {x y} → Hom y [ x , S ] → Hom x [ y , S ]
    tr {x} {y} f = ⟦ `tr {x = ` x} {y = ` y} (` f) ⟧ᵐ

    eqv : ∀ {x y} → is-equiv (tr {x} {y})
    eqv {x} {y} = is-iso→is-equiv record where
      from   = tr
      linv m = solve (`tr (`tr {x = ` x} {` y} (` m))) (` m) refl
      rinv m = solve (`tr (`tr {x = ` y} {` x} (` m))) (` m) refl

    nat : hom-iso-natural
      {L = opFʳ (Bifunctor.Left ([-,-] C cart cc) S)}
      {R = Bifunctor.Left ([-,-] C cart cc) S}
      tr
    nat {a} {b} {c} {d} g h x =
      let
        `h : Mor (` c) (` d) ; `h = ` h
        `g : Mor (` b) (` a) ; `g = ` g
      in solve
        (`tr ((`ƛ (`id `∘ `ev `∘ (`π₁ `, `h `∘ `π₂)) `∘ ` x) `∘ `g))
        (`ƛ (`id `∘ `ev `∘ (`π₁ `, `g `∘ `π₂)) `∘ `tr (` x) `∘ `h)
        refl
