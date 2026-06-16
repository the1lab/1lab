<!--
```agda
open import Cat.Instances.Presheaf.Limits
open import Cat.Diagram.DependentProduct
open import Cat.CartesianClosed.Locally
open import Cat.Diagram.Limit.Finite
open import Cat.Functor.Hom.Yoneda
open import Cat.Functor.Pullback
open import Cat.Instances.Slice
open import Cat.Functor.Base
open import Cat.Functor.Hom
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Instances.Presheaf.DependentProducts
  {o} ℓ (C : Precategory o (o ⊔ ℓ)) where
```

<!--
```agda
private
  module C = Cat.Reasoning C
  module PSh where
    open Cat.Reasoning (PSh (o ⊔ ℓ) C) public
    open Finitely-complete (PSh-finite-limits (o ⊔ ℓ) C) public
  fc = PSh-finite-limits (o ⊔ ℓ) C

  open Functor
  open _=>_
  open /-Obj
  open /-Hom
  open DependentProduct
  open is-dependent-product
```
-->

# Dependent products in presheaf categories

We explicitly describe the construction of dependent products in
presheaf categories. Just as for [exponentials], we use the
[[Yoneda lemma]] to divine the correct answer.

[exponentials]: Cat.Instances.Presheaf.Exponentials.html

Fix a natural transformation $\alpha : F \Rightarrow G$ of presheaves.
Given $X \in \psh(\cC)/F$, we wish to compute
$\prod\limits_\alpha X \in \psh(\cC)/G$.

$$
\begin{align*}
  (\prod_\alpha X)(c)
  &= \hom_{\psh(\cC)}(\yo c, \prod_\alpha X)
  \\ &= \hom_{\psh(\cC)}(\yo c, G)
    \times \hom_{\psh(\cC)/G}(\yo c, \prod_\alpha X)
  \\ &= G(c) \times \hom_{\psh(\cC)/F}(F \times_G \yo c, X)
\end{align*}
$$

This explains how to evaluate $\prod_\alpha X$ at objects. The rest is
straightforward, though the path algebra is tedious.

```agda
module _ {F G : PSh.Ob} (α : PSh.Hom F G) (X : /-Obj {C = PSh (o ⊔ ℓ) C} F) where
  private
    module /F = Cat.Reasoning (Slice (PSh (o ⊔ ℓ) C) F)
    module /G = Cat.Reasoning (Slice (PSh (o ⊔ ℓ) C) G)
    module F = Functor F
    module G = Functor G
    module pb = Functor (Base-change (PSh-pullbacks (o ⊔ ℓ) C) α)

    PShΠ₀ : C.Ob → Type (o ⊔ ℓ)
    PShΠ₀ c = Σ ∣ G.₀ c ∣ λ g → /F.Hom (pb.₀ (cut (yo G g))) X

    abstract
      PShΠ₀-path
        : ∀ {c} {x y : PShΠ₀ c}
        → (p : x .fst ≡ y .fst)
        → x .snd /F.∘ pb.₁ (record { map = PSh.id ; com = PSh.idr _ ∙ ap (yo G) p })
          ≡ y .snd
        → x ≡ y
      PShΠ₀-path {c} {g , β} {g′ , β′} p q = J
        (λ g′ p →
          ∀ {β′}
          → β /F.∘ pb.₁ (record { map = PSh.id ; com = PSh.idr _ ∙ ap (yo G) p }) ≡ β′
          → (g , β) ≡ (g′ , β′))
        (λ p → ap (g ,_) (/F.intror (ap pb.₁ (/-Hom-path refl) ∙ pb.F-id) ∙ p))
        p
        q

    PShΠ-Π : /G.Ob
    PShΠ-Π .dom .F₀ c = el! (PShΠ₀ c)
    PShΠ-Π .dom .F₁ f (g , β) =
      G.₁ f g , (β /F.∘ pb.₁ (record { map = よ C .F₁ f ; com = yo-naturalr }))
    PShΠ-Π .dom .F-id = funext λ (g , β) →
      PShΠ₀-path (happly G.F-id g) $ /F.cancelr $ /-Hom-path
      $ Nat-path λ _ → funext λ _ → Σ-pathp (C.idl _) (Σ-prop-pathp! refl)
    PShΠ-Π .dom .F-∘ f₁ f₂ = funext λ (g , β) →
      PShΠ₀-path (happly (G.F-∘ _ _) g) $ /F.extendr
      $ sym (pb.F-∘ _ _)
      ∙∙ ap pb.₁ (/-Hom-path (PSh.idr _ ∙ よ C .F-∘ _ _))
      ∙∙ pb.F-∘ _ _
    PShΠ-Π .map .η _ (g , _) = g
    PShΠ-Π .map .is-natural _ _ _ = refl

    PShΠ-ev : /F.Hom (pb.₀ PShΠ-Π) X
    PShΠ-ev .map .η c ((g , β) , f , p) = β .map .η c (C.id , f , happly G.F-id g ∙ p)
    PShΠ-ev .map .is-natural c c′ h = funext λ ((_ , β) , _) →
      ap (map β .η c′) (Σ-pathp C.id-comm (Σ-prop-pathp! refl))
      ∙ happly (β .map .is-natural c c′ h) _
    PShΠ-ev .com = Nat-path λ c → funext λ ((_ , β) , _) → happly (β .com ηₚ c) _

    PShΠ-ƛ : ∀ {Γ : /G.Ob} → /F.Hom (pb.₀ Γ) X → /G.Hom Γ PShΠ-Π
    PShΠ-ƛ {Γ} m .map .η c γ =
      Γ .map .η c γ , m /F.∘ pb.₁ (record { map = yo (dom Γ) γ ; com = yo-naturall })
    PShΠ-ƛ {Γ} m .map .is-natural c c′ h = funext λ γ →
      PShΠ₀-path (happly (map Γ .is-natural c c′ h) γ)
      $ /F.pullr (sym (pb.F-∘ _ _))
      ∙∙ ap (λ x → m /F.∘ pb.F₁ x) (/-Hom-path (PSh.idr _ ∙ sym yo-naturalr))
      ∙∙ /F.pushr (pb.F-∘ _ _)
    PShΠ-ƛ {Γ} m .com = Nat-path λ _ → refl
```

<!--
```agda
    abstract
      PShΠ-ƛ-commutes
        : ∀ {Γ} (m : /F.Hom (pb.₀ Γ) X) → PShΠ-ev /F.∘ pb.₁ (PShΠ-ƛ m) ≡ m
      PShΠ-ƛ-commutes {Γ} m = /-Hom-path $ Nat-path λ c → funext λ (γ , f , p) →
        ap (map m .η c) (Σ-pathp (happly (dom Γ .F-id) γ) (Σ-prop-pathp! refl))

      PShΠ-ƛ-unique
        : ∀ {Γ m} (m' : /G.Hom Γ PShΠ-Π) → PShΠ-ev /F.∘ pb.₁ m' ≡ m → m' ≡ PShΠ-ƛ m
      PShΠ-ƛ-unique {Γ} m′ p = /-Hom-path $ Nat-path λ c → funext λ γ →
        PShΠ₀-path (ap (λ x → x .η c γ) (m′ .com))
        $ (/-Hom-path $ Nat-path λ c′ → funext λ (h , f , q) →
          _ ≡⟨ ap (map (map m′ .η c γ .snd) .η c′) (Σ-pathp (sym (C.idr h)) (Σ-prop-pathp! refl)) ⟩
          _ ≡⟨(λ i → m′ .map .is-natural c c′ h (~ i) γ .snd .map .η c′ (C.id , f , (λ j → G.₁ C.id (m′ .map .is-natural c c′ h (~ i ∧ ~ j) γ .fst)) ∙ happly G.F-id _ ∙ ap fst (happly (m′ .map .is-natural c c′ h) γ) ∙ ap (G.₁ h) (λ i → m′ .com i .η c γ) ∙ q))⟩
          _ ≡⟨ ap (λ x → map (map m′ .η c′ (F₁ (dom Γ) h γ) .snd) .η c′ (C.id , f , x)) prop! ⟩
          _ ∎)
        ∙∙ /F.refl⟩∘⟨ pb.F-∘ _ _
        ∙∙ /F.pulll p
```
-->

```agda
    PShΠ-is-Π : is-dependent-product (PSh (o ⊔ ℓ) C) fc PShΠ-Π PShΠ-ev
    PShΠ-is-Π .ƛ = PShΠ-ƛ
    PShΠ-is-Π .commutes = PShΠ-ƛ-commutes
    PShΠ-is-Π .unique = PShΠ-ƛ-unique

  PShΠ : DependentProduct (PSh (o ⊔ ℓ) C) fc α X
  PShΠ .Π = PShΠ-Π
  PShΠ .ev = PShΠ-ev
  PShΠ .has-is-Π = PShΠ-is-Π
```

We conclude that presheaf categories are locally cartesian closed.

```agda
PSh-lccc : Locally-cartesian-closed (PSh (o ⊔ ℓ) C)
PSh-lccc = dependent-products→lccc (PSh (o ⊔ ℓ) C) fc PShΠ
```
