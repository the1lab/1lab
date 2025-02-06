<!--
```agda
open import Cat.Instances.Shape.Terminal
open import Cat.Bi.Instances.Terminal
open import Cat.Bi.Diagram.Monad
open import Cat.Bi.Base
open import Cat.Prelude

import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Bi.Diagram.Monad.Lax {o ℓ ℓ'} (S : Prebicategory o ℓ ℓ') where

private
  open module S = Prebicategory S

```

# Monads as lax functors

[[Monads in a bicategory|monad in]] in a bicategory $\cS$  are equivalent to
[[lax functors|lax functor]] functors from the terminal bicategory to $\cS$.

```agda
lax-functor→monad : Σ[ s ∈ S.Ob ] Monad S s → Lax-functor ⊤Catᵇ S
lax-functor→monad (s , monad) = P where
  open module monad = Monad monad

  open Lax-functor
  open _=>_ renaming (η to nt-η)
  open Functor
  P : Lax-functor ⊤Catᵇ S
  P .P₀ _ = s
  P .P₁ = !Const M
  P .compositor .nt-η _ = μ
  P .compositor .is-natural _ _ _ = S.Hom.elimr (S.compose .F-id) ∙ sym (S.Hom.idl _)
  P .unitor = η
  P .hexagon _ _ _ =
    Hom.id ∘ μ ∘ (μ ◀ M)                ≡⟨ Hom.pulll (Hom.idl _) ⟩
    μ ∘ (μ ◀ M)                         ≡⟨ Hom.intror $ ap (λ nt → nt .nt-η (M , M , M)) associator.invr ⟩
    (μ ∘ μ ◀ M) ∘ (α← M M M ∘ α→ M M M) ≡⟨ cat! (Hom s s) ⟩
    (μ ∘ μ ◀ M ∘ α← M M M) ∘ α→ M M M   ≡˘⟨ Hom.pulll μ-assoc ⟩
    μ ∘ (M ▶ μ) ∘ (α→ M  M  M)          ∎
  P .right-unit _ = Hom.id ∘ μ ∘ M ▶ η  ≡⟨ Hom.idl _ ∙ μ-unitr ⟩ ρ← M ∎
  P .left-unit _ = Hom.id ∘ μ ∘ (η ◀ M) ≡⟨ Hom.idl _ ∙ μ-unitl ⟩ λ← M ∎

monad→lax-functor : Lax-functor ⊤Catᵇ S → Σ[ s ∈ S.Ob ] Monad S s
monad→lax-functor P = (s , record { monad }) where
  open Lax-functor P

  s : S.Ob
  s = P₀ tt
  open _=>_ renaming (η to nt-η)

  module monad where
    M = P₁.F₀ _
    μ = γ→ _ _
    η = unitor
    μ-assoc =
      μ ∘ M ▶ μ                           ≡⟨ (Hom.intror $ ap (λ nt → nt .nt-η (M , M , M)) associator.invl) ⟩
      (μ ∘ M ▶ μ) ∘ (α→ M M M ∘ α← M M M) ≡⟨ cat! (Hom s s) ⟩
      (μ ∘ M ▶ μ ∘ α→ M M M) ∘ α← M M M   ≡˘⟨ hexagon _ _ _ Hom.⟩∘⟨refl ⟩
      (P₁.F₁ _ ∘ μ ∘ μ ◀ M) ∘ α← M M M   ≡⟨ ( P₁.F-id Hom.⟩∘⟨refl) Hom.⟩∘⟨refl  ⟩
      (Hom.id ∘ μ ∘ μ ◀ M) ∘ α← M M M     ≡⟨ cat! (Hom s s) ⟩
      μ ∘ μ ◀ M ∘ α← M M M ∎
    μ-unitr = P₁.introl refl ∙ right-unit _
    μ-unitl = P₁.introl refl ∙ left-unit _
```
