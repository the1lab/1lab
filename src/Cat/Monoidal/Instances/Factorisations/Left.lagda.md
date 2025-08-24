<!--
```agda
open import Cat.Displayed.Instances.Factorisations
open import Cat.Morphism.Factorisation.Algebraic
open import Cat.Instances.Shape.Interval
open import Cat.Displayed.Section
open import Cat.Diagram.Comonad
open import Cat.Morphism.Lifts
open import Cat.Prelude

import Cat.Monoidal.Instances.Factorisations as Ffm
import Cat.Functor.Bifunctor as Bi
import Cat.Reasoning

open is-comonad hiding (δ)
open Lwfs-on hiding (δ)
open Section
open Functor
open _=>s_
open _=>_
```
-->

```agda
module Cat.Monoidal.Instances.Factorisations.Left
  {o ℓ} (C : Precategory o ℓ) where
```

<!--
```agda
private module Arr = Cat.Reasoning (Arr C)
open Cat.Reasoning C
open Ffm C
```
-->

# Monoidal structure on lwfs

The [[monoidal category]] [structure] on [[functorial factorisations]]
lifts to [[left weak factorisation structures]].

[structure]: Cat.Monoidal.Instances.Factorisations.html

The comultiplication on the tensor unit is trivial.

```agda
Lwfs-on-unit : Lwfs-on Ff-unit
Lwfs-on-unit .L-δ .η (X , Y , f) = Arr.id
Lwfs-on-unit .L-δ .is-natural x y f = ext (id-comm-sym ,ₚ id-comm-sym)
Lwfs-on-unit .L-comonad .δ-unitl = ext (idl id ,ₚ idl id)
Lwfs-on-unit .L-comonad .δ-unitr = ext (idl id ,ₚ idl id)
Lwfs-on-unit .L-comonad .δ-assoc = ext refl
```

The comultiplication on tensors is where most of the work goes.

```agda
module _ {F G : Factorisation C} (Fl : Lwfs-on F) (Gl : Lwfs-on G) where
```

<!--
```agda
  private
    module FG = Factorisation (F ⊗ᶠᶠ G)
    module F = Lwfs Fl
    module G = Lwfs Gl
    open F renaming (ρ→ to ρᶠ ; λ→ to λᶠ) using ()
    open G renaming (ρ→ to ρᵍ ; λ→ to λᵍ) using ()
```
-->

```agda
    λλ : ∀ {x y} (f : Hom x y) → Hom x (G.Mid (ρᶠ f))
    λλ f = λᵍ (ρᶠ f) ∘ λᶠ f

    λ→λλ : ∀ {x y} (f : Hom x y) → Homᵃ C (λᶠ f) (λλ f)
    λ→λλ f .top = id
    λ→λλ f .bot = λᵍ (ρᶠ f)
    λ→λλ f .com = elimr refl
```

```agda
    δ-sq : ∀ {x y} (f : Hom x y) → Homᵃ C (λᵍ (ρᶠ f)) (ρᶠ (λλ f))
    δ-sq f using (llift , α , β) ← F.lift-λρ (λ→λλ f) = record
      { top = llift
      ; bot = id
      ; com = β ∙ introl refl
      }
```

The component of the comultiplication $\delta$ at a map $X \xto{f} Y$ is
given by the dashed arrow $l_2$ in the diagram below. The auxiliary
arrow $l_1$ serves primarily to establish that everything necessary
commutes. Note that the ellipse with faces $\rho_{\rho_{\dots}}$ and
$l_2$ is only the identity on $G(\rho_f)$, and this gives one of the
counit laws for $\delta$.

~~~{.quiver}
\[\begin{tikzcd}[ampersand replacement=\&]
  X \\
  \\
  {F(f)} \&\& {F(\lambda^2_f)} \\
  \\
  {G(\rho_f)} \&\&\&\& {G(\rho_{\lambda^2_f})} \\
  \\
  Y
  \arrow["{\lambda_f}", from=1-1, to=3-1]
  \arrow["{\lambda_{\lambda^2_f}}", from=1-1, to=3-3]
  \arrow["f"', curve={height=48pt}, dotted, from=1-1, to=7-1]
  \arrow["{l_1}"', dashed, from=3-1, to=3-3]
  \arrow["{\lambda_{\rho_f}}", from=3-1, to=5-1]
  \arrow["{\rho_{\lambda^2_f}}"{description}, dotted, from=3-3, to=5-1]
  \arrow["{\lambda_{\rho_{\lambda^2_f}}}"{description}, from=3-3, to=5-5]
  \arrow[""{name=0, anchor=center, inner sep=0}, "{l_2}"{description}, curve={height=18pt}, dashed, from=5-1, to=5-5]
  \arrow["{\rho_{\lambda_f}}", dotted, from=5-1, to=7-1]
  \arrow[""{name=1, anchor=center, inner sep=0}, "{\rho_{\rho_{\lambda^2_f}}}"{description}, curve={height=18pt}, from=5-5, to=5-1]
\end{tikzcd}\]
~~~

```agda
    lδ : FG.L => (FG.L F∘ FG.L)
    lδ .η (X , Y , f) = record where
      (l1  , α , _) = F.lift-λρ (λ→λλ f)
      (bot , β , _) = G.lift-λρ (δ-sq f)

      top = id
      com : (λᵍ (ρᶠ (λλ f)) ∘ λᶠ (λλ f)) ∘ id ≡ bot ∘ λᵍ (ρᶠ f) ∘ λᶠ f
      com = sym (pulll β ∙∙ pullr α ∙∙ pulll refl)
```

<!--
```agda
    lδ .is-natural x y f = ext $ id-comm-sym ,ₚ
        pullr (sym (G.δ-nat _))
      ∙ extendl (G.weave (ext
          ( pullr (sym (F.δ-nat _))
          ∙ extendl (F.weave (ext (id-comm-sym ,ₚ G .S₁ _ .sq₀)))
          ,ₚ id-comm-sym)))
```
-->

As indicated, we can obtain one of the counit laws by pondering the orb
contained in the diagram, and the other counit law pops up by
calculating until we can apply $F$ and $G$'s unit laws in turn. The only
lengthy calculation is associativity, but the idea is the same:
calculate to expose opportunities to apply the associativity of both
factors.

```agda
  Lwfs-on-tensor : Lwfs-on (F ⊗ᶠᶠ G)
  Lwfs-on-tensor .L-δ = lδ
  Lwfs-on-tensor .L-comonad .δ-assoc {x , y , f} = ext $ refl ,ₚ sym p1 where
    p0 =
      F.map (λ→λλ (λλ f)) ∘ F.δ (λλ f) ∘ F.map (λ→λλ f) ∘ F.δ f
        ≡⟨ ap₂ _∘_ refl (pulll (sym (F.δ-nat _)) ∙ pullr (sym F.δ-assoc)) ⟩
      F.map (λ→λλ (λλ f)) ∘ F.map (F.L₁ (λ→λλ f)) ∘ F.map (F.δˢ f) ∘ F.δ f
        ≡⟨ pulll (F.collapse refl) ⟩
      F.map (λ→λλ (λλ f) Arr.∘ F.L₁ (λ→λλ f)) ∘ F.map (F.δˢ f) ∘ F.δ f
        ≡⟨ extendl (F.weave (ext (elimr F.δ-top ,ₚ pullr refl ∙ sym (G.lift-λρ (δ-sq f) .snd .fst)))) ⟩
      F.map (lδ .η (_ , _ , f)) ∘ F.map (λ→λλ f) ∘ F.δ f
        ∎

    p1 =
      (G.map (δ-sq (λλ f)) ∘ G.δ (ρᶠ (λλ f))) ∘ G.map (δ-sq f) ∘ G.δ (ρᶠ f)
        ≡⟨ pullr (extendl (sym (G.δ-nat _))) ⟩
      G.map (δ-sq (λλ f)) ∘ G.map (G.L₁ (δ-sq f)) ∘ G.δ (λᵍ (ρᶠ f)) ∘ G.δ (ρᶠ f)
        ≡⟨ ap₂ _∘_ refl (ap₂ _∘_ refl (sym G.δ-assoc)) ⟩
      G.map (δ-sq (λλ f)) ∘ G.map (G.L₁ (δ-sq f)) ∘ G.map (G.δˢ (ρᶠ f)) ∘ G.δ (ρᶠ f)
        ≡⟨ ap₂ _∘_ refl (pulll (G.collapse refl)) ⟩
      G.map (δ-sq (λλ f)) ∘ G.map (G.L₁ (δ-sq f) Arr.∘ G.δˢ (ρᶠ f)) ∘ G.δ (ρᶠ f)
        ≡⟨ extendl (G.weave (ext (pullr (ap₂ _∘_ refl (elimr G.δ-top)) ∙ p0 ,ₚ pulll (eliml refl) ∙ intror refl))) ⟩
      G.map _ ∘ G.map (δ-sq f) ∘ G.δ (ρᶠ f)
        ∎
```

<!--
```agda
  Lwfs-on-tensor .L-comonad .δ-unitl {x , y , f} = ext $ idl id ,ₚ
    pulll (G.collapse (ext (pulll (F.collapse
      (ext (idl id ,ₚ sym (G.factors (ρᶠ f))))) ∙ F.δ-unitl ,ₚ idr _)))
    ∙ G.δ-unitl

  Lwfs-on-tensor .L-comonad .δ-unitr {x , y , f} = ext $ idl id ,ₚ
    G.lift-λρ (δ-sq f) .snd .snd
```
-->
