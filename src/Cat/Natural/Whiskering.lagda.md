<!-- 
```agda
open import Cat.Prelude

open Functor
```
-->

```agda
module Cat.Natural.Whiskering
  {oc ℓc od ℓd oe ℓe} 
  {𝒞 : Precategory oc ℓc} {𝒟 : Precategory od ℓd}
  {F G : Functor 𝒞 𝒟} {ℰ : Precategory oe ℓe}
  where
```

<!--
```agda
private 
  module ℰ = Precategory ℰ
  module 𝒟 = Precategory 𝒟
```
-->

# Whiskering of natural transformations

Let $F, G : \cC \to \cD$ be functors and $\phi : F \To G$ be a
[[natural transformation]] with components $\phi_x$ for $x \in \cC$. If 
$H : \cD \to \cE$ is a [[functor]], then **whiskering** $\phi$ with $H$ 
on the right gives a natural transformation $H \circ F \To H \circ G$ 
with components $H(\phi_x)$ for $x \in \cC$.

```agda
infix 35 _◀_ _▶_
_▶_ : ∀ (H : Functor 𝒟 ℰ) (φ : F => G) → H F∘ F => H F∘ G
H ▶ φ = NT (λ x → ₁ H (η x)) nat where 
  open _=>_ φ
  nat : ∀ x y f → _
  nat x y f = 
    ₁ H (η y) ℰ.∘ ₁ H (₁ F f) ≡˘⟨ H .F-∘ (η y) (₁ F f) ⟩
    ₁ H (η y 𝒟.∘ ₁ F f)       ≡⟨ ap (₁ H) (is-natural x y f) ⟩
    ₁ H (₁ G f 𝒟.∘ η x)       ≡⟨ F-∘ H (₁ G f) (η x) ⟩
    ₁ H (₁ G f) ℰ.∘ ₁ H (η x) ∎
```

Similarly, if $H : \cE \to \cC$ is a functor, then whiskering $\phi$ 
with $H$ on the left gives a natural transformation $F \circ H \To G \circ H$
with components $\phi_{H x}$ for $x \in \cE$.

```agda
_◀_ : ∀ (φ : F => G) (H : Functor ℰ 𝒞) → F F∘ H => G F∘ H
φ ◀ H = NT (λ x → η (₀ H x)) nat where
  open _=>_ φ
  nat : ∀ x y f → _
  nat x y f = is-natural (₀ H x) (₀ H y) (₁ H f)
```

This is a special case of whiskering in a general [[bicategory]],
being the whiskering operation in the [[bicategory of categories]].