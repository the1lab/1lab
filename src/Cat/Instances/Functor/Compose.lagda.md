```agda
open import Cat.Instances.Functor
open import Cat.Instances.Product
open import Cat.Prelude

import Cat.Functor.Reasoning as Fr
import Cat.Reasoning
import Cat.Morphism

open Functor
open _=>_

module Cat.Instances.Functor.Compose where
```

# Functoriality of functor composition

When the operation of functor composition, $(F, G) \mapsto F \circ G$,
is seen as happening not only to functors but to whole functor
_categories_, then it is _itself_ functorial. This is a bit mind-bending
at first, but this module will construct the _functor composition
functors_. There's actually a family of three related functors we're
interested in:

- The functor composition functor itself, having type $[B, C] \times [A,
B] \to [A,C]$;
- The _precomposition functor_ associated with any $p : C \to C'$, which
will be denoted $p_! : [C', D] \to [C,D]$ in TeX and `_!`{.Agda} in Agda;
- The _postcomposition functor_ associated with any $p : C \to C'$,
which will be denoted $p^* : [A,C] \to [A,C']$; In the code, that's
`_^*`{.Agda}.

Note that the precomposition functor $p_!$ is necessarily
"contravariant" when compared with $p$, in that it points in the
opposite direction to $p$.

<!--
```agda
private variable
  o ℓ : Level
  A B C C′ D E : Precategory o ℓ
  F G H K : Functor C D
  α β γ : F => G
```
-->

```agda
F∘-functor : Functor (Cat[ B , C ] ×ᶜ Cat[ A , B ]) Cat[ A , C ]
F∘-functor {C = C} = go module F∘-f where
  private module C = Cat.Reasoning C
  go : Functor _ _
  go .F₀ (F , G) = F F∘ G

  go .F₁ {y = y , _} (n1 , n2) .η x = y .F₁ (n2 .η _) C.∘ n1 .η _

  go .F₁ {x = F , G} {y = W , X} (n1 , n2) .is-natural _ _ f =
    (W .F₁ (n2 .η _) C.∘ n1 .η _) C.∘ F .F₁ (G .F₁ f) ≡⟨ C.pullr (n1 .is-natural _ _ _) ⟩
    W .F₁ (n2 .η _) C.∘ W .F₁ (G .F₁ f) C.∘ n1 .η _   ≡⟨ C.extendl (W.weave (n2 .is-natural _ _ _)) ⟩
    W .F₁ (X .F₁ f) C.∘ W .F₁ (n2 .η _) C.∘ n1 .η _   ∎
    where module W = Fr W

  go .F-id {x} = Nat-path λ _ → C.idr _ ∙ x .fst .F-id
  go .F-∘ {x} {y , _} {z , _} (f , _) (g , _) = Nat-path λ _ →
    z .F₁ _ C.∘ f .η _ C.∘ g .η _                 ≡⟨ C.pushl (z .F-∘ _ _) ⟩
    z .F₁ _ C.∘ z .F₁ _ C.∘ f .η _ C.∘ g .η _     ≡⟨ C.extend-inner (sym (f .is-natural _ _ _)) ⟩
    z .F₁ _ C.∘ f .η _ C.∘ y .F₁ _ C.∘ g .η _     ≡⟨ C.pulll refl ⟩
    (z .F₁ _ C.∘ f .η _) C.∘ (y .F₁ _ C.∘ g .η _) ∎

{-# DISPLAY F∘-f.go = F∘-functor #-}
```

Before setting up the pre/post-composition functors, we define their
action on _morphisms_ (natural transformations) first, called
**whiskerings**, first. The mnemonic for triangles is that the base
points towards the side that does _not_ change, so in (e.g.) $f
\blacktriangleright \theta$, the $f$ is unchanging: this expression has
type $fg \to fh$, as long as $\theta : g \to h$.

```agda
_◂_ : F => G → (H : Functor C D) → F F∘ H => G F∘ H
_◂_ nt H .η x = nt .η _
_◂_ nt H .is-natural x y f = nt .is-natural _ _ _

_▸_ : (H : Functor E C) → F => G → H F∘ F => H F∘ G
_▸_ H nt .η x = H .F₁ (nt .η x)
_▸_ H nt .is-natural x y f =
  sym (H .F-∘ _ _) ∙ ap (H .F₁) (nt .is-natural _ _ _) ∙ H .F-∘ _ _
```


With the whiskerings already defined, defining $p_!$ and $p^*$ is easy:

```agda
module _ (p : Functor C C′) where
  _! : Functor Cat[ C′ , D ] Cat[ C , D ]
  _! .F₀ G    = G F∘ p
  _! .F₁ θ    = θ ◂ p
  _! .F-id    = Nat-path λ _ → refl
  _! .F-∘ f g = Nat-path λ _ → refl

  _^* : Functor Cat[ D , C ] Cat[ D , C′ ]
  _^* .F₀ G    = p F∘ G
  _^* .F₁ θ    = p ▸ θ
  _^* .F-id    = Nat-path λ _ → p .F-id
  _^* .F-∘ f g = Nat-path λ _ → p .F-∘ _ _
```

Whiskerings are instances of a more general form of composition for
natural transformations, known as **horizontal composition**.

```agda
_◆_ : ∀ {F G : Functor D E} {H K : Functor C D}
    → F => G → H => K → F F∘ H => G F∘ K
_◆_ {E = E} {F = F} {G} {H} {K} α β = nat module horizontal-comp where
  private module E = Cat.Reasoning E
  open Fr
  nat : F F∘ H => G F∘ K
  nat .η x = G .F₁ (β .η _) E.∘ α .η _
  nat .is-natural x y f =
    E.pullr (α .is-natural _ _ _)
    ∙ E.extendl (weave G (β .is-natural _ _ _))
```

<!--
```agda
{-# DISPLAY horizontal-comp.nat f g = f ◆ g #-}
```
-->

<!--
[TODO: Reed M, 13/02/2023] Add whiskering reasoning combinators!
-->

<!--
```agda
module _ {F G : Functor C D} where
  open Cat.Morphism
  open Fr

  _◂ni_ : natural-iso F G → (H : Functor B C) → natural-iso (F F∘ H) (G F∘ H)
  (α ◂ni H) =
    make-iso _ (α .to ◂ H) (α .from ◂ H)
      (Nat-path λ _ → α .invl ηₚ _)
      (Nat-path λ _ → α .invr ηₚ _)

  _▸ni_ : (H : Functor D E) → natural-iso F G → natural-iso (H F∘ F) (H F∘ G)
  (H ▸ni α) =
    make-iso _ (H ▸ α .to) (H ▸ α .from)
      (Nat-path λ _ → annihilate H (α .invl ηₚ _))
      (Nat-path λ _ → annihilate H (α .invr ηₚ _))
```
-->

<!--
```agda
◂-distribl : (α ∘nt β) ◂ H ≡ (α ◂ H) ∘nt (β ◂ H)
◂-distribl = Nat-path λ _ → refl

▸-distribr : F ▸ (α ∘nt β) ≡ (F ▸ α) ∘nt (F ▸ β)
▸-distribr {F = F} = Nat-path λ _ → F .F-∘ _ _
```
-->
