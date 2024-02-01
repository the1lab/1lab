<!--
```agda
open import Cat.Functor.Naturality
open import Cat.Instances.Product
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Functor.Reasoning as Fr
import Cat.Reasoning
import Cat.Morphism

open Functor
open _=>_
```
-->

```agda
module Cat.Functor.Compose where
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
will be denoted $- \circ p : [C', D] \to [C,D]$ in TeX and `precompose`{.Agda} in Agda;
- The _postcomposition functor_ associated with any $p : C \to C'$,
which will be denoted $p \circ - : [A,C] \to [A,C']$; In the code, that's
`postcompose`{.Agda}.

Note that the precomposition functor $- \circ p$ is necessarily
"contravariant" when compared with $p$, in that it points in the
opposite direction to $p$.

<!--
```agda
private variable
  o ℓ : Level
  A B C C' D E : Precategory o ℓ
  F G H K : Functor C D
  α β γ : F => G
```
-->

We start by defining the action of the composition functor on *morphisms*:
given a pair of natural transformations as in the following diagram, we
define their **horizontal composition** as a natural transformation
$F \circ H \To G \circ K$.

~~~{.quiver}
\[\begin{tikzcd}
  C & D & E
  \arrow[""{name=0, anchor=center, inner sep=0}, "F", curve={height=-12pt}, from=1-2, to=1-3]
  \arrow[""{name=1, anchor=center, inner sep=0}, "G"', curve={height=12pt}, from=1-2, to=1-3]
  \arrow[""{name=2, anchor=center, inner sep=0}, "H", curve={height=-12pt}, from=1-1, to=1-2]
  \arrow[""{name=3, anchor=center, inner sep=0}, "K"', curve={height=12pt}, from=1-1, to=1-2]
  \arrow["\alpha"', shorten <=3pt, shorten >=3pt, Rightarrow, from=0, to=1]
  \arrow["\beta", shorten <=3pt, shorten >=3pt, Rightarrow, from=2, to=3]
\end{tikzcd}\]
~~~

Note that there are two ways to do so, but they are equal by naturality
of $\alpha$.

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

We can now define the composition functor itself.

```agda
F∘-functor : Functor (Cat[ B , C ] ×ᶜ Cat[ A , B ]) Cat[ A , C ]
F∘-functor {C = C} = go module F∘-f where
  private module C = Cat.Reasoning C
  go : Functor _ _
  go .F₀ (F , G) = F F∘ G
  go .F₁ (α , β) = α ◆ β

  go .F-id {x} = Nat-path λ _ → C.idr _ ∙ x .fst .F-id
  go .F-∘ {x} {y , _} {z , _} (f , _) (g , _) = Nat-path λ _ →
    z .F₁ _ C.∘ f .η _ C.∘ g .η _                 ≡⟨ C.pushl (z .F-∘ _ _) ⟩
    z .F₁ _ C.∘ z .F₁ _ C.∘ f .η _ C.∘ g .η _     ≡⟨ C.extend-inner (sym (f .is-natural _ _ _)) ⟩
    z .F₁ _ C.∘ f .η _ C.∘ y .F₁ _ C.∘ g .η _     ≡⟨ C.pulll refl ⟩
    (z .F₁ _ C.∘ f .η _) C.∘ (y .F₁ _ C.∘ g .η _) ∎

{-# DISPLAY F∘-f.go = F∘-functor #-}
```

Before setting up the pre/post-composition functors, we define their
action on morphisms, called **whiskerings**: these are special cases
of horizontal composition where one of the natural transformations is
the identity, so defining them directly saves us one application of the
unit laws. The mnemonic for triangles is that the base
points towards the side that does _not_ change, so in (e.g.) $F
\blacktriangleright \theta$, the $F$ is unchanging: this expression has
type $FG \to FH$, as long as $\theta : G \to H$.

```agda
_◂_ : F => G → (H : Functor C D) → F F∘ H => G F∘ H
_◂_ nt H .η x = nt .η _
_◂_ nt H .is-natural x y f = nt .is-natural _ _ _

_▸_ : (H : Functor E C) → F => G → H F∘ F => H F∘ G
_▸_ H nt .η x = H .F₁ (nt .η x)
_▸_ H nt .is-natural x y f =
  sym (H .F-∘ _ _) ∙ ap (H .F₁) (nt .is-natural _ _ _) ∙ H .F-∘ _ _
```

With the whiskerings already defined, defining $- \circ p$ and $p \circ -$ is easy:

```agda
module _ (p : Functor C C') where
  precompose : Functor Cat[ C' , D ] Cat[ C , D ]
  precompose .F₀ G    = G F∘ p
  precompose .F₁ θ    = θ ◂ p
  precompose .F-id    = Nat-path λ _ → refl
  precompose .F-∘ f g = Nat-path λ _ → refl

  postcompose : Functor Cat[ D , C ] Cat[ D , C' ]
  postcompose .F₀ G    = p F∘ G
  postcompose .F₁ θ    = p ▸ θ
  postcompose .F-id    = Nat-path λ _ → p .F-id
  postcompose .F-∘ f g = Nat-path λ _ → p .F-∘ _ _
```

<!--
[TODO: Reed M, 13/02/2023] Add whiskering reasoning combinators!
-->

<!--
```agda
module _ {F G : Functor C D} where
  open Cat.Morphism
  open Fr

  _◂ni_ : F ≅ⁿ G → (H : Functor B C) → (F F∘ H) ≅ⁿ (G F∘ H)
  (α ◂ni H) = make-iso _ (α .to ◂ H) (α .from ◂ H)
    (Nat-path λ _ → α .invl ηₚ _)
    (Nat-path λ _ → α .invr ηₚ _)

  _▸ni_ : (H : Functor D E) → F ≅ⁿ G → (H F∘ F) ≅ⁿ (H F∘ G)
  (H ▸ni α) = make-iso _ (H ▸ α .to) (H ▸ α .from)
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

module _ where
  open Cat.Reasoning

  -- [TODO: Reed M, 14/03/2023] Extend the coherence machinery to handle natural
  -- isos.
  ni-assoc : {F : Functor D E} {G : Functor C D} {H : Functor B C}
         → (F F∘ G F∘ H) ≅ⁿ ((F F∘ G) F∘ H)
  ni-assoc {E = E} = to-natural-iso λ where
    .make-natural-iso.eta _ → E .id
    .make-natural-iso.inv _ → E .id
    .make-natural-iso.eta∘inv _ → E .idl _
    .make-natural-iso.inv∘eta _ → E .idl _
    .make-natural-iso.natural _ _ _ → E .idr _ ∙ sym (E .idl _)
```
-->
