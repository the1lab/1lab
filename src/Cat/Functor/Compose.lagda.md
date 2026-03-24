<!--
```agda
open import Cat.Functor.Naturality
open import Cat.Functor.Bifunctor
open import Cat.Instances.Product
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Functor.Reasoning as Fr
import Cat.Reasoning as Cr
import Cat.Morphism

open Functor
open _=>_
```
-->

```agda
module Cat.Functor.Compose where
```

# Functoriality of functor composition {defines="precomposition-functor postcomposition-functor"}

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
  A B C C' D D' E E' : Precategory o ℓ
  F G H K L M : Functor C D
  α β γ : F => G
```
-->

:::{.definition #horizontal-composition-in-cat}
We start by defining the action of the composition functor on *morphisms*:
given a pair of natural transformations as in the following diagram, we
define their **horizontal composition** as a natural transformation
$F \circ H \To G \circ K$.
:::

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
_◂_ : F => G → (H : Functor C D) → F F∘ H => G F∘ H
_◂_ nt H .η x = nt .η _
_◂_ nt H .is-natural x y f = nt .is-natural _ _ _

_▸_ : (H : Functor E C) → F => G → H F∘ F => H F∘ G
_▸_ H nt .η x = H .F₁ (nt .η x)
_▸_ H nt .is-natural x y f =
  sym (H .F-∘ _ _) ∙ ap (H .F₁) (nt .is-natural _ _ _) ∙ H .F-∘ _ _
```

```agda
F∘-functor : Bifunctor Cat[ B , C ] Cat[ A , B ] Cat[ A , C ]
F∘-functor {C = C} = make-bifunctor record where
  F₀ F G = F F∘ G
  lmap     f = f ◂ _
  lmap-∘ f g = ext λ _ → refl
  lmap-id    = ext λ _ → refl

  rmap              f = _ ▸ f
  rmap-∘  {a = F} f g = ext λ _ → F .F-∘ _ _
  rmap-id {a = F}     = ext λ _ → F .F-id

  lrmap f g = ext λ _ → f .is-natural _ _ _
```

```agda
_◆_ : ∀ {F G : Functor D E} {H K : Functor C D}
    → F => G → H => K → F F∘ H => G F∘ K
_◆_ = Bifunctor._◆_ F∘-functor
```

Before setting up the pre/post-composition functors, we define their
action on morphisms, called **whiskerings**: these are special cases
of horizontal composition where one of the natural transformations is
the identity, so defining them directly saves us one application of the
unit laws. The mnemonic for triangles is that the base
points towards the side that does _not_ change, so in (e.g.) $F
\blacktriangleright \theta$, the $F$ is unchanging: this expression has
type $FG \to FH$, as long as $\theta : G \to H$.


With the composition functor already defined, defining $- \circ p$ and
$p \circ -$ is easy:

```agda
module _ (p : Functor C C') where
  precompose : Functor Cat[ C' , D ] Cat[ C , D ]
  precompose = Bifunctor.Left F∘-functor p

  postcompose : Functor Cat[ D , C ] Cat[ D , C' ]
  postcompose = Bifunctor.Right F∘-functor p
```

We also remark that horizontal composition obeys a very handy interchange
law.

```agda
◆-interchange
  : {F H L : Functor B C} {G K M : Functor A B}
  → (α : F => H) (β : G => K)
  → (γ : H => L) (δ : K => M)
  → (γ ◆ δ) ∘nt (α ◆ β) ≡ (γ ∘nt α) ◆ (δ ∘nt β)
◆-interchange {B = B} {C = C} {A = A} {H = H} {L = L} α β γ δ =
  sym (Bifunctor.◆-∘ F∘-functor)
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
  (α ◂ni H) = make-iso! _ (α .to ◂ H) (α .from ◂ H)
    (λ _ → α .invl ηₚ _)
    (λ _ → α .invr ηₚ _)

  _▸ni_ : (H : Functor D E) → F ≅ⁿ G → (H F∘ F) ≅ⁿ (H F∘ G)
  (H ▸ni α) = make-iso! _ (H ▸ α .to) (H ▸ α .from)
    (λ _ → annihilate H (α .invl ηₚ _))
    (λ _ → annihilate H (α .invr ηₚ _))
```
-->

<!--
```agda
◂-distribl : (α ∘nt β) ◂ H ≡ (α ◂ H) ∘nt (β ◂ H)
◂-distribl = ext λ _ → refl

▸-distribr : F ▸ (α ∘nt β) ≡ (F ▸ α) ∘nt (F ▸ β)
▸-distribr {F = F} = ext λ _ → F .F-∘ _ _

▸-id : H ▸ idnt {F = F} ≡ idnt
▸-id {H = H} = ext λ _ → H .Functor.F-id

module _ where
  open Cr

  -- [TODO: Reed M, 14/03/2023] Extend the coherence machinery to handle natural
  -- isos.
  ni-assoc
    : {F : Functor D E} {G : Functor C D} {H : Functor B C}
    → (F F∘ G F∘ H) ≅ⁿ ((F F∘ G) F∘ H)
  ni-assoc {E = E} = to-natural-iso λ where
    .make-natural-iso.eta _ → E .id
    .make-natural-iso.inv _ → E .id
    .make-natural-iso.eta∘inv _ → E .idl _
    .make-natural-iso.inv∘eta _ → E .idl _
    .make-natural-iso.natural _ _ _ → E .idr _ ∙ sym (E .idl _)

open Make-bifunctor
open Make-binatural

module _ (B : Bifunctor C D E) (F : Functor C' C) (G : Functor D' D) where
  private
    module F = Functor F
    module G = Functor G
    module B = Bifunctor B

  precompose₂ : Bifunctor C' D' E
  precompose₂ = make-bifunctor λ where
    .F₀     a b → B · F.₀ a · G.₀ b
    .lmap     f → B.lmap (F.₁ f)
    .rmap     f → B.rmap (G.₁ f)
    .lmap-id    → ap B.lmap F.F-id ∙ B.lmap-id
    .rmap-id    → ap B.rmap G.F-id ∙ B.rmap-id
    .lmap-∘ f g → ap B.lmap (F.F-∘ _ _) ∙ B.lmap-∘ _ _
    .rmap-∘ f g → ap B.rmap (G.F-∘ _ _) ∙ B.rmap-∘ _ _
    .lrmap  f g → B.lrmap _ _

module _ {B : Bifunctor C D E} {F : Functor C' C} {G : Functor D' D} where
  private
    open module B = Bifunctor B
    module F = Functor F
    module G = Functor G
    module E = Cr E

  whisker-precompose₂
    : {F' : Functor C' C} {G' : Functor D' D} (e1 : F => F') (e2 : G => G')
    → precompose₂ B F G => precompose₂ B F' G'
  whisker-precompose₂ e1 e2 .η x .η y              = e1 · x B.◆ e2 · y
  whisker-precompose₂ e1 e2 .η x .is-natural y z f =
    ▶.extendr (e2 .is-natural _ _ _) ∙ E.pushl (B.lrmap _ _)
  whisker-precompose₂ e1 e2 .is-natural x y f = ext λ z →
      E.pullr (B.rlmap _ _) ∙ ◀.extendl (e1 .is-natural _ _ _)

  whisker-precomposeˡ
    : {F' : Functor C' C} (e1 : F => F')
    → precompose₂ B F G => precompose₂ B F' G
  whisker-precomposeˡ e1 .η x .η y = e1 · x ◀ _
  whisker-precomposeˡ e1 .η x .is-natural y z f = B.lrmap _ _
  whisker-precomposeˡ e1 .is-natural x y z = ext λ z → ◀.weave (e1 .is-natural _ _ _)

  whisker-precomposeʳ
    : {G' : Functor D' D} (e2 : G => G')
    → precompose₂ B F G => precompose₂ B F G'
  whisker-precomposeʳ e2 .η x .η y = F.₀ x ▶ e2 .η y
  whisker-precomposeʳ e2 .η x .is-natural y z f = ▶.weave (e2 .is-natural y z f)
  whisker-precomposeʳ e2 .is-natural x y f = ext λ z → B.rlmap (e2 .η z) (F.F₁ f)

module _ (F : Functor E E') (B : Bifunctor C D E) where
  private
    module F = Functor F
    module B = Bifunctor B

  postcompose₂ : Bifunctor C D E'
  postcompose₂ = make-bifunctor λ where
    .F₀     a b → F.₀ (B · a · b)
    .lmap     f → F.₁ (B.lmap f)
    .rmap     f → F.₁ (B.rmap f)
    .lmap-id    → ap F.₁ B.lmap-id ∙ F.F-id
    .rmap-id    → ap F.₁ B.rmap-id ∙ F.F-id
    .lmap-∘ f g → ap F.₁ (B.lmap-∘ _ _) ∙ F.F-∘ _ _
    .rmap-∘ f g → ap F.₁ (B.rmap-∘ _ _) ∙ F.F-∘ _ _
    .lrmap  f g → Fr.weave F (B.lrmap f g)

module _ {B : Bifunctor C D E} {F F' : Functor E E'} where
  private
    open module B = Bifunctor B
    module F = Functor F
    module F' = Functor F'
    module E = Cr E

  whisker-postcompose₂
    : (e : F => F')
    → postcompose₂ F B => postcompose₂ F' B
  whisker-postcompose₂ e = make-binatural λ where
    .η x y → e .η (B.F₀ x y)
    .is-natural-◀ f x → e .is-natural _ _ (f ◀ x)
    .is-natural-▶ x f → e .is-natural _ _ (x ▶ f)
```
-->
