<!--
```agda
open import Cat.Instances.Shape.Terminal
open import Cat.Instances.Shape.Join
open import Cat.Diagram.Limit.Base
open import Cat.Diagram.Terminal
open import Cat.Instances.Slice
open import Cat.Prelude

open import Data.Sum

import Cat.Reasoning

open Functor
```
-->

```agda
module Cat.Instances.Slice.Limit where
```

# Arbitrary limits in slices {defines="limits-in-slice-categories"}

Suppose we have some really weird diagram $F : \cJ \to \cC/c$ in a
[[slice category]], like the
one below. Well, alright, it's not that weird, but it's not a pullback
or a terminal object, so we don't _a priori_ know how to compute its
limit in the slice.

~~~{.quiver}
\[\begin{tikzcd}
  & {(b,g)} && {(d,i)} \\
  {(a,f)} && {(c,h)}
  \arrow["x"', from=1-2, to=2-1]
  \arrow["y", from=1-2, to=2-3]
  \arrow["z"', from=1-4, to=2-3]
\end{tikzcd}\]
~~~

The observation that will let us compute a limit for this diagram is
inspecting the computation of [[products in a slice]]. To
compute the product of $(a, f)$ and $(b, g)$, we had to pass to a
_pullback_ of $a \xto{f} c \xot{g} b$ in $\cC$ --- which we had assumed
exists. But! Take a look at what that diagram _looks like_:

~~~{.quiver}
\[\begin{tikzcd}
  a && b \\
  \\
  & c
  \arrow["f"', from=1-1, to=3-2]
  \arrow["g", from=1-3, to=3-2]
\end{tikzcd}\]
~~~

We "exploded" a diagram of shape $\bullet \quad \bullet$ to one of shape
$\bullet \to \bullet \ot \bullet$. This process can be described in a
way easier to generalise: We "exploded" our diagram $F : \{*,*\} \to
\cC/c$ to one indexed by a category which contains $\{*,*\}$,
contains an extra point, and has a unique map between each object of
$\{*,*\}$ --- the [_join_] of these categories.

[_join_]: Cat.Instances.Shape.Join.html

<!--
```agda
module
  _ {o ℓ o' ℓ'} {C : Precategory o ℓ} {J : Precategory o' ℓ'} {o : ⌞ C ⌟}
    (F : Functor J (Slice C o))
    where

  open Terminal
  open /-Obj
  open /-Hom

  private
    module C   = Cat.Reasoning C
    module J   = Cat.Reasoning J
    module C/o = Cat.Reasoning (Slice C o)
    module F = Functor F
```
-->

Generically, if we have a diagram $F : J \to \cC/c$, we can "explode"
this into a diagram $F' : (J \star \{*\}) \to \cC$, compute the limit
in $\cC$, then pass back to the slice category.

```agda
    F' : Functor (J ⋆ ⊤Cat) C
    F' .F₀ (inl x) = F.₀ x .domain
    F' .F₀ (inr x) = o
    F' .F₁ {inl x} {inl y} (lift f) = F.₁ f .map
    F' .F₁ {inl x} {inr y} _ = F.₀ x .map
    F' .F₁ {inr x} {inr y} (lift h) = C.id
    F' .F-id {inl x} = ap map F.F-id
    F' .F-id {inr x} = refl
    F' .F-∘ {inl x} {inl y} {inl z} (lift f) (lift g) = ap map (F.F-∘ f g)
    F' .F-∘ {inl x} {inl y} {inr z} (lift f) (lift g) = sym (F.F₁ g .commutes)
    F' .F-∘ {inl x} {inr y} {inr z} (lift f) (lift g) = C.introl refl
    F' .F-∘ {inr x} {inr y} {inr z} (lift f) (lift g) = C.introl refl

  limit-above→limit-in-slice : Limit F' → Limit F
  limit-above→limit-in-slice lims = to-limit (to-is-limit lim) where
    module lims = Limit lims
    open make-is-limit

    apex : C/o.Ob
    apex = cut (lims.ψ (inr tt))

    nadir : (j : J.Ob) → /-Hom apex (F .F₀ j)
    nadir j .map = lims.ψ (inl j)
    nadir j .commutes = lims.commutes (lift tt)

    module Cone
      {x : C/o.Ob}
      (eta : (j : J.Ob) → C/o.Hom x (F .F₀ j))
      (p : ∀ {i j : J.Ob} → (f : J.Hom i j) → F .F₁ f C/o.∘ eta i ≡ eta j)
      where

        ϕ : (j : J.Ob ⊎ ⊤) → C.Hom (x .domain) (F' .F₀ j)
        ϕ (inl j) = eta j .map
        ϕ (inr _) = x .map

        ϕ-commutes
          : ∀ {i j : J.Ob ⊎ ⊤}
          → (f : ⋆Hom J ⊤Cat i j)
          → F' .F₁ f C.∘ ϕ i ≡ ϕ j
        ϕ-commutes {inl i} {inl j} (lift f) = ap map (p f)
        ϕ-commutes {inl i} {inr j} (lift f) = eta i .commutes
        ϕ-commutes {inr i} {inr x} (lift f) = C.idl _

        ϕ-factor
          : ∀ (other : /-Hom x apex)
          → (∀ j → nadir j C/o.∘ other ≡ eta j)
          → (j : J.Ob ⊎ ⊤)
          → lims.ψ j C.∘ other .map ≡ ϕ j
        ϕ-factor other q (inl j) = ap map (q j)
        ϕ-factor other q (inr tt) = other .commutes

    lim : make-is-limit F apex
    lim .ψ = nadir
    lim .commutes f = ext (lims.commutes (lift f))
    lim .universal {x} eta p .map =
      lims.universal (Cone.ϕ eta p) (Cone.ϕ-commutes eta p)
    lim .universal eta p .commutes =
      lims.factors _ _
    lim .factors eta p = ext (lims.factors _ _)
    lim .unique eta p other q = ext $
      lims.unique _ _ (other .map) (Cone.ϕ-factor eta p other q)
```

In particular, if a category $\cC$ is complete, then so are its slices:

```agda
is-complete→slice-is-complete
  : ∀ {ℓ o o' ℓ'} {C : Precategory o ℓ} {c : ⌞ C ⌟}
  → is-complete o' ℓ' C
  → is-complete o' ℓ' (Slice C c)
is-complete→slice-is-complete lims F = limit-above→limit-in-slice F (lims _)
```
