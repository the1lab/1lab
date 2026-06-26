<!--
```agda
open import Cat.Instances.Shape.Terminal
open import Cat.Instances.Localisation
open import Cat.Functor.Conservative
open import Cat.Instances.Shape.Join
open import Cat.Diagram.Limit.Base
open import Cat.Diagram.Terminal
open import Cat.Instances.Slice
open import Cat.Connected
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
$\{*,*\}$ --- we have [[adjoined|adjoined terminal object]] a
[[terminal object]] to our diagram shape.

<!--
```agda
module
  _ {o ℓ o' ℓ'} {C : Precategory o ℓ} {J : Precategory o' ℓ'} {o : ⌞ C ⌟}
    (F : Functor J (Slice C o))
    where

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
this into a diagram $F' : cJ^\triangleright \to \cC$, compute the limit
in $\cC$, then pass back to the slice category.

```agda
    F' : Functor (J ▹) C
    F' = to-slice→from-▹ F

  limit-above→limit-in-slice : Limit F' → Limit F
  limit-above→limit-in-slice lims = to-limit (to-is-limit lim) where
    module lims = Limit lims
    open make-is-limit

    apex : C/o.Ob
    apex = cut (lims.ψ (inr tt))

    nadir : (j : J.Ob) → /-Hom apex (F .F₀ j)
    nadir j .map = lims.ψ (inl j)
    nadir j .com = lims.commutes (lift tt)

    module Cone
      {x : C/o.Ob}
      (eps : (j : J.Ob) → C/o.Hom x (F .F₀ j))
      (p : ∀ {i j : J.Ob} → (f : J.Hom i j) → F .F₁ f C/o.∘ eps i ≡ eps j)
      where

        ϕ : (j : J.Ob ⊎ ⊤) → C.Hom (x .dom) (F' .F₀ j)
        ϕ (inl j) = eps j .map
        ϕ (inr _) = x .map

        ϕ-commutes
          : ∀ {i j : J.Ob ⊎ ⊤}
          → (f : ⋆Hom J ⊤Cat i j)
          → F' .F₁ f C.∘ ϕ i ≡ ϕ j
        ϕ-commutes {inl i} {inl j} (lift f) = ap map (p f)
        ϕ-commutes {inl i} {inr j} (lift f) = eps i .com
        ϕ-commutes {inr i} {inr x} (lift f) = C.idl _

        ϕ-factor
          : ∀ (other : /-Hom x apex)
          → (∀ j → nadir j C/o.∘ other ≡ eps j)
          → (j : J.Ob ⊎ ⊤)
          → lims.ψ j C.∘ other .map ≡ ϕ j
        ϕ-factor other q (inl j)  = ap map (q j)
        ϕ-factor other q (inr tt) = other .com

    lim : make-is-limit F apex
    lim .ψ          = nadir
    lim .commutes f = ext (lims.commutes (lift f))

    lim .universal {x} eps p .map = lims.universal
      (Cone.ϕ eps p) (Cone.ϕ-commutes eps p)
    lim .universal {x} eps p .com = lims.factors _ _

    lim .factors eps p         = ext (lims.factors _ _)
    lim .unique  eps p other q = ext $
      lims.unique _ _ (other .map) (Cone.ϕ-factor eps p other q)
```

In particular, if a category $\cC$ is complete, then so are its slices:

```agda
is-complete→slice-is-complete
  : ∀ {ℓ o o' ℓ'} {C : Precategory o ℓ} {c : ⌞ C ⌟}
  → is-complete o' ℓ' C
  → is-complete o' ℓ' (Slice C c)
is-complete→slice-is-complete lims F = limit-above→limit-in-slice F (lims _)
```

## Connected limits in slices {defines="connected-limits-in-slice-categories"}

We can simplify this story for a particular class of limits: the
forgetful functor $U : \cC/o \to \cC$ [[creates|created limit]]
*connected* limits.^[That is, limits of shape a [[connected category]].
This notably includes [[pullbacks]], but *not* terminal objects or
binary products, since their shape categories have respectively 0 and 2
connected components.]
For instance, a [[pullback]] in $\cC/o$ is computed exactly as a
pullback in $\cC$ (assuming this pullback exists), ignoring the maps
into $o$. Contrast this with the fact that [[colimits in slice
categories]] are *all* created by the forgetful functor.

To get some intuition for the connectedness requirement, we can think
type-theoretically: an object of $\cC/A$ is, in the internal language of
$\cC$, a "type in context $A$", $a : A \vdash B(a)$, while the forgetful
functor can be thought of as forming the $\Sigma$-type $\sum_{a : A} B(a)$.
Then, given a diagram of types $a : A \vdash B_i(a)$ in $\cC/A$ with
maps between them over $A$, the limit of the induced diagram of closed
types consists of a bunch of pairs $(a_i : A, b_i : B_i(a_i))$ obeying
some relations; but, since the diagram has a connected shape, those
relations ensure that all the $a_i$s are equal! Thus, it is enough
to compute the limit *over $A$* and then take the $\Sigma$.

<!--
```agda
module
  _ {o ℓ o' ℓ'} {C : Precategory o ℓ} {J : Precategory o' ℓ'} {A : ⌞ C ⌟}
    where

  private
    module C = Cat.Reasoning C
    module J = Precategory J

  open lifts-limit
  open /-Obj
  open /-Hom
```
-->

We start by showing that `Forget/`{.Agda} [[lifts limits]]: given a
diagram $D$ in $\cC/A$ and its limit $L$ in $\cC$, the key step is to find
a suitable map $L \to A$ to promote this to a limit in $\cC/A$.
As hinted above, we can pick any object $j : J$ and set this to the
composite $L \to D_j \to A$; since $J$ is connected, the choice of
$j$ doesn't matter, and there is at least one object by assumption.

```agda
  Forget/-lifts-connected-limits
    : is-connected-cat J
    → lifts-limits-of J (Forget/ {C = C} {c = A})
  Forget/-lifts-connected-limits conn {D} L .lifted = to-limit (to-is-limit L')
    where
      module D = Functor D
      module L = Limit L
      module conn = is-connected-groupoid conn

      proj : J.Ob → C.Hom L.apex A
      proj j = D.₀ j .map C.∘ L.ψ j

      proj' : ∥ J.Ob ∥ → C.Hom L.apex A
      proj' = connected-∥-∥-rec! conn proj λ {x} {y} f →
        D.₀ x .map C.∘ L.ψ x                ≡⟨ C.pushl (sym (D.₁ f .com)) ⟩
        D.₀ y .map C.∘ D.₁ f .map C.∘ L.ψ x ≡⟨ C.cdr (L.commutes f) ⟩
        D.₀ y .map C.∘ L.ψ y                ∎
```

The rest is an uneventful computation.

```agda
      L' : make-is-limit D (cut (proj' conn.point))
      L' .make-is-limit.ψ j .map = L.ψ j
      L' .make-is-limit.ψ j .com = ap proj' (squash (inc _) conn.point)
      L' .make-is-limit.commutes f = ext (L.commutes f)
      L' .make-is-limit.universal eps comm .map =
        L.universal (λ j → eps j .map) λ {x} {y} f → unext (comm f)
      L' .make-is-limit.universal eps comm .com =
        case conn.point return (λ p → proj' p C.∘ _ ≡ _) of λ j →
          C.pullr (L.factors _ _) ∙ eps j .com
      L' .make-is-limit.factors eps comm = ext (L.factors _ _)
      L' .make-is-limit.unique eps comm other fac =
        ext (L.unique _ _ _ λ j → unext (fac j))

  Forget/-lifts-connected-limits conn lim .preserved =
    generalize-limitp (Limit.has-limit lim) refl
```

Since `Forget/`{.Agda} is [[conservative]], we conclude that it creates
connected limits.

```agda
  Forget/-creates-connected-limits
    : is-connected-cat J
    → creates-limits-of J (Forget/ {C = C} {c = A})
  Forget/-creates-connected-limits conn = conservative+lifts→creates-limits
    Forget/-is-conservative (Forget/-lifts-connected-limits conn)
```
