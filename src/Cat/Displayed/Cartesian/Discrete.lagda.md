---
description: |
  We define discrete fibrations,
  and explore their relations to presheaves.
---
<!--
```agda
open import Cat.Displayed.Functor.Equivalence
open import Cat.Displayed.Instances.Elements
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Functor
open import Cat.Instances.Functor
open import Cat.Displayed.Fibre
open import Cat.Displayed.Base
open import Cat.Displayed.Path
open import Cat.Prelude

import Cat.Displayed.Reasoning
import Cat.Displayed.Morphism
import Cat.Reasoning
```
-->

```agda
module Cat.Displayed.Cartesian.Discrete where
```

<!--
```agda
open Cartesian-lift
open is-cartesian
```
-->

# Discrete cartesian fibrations

A **discrete cartesian fibration** or **discrete fibration** is a
[[displayed category]] whose [[fibre categories]] are all _discrete categories_:
thin, univalent groupoids. Since thin, univalent groupoids are sets, a
discrete fibration over $\cB$ is an alternate way of encoding a presheaf
over $\cB$, i.e., a functor $\cB\op\to\Sets$. Here, we identify a purely fibrational
property that picks out the discrete fibrations among the displayed
categories, without talking about the fibres directly.

:::{.definition #discrete-cartesian-fibration alias="discrete-fibration"}
A discrete cartesian fibration is a displayed category such that each type of
displayed objects is a set, and such that, for each right corner

~~~{.quiver}
\[\begin{tikzcd}
  & {y'} \\
  x & {y\text{,}}
  \arrow[lies over, from=1-2, to=2-2]
  \arrow["f"', from=2-1, to=2-2]
\end{tikzcd}\]
~~~

there is a contractible space of objects $x'$ over $x$ equipped with
maps $x' \to_f y'$.
:::

<!--
```agda
module _ {o ℓ o' ℓ'} {B : Precategory o ℓ} (E : Displayed B o' ℓ') where
  private
    module B = Cat.Reasoning B
    open module E = Cat.Displayed.Reasoning E
    open Cat.Displayed.Morphism E
```
-->

```agda
  record is-discrete-cartesian-fibration : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ') where
    field
      fibre-set : ∀ x → is-set E.Ob[ x ]
      cart-lift
        : ∀ {x y} (f : B.Hom x y) (y' : E.Ob[ y ])
        → is-contr (Σ[ x' ∈ E.Ob[ x ] ] E.Hom[ f ] x' y')
```

We will denote the canonical lift of $f$ to $y'$ as
$$
\pi_{f, y'}^{*} : f^{*}(y') \to_{f} y'
$$

```agda
    _^*_ : ∀ {x y} → (f : B.Hom x y) (y' : E.Ob[ y ]) → E.Ob[ x ]
    f ^* y' = cart-lift f y' .centre .fst

    π* : ∀ {x y} → (f : B.Hom x y) (y' : E.Ob[ y ]) → E.Hom[ f ] (f ^* y') y'
    π* f y' = cart-lift f y' .centre .snd
```

## Basic properties of discrete cartesian fibrations

Every hom set of a discrete fibration is a [[proposition]].

```agda
    Hom[]-is-prop : ∀ {x y x' y'} {f : B.Hom x y} → is-prop (Hom[ f ] x' y')
```

Let $f', f'' : x' \to_{f} y'$ be a pair of morphisms in $\cE$. Both
$(x', f')$ and $(x' , f'')$ are candidates for lifts of $y'$ along
$f$, so contractibility of lifts ensures that $(x', f') = (x' , f'')$.
Moreover, the type of objects in $\cE$ forms a [[set]], so we can
conclude that $f' = f''$.

```agda
    Hom[]-is-prop {x' = x'} {y' = y'} {f = f} f' f'' =
      Σ-inj-set (fibre-set _) $
      is-contr→is-prop (cart-lift f y') (x' , f') (x' , f'')
```

We can improve the previous result by noticing that morphisms
$f' : x' \to_{f} y'$ give rise to proofs that $f^*(y') = x'$.

```agda
    opaque
      ^*-lift
        : ∀ {x y x' y'}
        → (f : B.Hom x y)
        → Hom[ f ] x' y'
        → f ^* y' ≡ x'
      ^*-lift {x' = x'} {y' = y'} f f' =
        ap fst $ cart-lift f y' .paths (x' , f')
```

We can further improve this to an equivalence between paths
$f^{*}(y') = x'$ and morphisms $x' \to y'$.

```agda
      ^*-hom
        : ∀ {x y x' y'}
        → (f : B.Hom x y)
        → f ^* y' ≡ x'
        → Hom[ f ] x' y'
      ^*-hom {x' = x'} {y' = y'} f p =
        hom[ B.idr f ] $
          π* f y' ∘' subst (λ y' → Hom[ B.id ] x' y') (sym p) id'

      ^*-hom-is-equiv
        : ∀ {x y x' y'}
        → (f : B.Hom x y)
        → is-equiv (^*-hom {x' = x'} {y' = y'} f)
      ^*-hom-is-equiv f =
        is-iso→is-equiv $
        iso (^*-lift f)
          (λ _ → Hom[]-is-prop _ _)
          (λ _ → fibre-set _ _ _ _ _)
```

## Functoriality of lifts

The (necessarily unique) choice of lifts in a discrete fibration are
contravariantly functorial.

```agda
    ^*-id
      : ∀ {x} (x' : Ob[ x ])
      → B.id ^* x' ≡ x'

    ^*-∘
      : ∀ {x y z}
      → (f : B.Hom y z) (g : B.Hom x y) (z' : Ob[ z ])
      → (f B.∘ g) ^* z' ≡ g ^* (f ^* z')
```

The proof here is rather slick. As noted earlier morphisms $x' \to_{f} y'$
in a discrete fibration correspond to proofs that $f^{*}(y') = x'$, so
it suffices to construct morphisms $x' \to_{id} x'$ and
$g^{*}(f^{*}(z')) \to_{f \circ g} z'$, resp. The former is given by
the identity morphism, and the latter by composition of lifts!

```agda
    ^*-id x' = ^*-lift B.id id'
    ^*-∘ f g z' = ^*-lift (f B.∘ g) (π* f z' ∘' π* g (f ^* z'))
```

## Invertible maps in discrete cartesian fibrations

Let $f : x \to y$ be an [[invertible]] morphism of $\cB$. If $\cE$
is a discrete fibration, then every morphism displayed over $f$ is
also invertible.

```agda
    all-invertible[]
      : ∀ {x y x' y'} {f : B.Hom x y}
      → (f' : Hom[ f ] x' y')
      → (f⁻¹ : B.is-invertible f)
      → is-invertible[ f⁻¹ ] f'
```

Let $f : x \to y$ be an invertible morphism, and $f' : x' \to_{f} y'$
be a morphism lying over $f$. Every hom set of $\cE$ is a proposition,
so constructing an inverse only requires us to exhibit a map
$y' \to_{f^{-1}} x'$, which in turn is given by a proof that $(f^{-1})^{*}(x') = y'$.
This is easy enough to prove with a bit of algebra.

```agda
    all-invertible[] {x' = x'} {y' = y'} {f = f} f' f⁻¹ = f'⁻¹ where
      module f⁻¹ = B.is-invertible f⁻¹
      open is-invertible[_]

      f'⁻¹ : is-invertible[ f⁻¹ ] f'
      f'⁻¹ .inv' =
        ^*-hom f⁻¹.inv $
          f⁻¹.inv ^* x'         ≡˘⟨ ap (f⁻¹.inv ^*_) (^*-lift f f') ⟩
          f⁻¹.inv ^* (f ^* y')  ≡˘⟨ ^*-∘ f f⁻¹.inv y' ⟩
          (f B.∘ f⁻¹.inv) ^* y' ≡⟨ ap (_^* y') f⁻¹.invl ⟩
          B.id ^* y'            ≡⟨ ^*-id y' ⟩
          y'                    ∎
      f'⁻¹ .inverses' .Inverses[_].invl' =
        is-prop→pathp (λ _ → Hom[]-is-prop) _ _
      f'⁻¹ .inverses' .Inverses[_].invr' =
        is-prop→pathp (λ _ → Hom[]-is-prop) _ _
```

As an easy corollary, we get that all vertical maps in a discrete
fibration are invertible.

```agda
    all-invertible↓
      : ∀ {x x' y'}
      → (f' : Hom[ B.id {x} ] x' y')
      → is-invertible↓ f'
    all-invertible↓ f' = all-invertible[] f' B.id-invertible
```


## Cartesian maps in discrete fibrations

Every morphism in a discrete fibration is [[cartesian|cartesian-morphism]].
Every hom set in a discrete fibration is propositional, so we just
need to establish the existence portion of the universal property.

```agda
    all-cartesian
      : ∀ {x y x' y'} {f : B.Hom x y}
      → (f' : Hom[ f ] x' y')
      → is-cartesian E f f'
    all-cartesian f' .commutes _ _ = Hom[]-is-prop _ _
    all-cartesian f' .unique _ _ = Hom[]-is-prop _ _
```

Suppose we have an open diagram

~~~{.quiver}
\[\begin{tikzcd}
  {u'} \\
  & {x'} && {y'} \\
  u \\
  & x && {y,}
  \arrow["{f'}"', from=2-2, to=2-4]
  \arrow["f", from=4-2, to=4-4]
  \arrow[lies over, from=2-2, to=4-2]
  \arrow[lies over, from=2-4, to=4-4]
  \arrow["g"', from=3-1, to=4-2]
  \arrow[lies over, from=1-1, to=3-1]
  \arrow["{h'}", curve={height=-12pt}, from=1-1, to=2-4]
\end{tikzcd}\]
~~~

where $f' : x' \to_{f} y'$ is the unique lift of $f$ along $y'$. We need to
find a map $u' \to_{g} x'$. By the usual yoga, it suffices to show that
$g^{*}(x') = u'$.

Note that we can transform $f' : x' \to_{f} y'$ into a proof that $f^{*}(y') = x'$,
and $h'$ into a proof that $(f \circ g)^{*}(y') = u'$. Moreover,
$(f \circ g)^{*}(y') = g^{*}(f^{*}(y'))$. Putting this all together, we get:

$$
\begin{align*}
g^{*}(x') &= g^{*}(f^{*}(y')) \\
          &= (f \circ g)^{*}(y') \\
          &= u'
\end{align*}
$$

```agda
    all-cartesian {x' = x'} {y' = y'} {f = f} f' .universal {u' = u'} g h' =
      ^*-hom g $
        g ^* x'          ≡˘⟨ ap (g ^*_) (^*-lift f f') ⟩
        (g ^* (f ^* y')) ≡˘⟨ ^*-∘ f g y' ⟩
        (f B.∘ g) ^* y'  ≡⟨ ^*-lift (f B.∘ g) h' ⟩
        u'               ∎
```

## Discrete fibrations are cartesian

To prove that discrete fibrations deserve the name discrete
_fibrations_, we prove that any discrete fibration is a [[Cartesian
fibration]].

```agda
  discrete→cartesian : is-discrete-cartesian-fibration → Cartesian-fibration E
  discrete→cartesian disc = r where
    open is-discrete-cartesian-fibration disc
    r : Cartesian-fibration E
```

Luckily for us, the sea has already risen to meet us: by assumption,
every right corner has a unique lift, and every morphism in a discrete
fibration is cartesian.

```agda
    r f y' .x' = f ^* y'
    r f y' .lifting = π* f y'
    r f y' .cartesian = all-cartesian (π* f y')
```

## Discrete fibrations are presheaves {defines="discrete-fibrations-are-presheaves"}

As noted earlier, a discrete fibration over $\cB$ encodes the same
data as a presheaf on $\cB$. First, let us show that we can construct
a presheaf from a discrete fibration.

<!--
```agda
module _ {o ℓ} (B : Precategory o ℓ)  where
  private
    module B = Precategory B
```
-->

```agda
  discrete→presheaf
    : ∀ {o' ℓ'} (E : Displayed B o' ℓ')
    → is-discrete-cartesian-fibration E
    → Functor (B ^op) (Sets o')
  discrete→presheaf {o' = o'} E disc = psh where
    module E = Displayed E
    open is-discrete-cartesian-fibration disc
```

For each object $X : \cB$, we take the set of objects $E$ that
lie over $X$. The functorial action of `f : Hom X Y` is then constructed
by taking the domain of the lift of `f`. Functoriality follows by
uniqueness of the lifts.

```agda
    psh : Functor (B ^op) (Sets o')
    psh .Functor.F₀ X = el E.Ob[ X ] (fibre-set X)
    psh .Functor.F₁ f X' = f ^* X'
    psh .Functor.F-id = funext λ X' → ^*-id X'
    psh .Functor.F-∘ {X} {Y} {Z} f g = funext λ X' → ^*-∘ g f X'
```

To construct a discrete fibration from a presheaf $P$, we take the
[(displayed) category of elements] of $P$. This is a natural choice,
as it encodes the same data as $P$, just rendered down into a soup
of points and bits of functions. Discreteness follows immediately
from the contractibilty of singletons.

[(displayed) category of elements]: Cat.Displayed.Instances.Elements.html

```agda
  presheaf→discrete
    : ∀ {κ} → Functor (B ^op) (Sets κ)
    → Σ[ E ∈ Displayed B κ κ ] is-discrete-cartesian-fibration E
  presheaf→discrete {κ = κ} P = ∫ B P , discrete where
    module P = Functor P

    discrete : is-discrete-cartesian-fibration (∫ B P)
    discrete .is-discrete-cartesian-fibration.fibre-set X = hlevel 2
    discrete .is-discrete-cartesian-fibration.cart-lift f P[Y] = hlevel 0
```

We conclude by proving that the two maps defined above are, in fact,
inverses. Most of the complexity is in [characterising paths between
displayed categories][disppath], but that doesn't mean that the proof
here is entirely trivial, either. Well, first, we note that one
direction _is_ trivial: modulo differences in the proofs of
functoriality, which do not matter for identity, turning a functor into
a discrete fibration and back is the identity.

[disppath]: Cat.Displayed.Path.html

```agda
  open is-iso

  presheaf≃discrete : ∀ {κ} → is-iso (presheaf→discrete {κ = κ})
  presheaf≃discrete .from (d , f) = discrete→presheaf d f
  presheaf≃discrete .linv x       = Functor-path (λ _ → n-path refl) λ _ → refl
```

The other direction is where the complication lies. Given a discrete
fibration $P \liesover X$, how do we show that $\int P \equiv P$? Well,
by the aforementioned characterisation of paths in displayed categories,
it'll suffice to construct a functor $(\int P) \to P$ (lying over the
identity), then show that this functor has an invertible action on
objects, and an invertible action on morphisms.

```agda
  presheaf≃discrete .rinv (P , p-disc) = Σ-prop-path hl ∫≡dx where
    open is-discrete-cartesian-fibration p-disc
    open Displayed-functor
    open Displayed P
```

The functor will send an object $c \liesover x$ to that same object $c$;
This is readily seen to be invertible. But the action on morphisms is
slightly more complicated. Recall that, since $P$ is a discrete
fibration, every span $b' \liesover b \xot{f} a$ has a contractible
space of Cartesian lifts $(a', f')$. Our functor must, given objects
$a'', b'$, a map $f : a \to b$, and a proof that $a'' = a'$, produce a
map $a'' \to_f b$ --- so we can take the canonical $f' : a' \to_f b$ and
transport it over the given $a'' = a'$.

```agda
    pieces : Vertical-functor (∫ B (discrete→presheaf P p-disc)) P
    pieces .F₀' x = x
    pieces .F₁' {f = f} {a'} {b'} x =
      subst (λ e → Hom[ f ] e b') x $ cart-lift f b' .centre .snd
```

This transport _threatens_ to throw a spanner in the works, since it is
an equation between objects (over $a$). But since $P$ is a discrete
fibration, the space of objects over $a$ is a set, so this equation
_can't_ ruin our day. Directly from the uniqueness of $(a', f')$ we
conclude that we've put together a functor.

```agda
    pieces .F-id' =
      is-prop→pathp (λ _ → Hom[]-is-prop) _ _
    pieces .F-∘' {f = f} {g} {a'} {b'} {c'} {f'} {g'} =
      is-prop→pathp (λ _ → Hom[]-is-prop) _ _
```

It remains to show that, given a map $a'' \to b$ (and the rest of the
data $a$, $b$, $f : a \to b$, $b' \liesover b$), we can recover a proof
that $a''$ is the chosen lift $a'$. But again, lifts are unique, so this
is immediate.

```agda
    ∫≡dx : ∫ B (discrete→presheaf P p-disc) ≡ P
    ∫≡dx = Displayed-path pieces $ iso[] (is-iso→is-equiv p) (λ _ → id-equiv) where
      p : ∀ {a b} {f : B.Hom a b} {a'} {b'} → is-iso (pieces .F₁' {f = f} {a'} {b'})
      p .from f = ap fst $ cart-lift _ _ .paths (_ , f)
      p .rinv p = from-pathp (ap snd (cart-lift _ _ .paths _))
      p .linv p = fibre-set _ _ _ _ _
```

We must additionally show that the witness that $P$ is a discrete
fibration will survive a round-trip through the type of presheaves, but
this witness lives in a proposition (it is a pair of propositions), so
it survives automatically.

```agda
    unquoteDecl eqv = declare-record-iso eqv (quote is-discrete-cartesian-fibration)
    hl : ∀ x → is-prop _
    hl x = Iso→is-hlevel! 1 eqv
```
