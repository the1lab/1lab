---
description: |
  Beck-Chevalley conditions.
---
<!--
```agda
open import Cat.Displayed.Cartesian.Indexing
open import Cat.Displayed.Cocartesian.Weak
open import Cat.Displayed.Cocartesian
open import Cat.Functor.Adjoint.Mate
open import Cat.Displayed.Cartesian
open import Cat.Functor.Naturality
open import Cat.Displayed.Fibre
open import Cat.Functor.Adjoint
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Fibre.Reasoning
import Cat.Displayed.Reasoning
import Cat.Displayed.Morphism
import Cat.Functor.Reasoning
import Cat.Reasoning
```
-->
```agda
module Cat.Displayed.BeckChevalley where
```

# Beck-Chevalley conditions {defines="Beck-Chevalley-condition"}

Let $\cE \liesover \cB$ be a [[cartesian fibration]], which we shall
view as a setting for some sort of logic or type theory. In particular,
we shall view the corresponding [[base change]] functors $f^{*} :
\cE_{Y} \to \cE_{X}$ as an operation of substitution on
predicates/types, and assume that $\cB$ has [[finite products]]. This
setup leads to a tidy definition of existential quantifiers as left
adjoints $\exists_{Y} : \cE_{X \times Y} \to \cE_{X}$ to the base changes
along projections $\pi : X \times Y \to X$:

- The introduction rule is given by the unit
    $\eta : \cE_{X}(P, \exists_{Y} (\pi^{*} P))$;
- The elimination rule is given by the counit
    $\eps : \cE_{X \times Y}(\pi^{*}(\exists_{Y} P), P)$; and
- The $\beta$ and $\eta$ rules are given by the zig-zag equations.

This story is quite elegant, but there is a missing piece: how do
substitutions interact with $\exists$, or, in categorical terms, how do
base change functors commute with their left adjoints? In particular,
consider the following diagram:

~~~{.quiver}
\begin{tikzcd}
  {\mathcal{E}_{\Gamma \times X}} && {\mathcal{E}_{\Gamma}} \\
  \\
  {\mathcal{E}_{\Delta \times X}} && {\mathcal{E}_{\Delta}}
  \arrow["{\exists_{X}}", from=1-1, to=1-3]
  \arrow["{(\sigma \times \id)^{*}}"', from=1-1, to=3-1]
  \arrow["{\sigma^{*}}", from=1-3, to=3-3]
  \arrow["{\exists_{X}}"', from=3-1, to=3-3]
\end{tikzcd}
~~~

Ideally, we'd like
$\sigma^*({\exists_{X} P}) \iso \exists_{X}((\sigma \times \id)^{*} P)$,
corresponding to the usual substitution rule for quantifiers. Somewhat
surprisingly, this does not always hold; we always have a map
$$\exists_{X}((\sigma \times \id)^{*} P) \to \sigma^*({\exists_{X} P})$$
coming from adjoint yoga, but this map is not necessarily invertible!
This leads us to the main topic of this page: the **Beck-Chevalley
conditions** are a set of properties that ensure that the aforementioned
map is invertible, which in turn ensures that our quantifiers are stable
under substitution.

## Left Beck-Chevalley conditions

A **left Beck-Chevalley condition** characterises well-behaved left
adjoints to base change. Typically, this is done by appealing to
properties of base change, but we opt to use a a more local definition
in terms of [[cartesian|cartesian map]] and [[cocartesian|cocartesian
map]] maps. This has the benefit of working in displayed categories that
may be missing some cartesian maps.

:::{.definition #left-beck-chevalley-condition}
Explicitly, a square $fg = hk$ in $\cB$ satisfies the left
Beck-Chevalley condition if for every square $f'g' = h'k'$ over $fg =
hk$, if $g'$ and $h'$ are cartesian and $f'$ is cocartesian, then $k'$
is cocartesian.  This is best understood diagrammatically, so consider
the diagram below:

~~~{.quiver}
\begin{tikzcd}
  {A'} &&& {C'} \\
  & {B'} &&& {D'} \\
  A &&& C \\
  & B &&& D
  \arrow["{\mathrm{cocart}}"{description}, color={rgb,255:red,92;green,92;blue,214}, from=1-1, to=1-4]
  \arrow["{\mathrm{cart}}"{description}, color={rgb,255:red,214;green,92;blue,92}, from=1-1, to=2-2]
  \arrow[from=1-1, lies over, to=3-1]
  \arrow["{\mathrm{cart}}"{description}, color={rgb,255:red,214;green,92;blue,92}, from=1-4, to=2-5]
  \arrow[from=1-4, lies over, to=3-4]
  \arrow["{\mathrm{cocart}}"{description}, color={rgb,255:red,214;green,92;blue,92}, from=2-2, to=2-5]
  \arrow[from=2-2, lies over, to=4-2]
  \arrow[from=2-5, lies over, to=4-5]
  \arrow["k"{description}, from=3-1, to=3-4]
  \arrow["g"{description}, from=3-1, to=4-2]
  \arrow["h"{description}, from=3-4, to=4-5]
  \arrow["f"{description}, from=4-2, to=4-5]
\end{tikzcd}
~~~

If all the morphisms marked in red are (co)cartesian, then the morphism
marked in blue must be cocartesian. To put things more succinctly,
cocartesian morphisms can be pulled back along pairs of cartesian
morphisms.
:::


<!--
```agda
module _
  {o ℓ o' ℓ'}
  {B : Precategory o ℓ}
  (E : Displayed B o' ℓ')
  where
  open Cat.Reasoning B
  open Cat.Displayed.Reasoning E
```
-->

```agda
  left-beck-chevalley
    : {a b c d : Ob}
    → (f : Hom b d) (g : Hom a b) (h : Hom c d) (k : Hom a c)
    → (p : f ∘ g ≡ h ∘ k)
    → Type _
  left-beck-chevalley {a} {b} {c} {d} f g h k p =
    ∀ {a' : Ob[ a ]} {b' : Ob[ b ]} {c' : Ob[ c ]} {d' : Ob[ d ]}
    → {f' : Hom[ f ] b' d'} {g' : Hom[ g ] a' b'}
    → {h' : Hom[ h ] c' d'} {k' : Hom[ k ] a' c'}
    → f' ∘' g' ≡[ p ] h' ∘' k'
    → is-cocartesian E f f' → is-cartesian E g g'
    → is-cartesian E h h' → is-cocartesian E k k'
```

## Beck-Chevalley and left adjoints to base change

This may seem somewhat far removed from the intuition we provided
earlier, but it turns out that the two notions are equivalent! Proving
this is a bit involved though, so we will need some intermediate lemmas
first.

<!--
```agda
module _
  {o ℓ o' ℓ'}
  {B : Precategory o ℓ}
  {E : Displayed B o' ℓ'}
  where
  open Cat.Reasoning B

  open Cat.Displayed.Reasoning E
  open Cat.Displayed.Morphism E

  module Fib = Cat.Displayed.Fibre.Reasoning E
  open Functor
  open _=>_

  private variable
    a b c d : Ob
    f g h k : Hom a b
```
-->

In particular, let us consider a commuting square of morphisms $fg = hk$
in $\cB$ such that we have cocartesian lifts over $f, k$, and cartesian
lifts over $g, h$, as in the following diagram.

~~~{.quiver}
\begin{tikzcd}
  && C \\
  A &&&& D \\
  && B
  \arrow["h"{description}, from=1-3, to=2-5]
  \arrow["k"{description}, from=2-1, to=1-3]
  \arrow["g"{description}, from=2-1, to=3-3]
  \arrow["f"{description}, from=3-3, to=2-5]
\end{tikzcd}
~~~

```agda
  module _
    {a b c d}
    {f : Hom b d} {g : Hom a b} {h : Hom c d} {k : Hom a c}
    (p : f ∘ g ≡ h ∘ k)
    (f^! : ∀ b' → Cocartesian-lift E f b')
    (g^* : ∀ b' → Cartesian-lift E g b')
    (h^* : ∀ c' → Cartesian-lift E h c')
    (k^! : ∀ c' → Cocartesian-lift E k c')
    where
```

<!--
```agda
    private
      module f (b' : Ob[ b ]) where
        open Cocartesian-lift (f^! b') renaming (y' to ^!_; lifting to ι) public

      module g (b' : Ob[ b ]) where
        open Cartesian-lift (g^* b') renaming (x' to ^*; lifting to π) public

      module h (d' : Ob[ d ]) where
        open Cartesian-lift (h^* d') renaming (x' to ^*; lifting to π) public

      module k (a' : Ob[ a ]) where
        open Cocartesian-lift (k^! a') renaming (y' to ^!_; lifting to ι) public
```
-->

Now, fix some $B' : \cE_{B}$. We can form the following immortal
pentagonal diagram by repeatedly taking lifts of $B'$ and
applying various universal properties.

~~~{.quiver}
\begin{tikzcd}
  & {h^*f_!(B')} && {k_!g^*(B')} \\
  \\
  {g^*B'} & C && C & {f_!B'} \\
  && {B'} \\
  A &&&& D \\
  && B
  \arrow["{((\iota \circ \pi)_{!})^*}"{description}, curve={height=12pt}, to=1-2, from=1-4]
  \arrow["{((\iota \circ \pi)^{*})_!}"{description}, curve={height=-12pt}, to=1-2, from=1-4]
  \arrow[lies over, from=1-2, to=3-2]
  \arrow[lies over, from=1-4, to=3-4]
  \arrow["{(\iota \circ \pi)_{!}}"{description}, from=1-4, to=3-5]
  \arrow["{(\iota \circ \pi)^{*}}"{description}, from=3-1, to=1-2]
  \arrow["\pi"{description}, from=3-1, to=4-3]
  \arrow[lies over, from=3-1, to=5-1]
  \arrow["\id"{description}, from=3-2, to=3-4]
  \arrow["h"{description}, from=3-4, to=5-5]
  \arrow[lies over, from=3-5, to=5-5]
  \arrow["\iota"{description}, from=4-3, to=3-5]
  \arrow[lies over, from=4-3, to=6-3]
  \arrow["k"{description}, from=5-1, to=3-2]
  \arrow["g"{description}, from=5-1, to=6-3]
  \arrow["f"{description}, from=6-3, to=5-5]
\end{tikzcd}
~~~

```agda
    private
      h^*-interp : ∀ b' → Hom[ k ] (g.^* b') (h.^* (f.^! b'))
      h^*-interp b' = h.universal' (f.^! b') (sym p) (f.ι b' ∘' g.π b')

      k^!-interp : ∀ b' → Hom[ h ] (k.^! g.^* b') (f.^! b')
      k^!-interp b' = k.universal' (g.^* b') (sym p) (f.ι b' ∘' g.π b')

      h^*k^!-comparison : ∀ b' → Hom[ id ] (k.^! (g.^* b')) (h.^* (f.^! b'))
      h^*k^!-comparison b' = h.universalv (f.^! b') (k^!-interp b')

      k^!h^*-comparison : ∀ b' → Hom[ id ] (k.^! (g.^* b')) (h.^* (f.^! b'))
      k^!h^*-comparison b' = k.universalv (g.^* b') (h^*-interp b')

      comparison-square : ∀ {b'} → h^*k^!-comparison b' ≡ k^!h^*-comparison b'
      comparison-square {b'} = h.uniquep₂ (f.^! b') _ _ (idr _) _ _
        (h.commutesv _ _) (k.uniquep (g.^* b') _ (idr _) _ _
          (pullr[] _ (k.commutesv (g.^* b') _)
            ∙[] h.commutesp _ (sym p) (f.ι b' ∘' g.π b')))
```

The immortal pentagon diagram above *almost* lets us "interpolate" $B'$
around the entire square in the base, but there is a conspicuous gap
between $h^*f_!(B')$ and $k_!g^*(B')$; this is precisely the missing map
that the Beck-Chevalley condition ought to give us.

```agda
    left-beck-chevalley→comparison-invertible
      : left-beck-chevalley E f g h k p
      → ∀ {b'} → is-invertible↓ (h^*k^!-comparison b')
```

First, observe that the map $(\iota \circ \pi)^{*}$ fits into a square
with 2 cartesian sides and 1 cocartesian side; so we can apply
Beck-Chevalley to deduce that it is cocartesian.

~~~{.quiver}
\begin{tikzcd}
  &&& {h^*k_!(B')} \\
  {g^*(B')} &&&&& {f_!(B')} \\
  && {B'} & C \\
  A &&&&& D \\
  && B
  \arrow["\pi"{description}, color={rgb,255:red,214;green,92;blue,92}, from=1-4, to=2-6]
  \arrow[from=1-4, to=3-4]
  \arrow["{(\iota \circ \pi)^*}"{description}, color={rgb,255:red,92;green,92;blue,214}, from=2-1, to=1-4]
  \arrow["\pi"{description}, color={rgb,255:red,214;green,92;blue,92}, from=2-1, to=3-3]
  \arrow[lies over, from=2-1, to=4-1]
  \arrow[lies over, from=2-6, to=4-6]
  \arrow["\iota"{description}, color={rgb,255:red,214;green,92;blue,92}, from=3-3, to=2-6]
  \arrow[lies over, from=3-3, to=5-3]
  \arrow["h"{description}, from=3-4, to=4-6]
  \arrow["k"{description}, from=4-1, to=3-4]
  \arrow["g"{description}, from=4-1, to=5-3]
  \arrow["f"{description}, from=5-3, to=4-6]
\end{tikzcd}
~~~

```agda
    left-beck-chevalley→comparison-invertible left-bc {b'} =
      make-invertible↓ comparison⁻¹ left-beck-invl left-beck-invr where
        h^*-interp-cocartesian : is-cocartesian E k (h^*-interp b')
        h^*-interp-cocartesian = left-bc (symP (h.commutesp (f.^! b') (sym p) _))
          (f.cocartesian b')
          (g.cartesian b')
          (h.cartesian (f.^! b'))

        module h^*-interp = is-cocartesian h^*-interp-cocartesian
```

Notably, this lets us factor the map $\iota :
\cE_{k}(g^{*}(B'),k_{!}g^{*}(B'))$ to get a vertical map
$\cE(h^{*}f_{!}(B'), k_{!}g^{*}(B'))$ that fits neatly into the gap in
the pentagon.

```agda
        comparison⁻¹ : Hom[ id ] (h.^* (f.^! b')) (k.^! (g.^* b'))
        comparison⁻¹ = h^*-interp.universalv (k.ι (g.^* b'))
```

We can show that our putative inverse is a left inverse of the
comparison map by appealing to uniqueness of both maps into and maps out
of $h^*f_!(B')$, as it is simultaneously a cartesian and a cocartesian
lift. This yields the following hexagonal goal, which we can show
commutes by a short diagram chase.

~~~{.quiver}
\begin{tikzcd}
  && {k_{!}g^{*}(B')} \\
  {h^{*}f_{!}(b')} &&&& {h^{*}f_{!}(b')} \\
  \\
  {g^{*}(B')} &&&& {f_!(B')} \\
  && {B'}
  \arrow["{((\iota \circ \pi)_{!})^{*}}"{description}, from=1-3, to=2-5]
  \arrow["{\iota_!}"{description}, from=2-1, to=1-3]
  \arrow["\pi"{description}, from=2-5, to=4-5]
  \arrow["{(\iota \circ \pi)^*}"{description}, from=4-1, to=2-1]
  \arrow["\pi"{description}, from=4-1, to=5-3]
  \arrow["\iota"{description}, from=5-3, to=4-5]
\end{tikzcd}
~~~

```agda
        left-beck-invl : h^*k^!-comparison b' ∘' comparison⁻¹ ≡[ idl id ] id'
        left-beck-invl = symP $ h.uniquep₂ _ _ _ (elimr (idl id)) _ _ (idr' _)
          $ symP $ h^*-interp.uniquep₂ _ _ _ _ _ (h.commutesp _ (sym p) (f.ι b' ∘' g.π b'))
          $ begin
          (h.π (f.^! b') ∘' h^*k^!-comparison b' ∘' comparison⁻¹) ∘' h^*-interp b' ≡[]⟨ pullr[] _ (pullr[] _ (h^*-interp.commutesv _)) ⟩
          h.π (f.^! b') ∘' h^*k^!-comparison b' ∘' k.ι (g.^* b')                   ≡[]⟨ pulll[] _ (h.commutesv (f.^! b') _) ⟩
          k^!-interp b' ∘' k.ι (g.^* b')                                           ≡[]⟨ k.commutesp _ (sym p) (f.ι b' ∘' g.π b') ⟩
          f.ι b' ∘' g.π b'                                                         ∎[]
```

The right inverse is a bit trickier. We start by appealing to the
uniqueness of maps into the cocartesian lift $k_{!}g^{*}(B')$, which
reduces the goal to the following diagram.

~~~{.quiver}
\begin{tikzcd}
  {f_{!}g^{*}(B')} && {h^{*}f_{!}(B')} \\
  \\
  {g^{*}} && {f_{!}g^{*}(B')}
  \arrow["{((\iota \circ \pi)_{!})^{*}}"{description}, from=1-1, to=1-3]
  \arrow["{\iota_!}"{description}, from=1-3, to=3-3]
  \arrow["\iota"{description}, from=3-1, to=1-1]
  \arrow["\iota"{description}, from=3-1, to=3-3]
\end{tikzcd}
~~~

If we go back to the immortal pentagon, we will notice that we actually
have two equivalent ways of writing the comparison map: we can either
apply the universal property of $k$ followed by the universal property
of $h$, or we can apply the universal property of $k$ followed by $h$.
This means that we have:

$$((\iota \circ \pi)_{!})^{*} \circ \iota = ((\iota \circ \pi)^{*})_{!} \circ \iota = (\iota \circ \pi)^{*}$$

This reduces the problem to showing that $\iota_{!} \circ (\iota \circ
\pi)^{*} = \iota$, which follows immediately from commutativity of
$(\iota \circ \pi)^{*}$ as a cocartesian map.

```agda
        left-beck-invr : comparison⁻¹ ∘' h^*k^!-comparison b' ≡[ idl id ] id'
        left-beck-invr = symP $ k.uniquep₂ _ _ _ _ _ _ (idl' _) $ begin
          (comparison⁻¹ ∘' h^*k^!-comparison b') ∘' k.ι (g.^* b')  ≡[]⟨ (refl⟩∘'⟨ comparison-square) ⟩∘'⟨refl ⟩
          (comparison⁻¹ ∘' k^!h^*-comparison b') ∘' k.ι (g.^* b')  ≡[]⟨ pullr[] _ (k.commutesv (g.^* b') _) ⟩
          comparison⁻¹ ∘' h^*-interp b'                            ≡[]⟨ h^*-interp.commutesv _ ⟩
          k.ι (g.^* b')                                            ∎[]
```

We shall now show the converse of our previous statement: if the
comparison map from earlier is invertible, then the Beck-Chevalley
property holds for our square. At a first glance, this seems a bit
tricky: the Beck-Chevalley property talks about an arbitrary square of
(co)cartesian morphisms, but the comparison map only refers to a
*particular* square.  Luckily, we can reduce the Beck-Chevalley property
to checking if the interpolation map $(\iota \circ \pi)^{*}$ is
cocartesian.

```agda
    interp-cocartesian→left-beck-chevalley
      : (∀ b' → is-cocartesian E k (h^*-interp b'))
      → left-beck-chevalley E f g h k p
```

<details>
<summary>
The full proof is rather tedious, so we shall only present a short
sketch. The key fact we shall use is that the (co)domains of
(co)cartesian morphisms over the same map in the base are vertically
isomorphic. This lets us connect an arbitrary square of (co)cartesian
morphisms to the square formed via lifts with a bunch of vertical isos,
which lets us transfer the Beck-Chevalley property.
</summary>

```agda
    interp-cocartesian→left-beck-chevalley h^*interp-cocart {a'} {b'} {c'} {d'} {f'} {g'} {h'} {k'} q f'-cocart g'-cart h'-cart =
      coe0→1 (λ i → is-cocartesian E ((cancell (idl _) ∙ idr _) i) (square i))
        (cocartesian-∘ E (iso→cocartesian E γ) $
         cocartesian-∘ E (iso→cocartesian E h^*δ) $
         cocartesian-∘ E (h^*interp-cocart b') $
         iso→cocartesian E α)
      where
        open _≅[_]_
        module h' = is-cartesian h'-cart

        α : a' ≅↓ g.^* b'
        α = cartesian-domain-unique E g'-cart (g.cartesian b')

        γ : h.^* d' ≅↓ c'
        γ = cartesian-domain-unique E (h.cartesian d') h'-cart

        δ : (f.^! b') ≅↓ d'
        δ = cocartesian-codomain-unique E (f.cocartesian b') f'-cocart

        h^*δ : h.^* (f.^! b') ≅↓ h.^* d'
        h^*δ = make-vertical-iso
          (h.universal' d' id-comm (δ .to' ∘' h.π (f.^! b')))
          (h.universal' (f.^! b') id-comm (δ .from' ∘' h.π d'))
          (h.uniquep₂ _ _ _ _ _ _
            (   pulll[] _ (h.commutesp _ id-comm _)
            ∙[] pullr[] _ (h.commutesp _ id-comm _)
            ∙[] cancell[] _ (δ .invl'))
            (idr' _))
          (h.uniquep₂ _ _ _ _ _ _
            (   pulll[] _ (h.commutesp _ id-comm _)
            ∙[] pullr[] _ (h.commutesp _ id-comm _)
            ∙[] cancell[] _ (δ .invr'))
            (idr' _))

        abstract
          square : γ .to' ∘' h^*δ .to' ∘' h^*-interp b' ∘' α .to' ≡[ cancell (idl _) ∙ idr _ ] k'
          square = h'.uniquep₂ _ _ _ _ _
            (begin
              _ ≡[]⟨ pulll[] _ (h'.commutesp (idr _) _) ⟩
              _ ≡[]⟨ pulll[] _ (h.commutesp _ id-comm _) ⟩
              _ ≡[]⟨ pullr[] _ (pulll[] _ (h.commutesp _ (sym p) _)) ⟩
              _ ≡[]⟨ pulll[] _ (pulll[] _ (f.commutesp _ (idl _) _)) ⟩
              _ ≡[]⟨ pullr[] _ (g.commutesp _ (idr _) _) ⟩
              _ ∎[])
            (symP q)
```
</details>

On to the converse! Suppose that the comparison map is invertible, and
denote the inverse $\alpha$. By our previous lemma, it suffices to show
that the interpolant $(\iota \circ \pi)^{*}$ is cocartesian.  Moreover,
cocartesian maps are stable under precomposition of isomorphisms, so it
suffices to show that $\alpha \circ (\iota \circ \pi)^{*}$ is
cocartesian.  A short calculation reveals that:

$$
\begin{align*}
  ((\iota \circ\ \pi)_{!})^{*} \circ \alpha \circ (\iota \circ \pi)^{*}
  &= (\iota \circ \pi)^{*} \\
  &= ((\iota \circ\ \pi)^{*})_{!} \circ \iota \\
  &= ((\iota \circ\ \pi)_{!})^{*} \circ \iota \\
\end{align*}
$$

Finally, since $((\iota \circ\ \pi)_{!})^{*}$ is monic, we have $\alpha
\circ (\iota \circ \pi)^{*} = \iota$, which is cocartesian!

```agda
    comparison-invertible→left-beck-chevalley
      : (∀ b' → is-invertible↓ (h^*k^!-comparison b'))
      → left-beck-chevalley E f g h k p
    comparison-invertible→left-beck-chevalley comparison-inv =
      interp-cocartesian→left-beck-chevalley λ b' →
        cocartesian-vertical-section-stable E
          (k.cocartesian (g.^* b'))
          (invertible[]→from-has-retract[] (comparison-inv b'))
          (comparison-inv-interp b')
      where
        module comparison b' = is-invertible[_] (comparison-inv b')

        abstract
          comparison-inv-interp : ∀ b' → comparison.inv' b' ∘' h^*-interp b' ≡[ idl k ] k.ι (g.^* b')
          comparison-inv-interp b' =
            cast[] $ invertible[]→monic[] (comparison-inv b') _ _ _ $ begin
            h^*k^!-comparison b' ∘' comparison.inv' b' ∘' h^*-interp b' ≡[]⟨ cancell[] _ (comparison.invl' b') ⟩
            h^*-interp b'                                               ≡[]˘⟨ k.commutesv (g.^* b') (h^*-interp b') ⟩
            k^!h^*-comparison b' ∘' k.ι (g.^* b')                       ≡[]˘⟨ comparison-square ⟩∘'⟨refl ⟩
            h^*k^!-comparison b' ∘' k.ι (g.^* b')                       ∎[]
```

Now that we have our arsenal of lemmas, we shall tackle our original
question: how are adjoints to base change related to our formulation of
Beck-Chevalley? To start, suppose that we have a commutative square $fg
= hk$, and left adjoints $f_{!}$ and $k_{!}$ to base change along $f$
and $k$, respectively. Moreover, recall that [cocartesian lifts are left
adjoints to base change], so we have cocartesian lifts along $f$ and
$k$.

[cocartesian lifts are left adjoints to base change]: Cat.Displayed.Cocartesian.Weak.html#weak-cocartesian-morphisms-as-left-adjoints-to-base-change

```agda
  module _
    (E-fib : Cartesian-fibration E)
    {Lᶠ : Functor (Fibre E b) (Fibre E d)}
    {Lᵏ : Functor (Fibre E a) (Fibre E c)}
    (Lᶠ⊣f^* : Lᶠ ⊣ base-change E E-fib f)
    (Lᵏ⊣k^* : Lᵏ ⊣ base-change E E-fib k)
    (p : f ∘ g ≡ h ∘ k)
```


<!--
```agda
    where
      open Cartesian-fibration E E-fib
      private
        module Lᶠ where
          open Functor Lᶠ public
          open _⊣_ Lᶠ⊣f^* public

        module Lᵏ where
          open Cat.Functor.Reasoning Lᵏ public
          open _⊣_ Lᵏ⊣k^* public

        module f (b' : Ob[ b ]) where
          open Cocartesian-lift (left-adjoint→cocartesian-lift E E-fib Lᶠ⊣f^* b')
            renaming (y' to ^!_; lifting to ι)
            public

        module k (b' : Ob[ a ]) where
          open Cocartesian-lift (left-adjoint→cocartesian-lift E E-fib Lᵏ⊣k^* b')
            renaming (y' to ^!_; lifting to ι)
            public
```
-->

The commutative square $fg = hk$ lifts to a natural iso $g^{*}f^{*} \iso
k^{*}f^{*}$, which yields a natural transformation $k_{!}g^{*} \to
h^{*}f_{!}$ via the calculus of [[mates]].

```agda
      private
        comparison : ∀ b' → Hom[ id ] (k.^! (g ^* b')) (h ^* (f.^! b'))
        comparison b' =
          mate Lᶠ⊣f^* Lᵏ⊣k^*
            (base-change E E-fib g) (base-change E E-fib h)
            (Isoⁿ.to (base-change-square-ni E E-fib p)) .η b'
```

Moreover, the comparison map we get from the mate of $g^{*}f^{*} \iso
k^{*}f^{*}$ is the same comparison map we defined in the previous
section.

```agda
        opaque
          unfolding base-change-square
          mate-comparison
            : ∀ {b'}
            → comparison b' ≡ π*.universalv (k.universal' _ (sym p) (f.ι b' ∘' π* g b'))
```

<details>
<summary>
This essentially *has* to hold, as there are so many universal
properties floating around. Unfortunately, the proof is a bit more
tedious than one would hope, so we omit the details.
</summary>

```agda
          mate-comparison {b'} = π*.uniquev (comparison b') $ k.uniquep _ _ _ _ _ $
            begin
              _ ≡[]⟨ extendr[] _ (Fib.extendrf (Fib.pullrf (left-adjoint→cocartesian-lift-natural E E-fib Lᵏ⊣k^* _))) ⟩
              _ ≡[]⟨ extendr[] _ (Fib.pullrf (pulll[] _ (left-adjoint→cocartesian-lift-natural E E-fib Lᵏ⊣k^* _))) ⟩
              _ ≡[]⟨ extendr[] _ (extendl[] _ (pulll[] _ (left-adjoint→counit-commutesv E E-fib Lᵏ⊣k^*))) ⟩
              _ ≡[]⟨ pullr[] _ (pulll[] _ (π*.commutesv _)) ⟩
              _ ≡[]⟨ pulll[] _ (π*.commutesp (sym p) _) ⟩
              _ ≡[]⟨ pullr[] _ (π*.commutesp id-comm _) ⟩
              _ ≡[]⟨ pulll[] _ (wrap (idr f)) ⟩
              _ ∎[]
```
</details>

We can combine this with our previous results about squares of
(co)cartesian lifts to deduce that the Beck-Chevalley condition holds if
and only if the comparison map derived from the aforementioned mate is
invertible.

```agda
      left-beck-chevalley→mate-invertible
        : left-beck-chevalley E f g h k p
        → ∀ {b'} → is-invertible↓ (comparison b')
      left-beck-chevalley→mate-invertible left-bc =
        subst is-invertible↓ (sym mate-comparison) $
        left-beck-chevalley→comparison-invertible p
          (left-adjoint→cocartesian-lift E E-fib Lᶠ⊣f^*)
          (E-fib g)
          (E-fib h)
          (left-adjoint→cocartesian-lift E E-fib Lᵏ⊣k^*)
          left-bc

      mate-invertible→left-beck-chevalley
        : (∀ b' → is-invertible↓ (comparison b'))
        → left-beck-chevalley E f g h k p
      mate-invertible→left-beck-chevalley mate-inv =
        comparison-invertible→left-beck-chevalley p
          (left-adjoint→cocartesian-lift E E-fib Lᶠ⊣f^*)
          (E-fib g)
          (E-fib h)
          (left-adjoint→cocartesian-lift E E-fib Lᵏ⊣k^*)
          (λ b' → subst is-invertible↓ mate-comparison (mate-inv b'))
```

## Right Beck-Chevalley conditions

Left Beck-Chevalley conditions require stability of cocartesian maps
under cartesian maps. We can dualize this to obtain the **right
Beck-Chevalley conditions**, which ensures stability of cartesian maps
under pushforward along cocartesian maps. As before, this is best
understood diagrammatically:

~~~{.quiver}
\begin{tikzcd}
	{A'} &&& {D'} \\
	& {B'} &&& {C'} \\
	A &&& B \\
	& C &&& D
	\arrow["{\mathrm{cart}}"{description}, color={rgb,255:red,214;green,92;blue,92}, from=1-1, to=1-4]
	\arrow["{\mathrm{cocart}}"{description}, color={rgb,255:red,214;green,92;blue,92}, from=1-1, to=2-2]
	\arrow[lies over, from=1-1, to=3-1]
	\arrow["{\mathrm{cocart}}"{description}, color={rgb,255:red,214;green,92;blue,92}, from=1-4, to=2-5]
	\arrow[lies over, from=1-4, to=3-4]
	\arrow["{\mathrm{cart}}"{description}, color={rgb,255:red,92;green,92;blue,214}, from=2-2, to=2-5]
	\arrow[lies over, from=2-2, to=4-2]
	\arrow[lies over, from=2-5, to=4-5]
	\arrow["g"{description}, from=3-1, to=3-4]
	\arrow["k"{description}, from=3-1, to=4-2]
	\arrow["f"{description}, from=3-4, to=4-5]
	\arrow["h"{description}, from=4-2, to=4-5]
\end{tikzcd}
~~~

<!--
```agda
module _
  {o ℓ o' ℓ'}
  {B : Precategory o ℓ}
  (E : Displayed B o' ℓ')
  where
  open Cat.Reasoning B
  open Cat.Displayed.Reasoning E
```
-->

```agda
  right-beck-chevalley
    : {a b c d : Ob}
    → (f : Hom b d) (g : Hom a b) (h : Hom c d) (k : Hom a c)
    → (p : f ∘ g ≡ h ∘ k)
    → Type _
  right-beck-chevalley {a} {b} {c} {d} f g h k p =
    ∀ {a' : Ob[ a ]} {b' : Ob[ b ]} {c' : Ob[ c ]} {d' : Ob[ d ]}
    → {f' : Hom[ f ] b' d'} {g' : Hom[ g ] a' b'}
    → {h' : Hom[ h ] c' d'} {k' : Hom[ k ] a' c'}
    → f' ∘' g' ≡[ p ] h' ∘' k'
    → is-cartesian E g g'
    → is-cocartesian E f f' → is-cocartesian E k k'
    → is-cartesian E h h'
```
