<!--
```agda
{-# OPTIONS --lossy-unification -vtc.def:20 #-}
open import Cat.Diagram.Pullback.Properties
open import Cat.Morphism.Factorisation
open import Cat.Morphism.StrongEpi
open import Cat.Instances.Functor
open import Cat.Instances.Product
open import Cat.Diagram.Pullback
open import Cat.Diagram.Product
open import Cat.Bi.Base
open import Cat.Prelude
open import Cat.Regular

import Cat.Displayed.Instances.Subobjects as Sub
import Cat.Functor.Bifunctor as Bifunctor
import Cat.Regular.Image as Img
import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Bi.Instances.Relations
  {o ℓ} {C : Precategory o ℓ} (reg : is-regular C) where
```

<!--
```agda
open Pullback
open is-regular reg
open Binary-products C lex.products
open Factorisation
open Cr C
open Sub C
open Img reg
```
-->

# Relations in a regular category

This module defines the [[bicategory]] of relations in arbitrary [regular
categories] --- categories with [[pullback-stable]] [[image
factorisations]]. **Relations** $\phi : a \rel b$ between objects $a, b
: \cC$ can be defined in arbitrary categories^[A relation $\phi : a \rel
b$ is a span $a \xot{f} r \xto{g} b$ such that $f, g$ are jointly
monic.], but in finite-products categories, the definition takes an
especially pleasant form: A relation $\phi : a \rel b$ is a [subobject]
of the [Cartesian product] $a \times b$.

[regular categories]: Cat.Regular.html
[subobject]: Cat.Displayed.Instances.Subobjects.html
[Cartesian product]: Cat.Diagram.Product.html

Unlike the more general [bicategory of spans] $\Spans_\cC$, which can be
defined for an arbitrary category with [[pullbacks]] $\cC$, the
definition of a bicategory of _relations_ does need an honest regular
category. Before we get into the details of the construction, let's
introduce some notation:

[bicategory of spans]: Cat.Bi.Instances.Spans.html

Following [@Elephant], relations will be denoted using lowercase Greek
letters: we will write a relation $\phi : R \mono A \times B$ as $\phi :
A \rel B$, leaving its domain $R$ implicit. Any relation $\phi$ can be
factored^[Recall that, for $\phi : A \to B \times C$, we have a
tautological decomposition $\phi = \langle \pi_1\phi, \pi_2\phi
\rangle$.] into morphisms $s : R \to A$ and $t : R \to B$ --- we shall
say that the pair $(s, t)$ **tabulates** $\phi$.

```agda
_↬_ : Ob → Ob → Type (o ⊔ ℓ)
_↬_ a b = Subobject (a ⊗₀ b)
```

For intuition, a tabulation $(f, g) : R \mono A \times B$ of $\phi : A
\rel B$ exhibits $R$ as the _object of witnesses_ for $\phi$, with the
maps $f$ and $g$ determining the "source" and "target" of each witness.
The condition that $(f, g)$ be a subobject ensures we have _at most_ one
witness in $r$ for a $\phi$-related pair $a, b$. When speaking
informally, we may regard the maps $(f, g)$ as exhibiting $R$ as the
total space of a family over $A \times B$; From that point of view, it's
natural to write the fibre over some $(x, y)$ as $R(x, y).$^[Points in
this fibre is a morphism $p : \Gamma \to R$ satisfying $fp = x$ and $gp
= y$.]

<!--
```
module Relation {a b} (r : _↬_ a b) where
  rel : Ob
  rel = r .domain

  src : Hom rel a
  src = π₁ ∘ r .map

  tgt : Hom rel b
  tgt = π₂ ∘ r .map
```
-->

The identity relation $\iota : a \rel a$ is tabulated by the pair $(\id,
\id) : A \mono A \times A$, which is easily seen to be a subobject.

```agda
id-rel : ∀ {a} → a ↬ a
id-rel {a} .domain = a
id-rel {a} .map = δ
id-rel {a} .monic g h x = by-π₁ $
  ⟨ g , g ⟩       ≡˘⟨ ⟨⟩∘ g ∙ ap₂ ⟨_,_⟩ (idl g) (idl g) ⟩
  ⟨ id , id ⟩ ∘ g ≡⟨ x ⟩
  ⟨ id , id ⟩ ∘ h ≡⟨ ⟨⟩∘ h ∙ ap₂ ⟨_,_⟩ (idl h) (idl h) ⟩
  ⟨ h , h ⟩       ∎
```

Relational composition is slightly more intricate. Given relations $(s,
t) : R \mono B \times C$, $(s', t') : S \mono A \times B$, we may
compose them at the level of spans by taking the pullback

~~~{.quiver .tall-1}
\[\begin{tikzcd}
  && {R \times_BS} \\
  & S && R \\
  A && B && C
  \arrow[from=1-3, to=2-4]
  \arrow["s", from=2-4, to=3-3]
  \arrow["{t'}"', from=2-2, to=3-3]
  \arrow[from=1-3, to=2-2]
  \arrow["\lrcorner"{anchor=center, pos=0.125, rotate=-45}, draw=none, from=1-3, to=3-3]
  \arrow["{s'}"', from=2-2, to=3-1]
  \arrow["t", from=2-4, to=3-5]
\end{tikzcd}\]
~~~

whose generalised elements are pairs $(a, b) : \Gamma \to R \times S$
satisfying $t'(b) = s(a)$. Thinking of $(s, t)$ and $(s', t')$ as
bundles over their codomain, the fibre of $R \times_B S$ over $x, y$ is
the "sum type"

$$\sum_{b : B} (S(x, b) \times R(b, y))$$

which is _not_ a subobject of $A \times C$, since there might be
multiple choices of "bridge" element $b$! As a concrete failure, think
in $\Sets$, and consider composing the implication order on $\{0,1\}$
with its converse: The fibre over $(0, 0)$ has distinct elements
corresponding to $0 \le 0 \ge 0$ and $0 \le 1 \ge 0$.

```agda
∘-rel : ∀ {a b c} → b ↬ c → a ↬ b → a ↬ c
∘-rel {a} {b} {c} φ ψ = composite module ∘-rel where
  module φ = Relation φ
  module ψ = Relation ψ

  inter : Pullback C ψ.tgt φ.src
  inter = lex.pullbacks _ _
```

Can we fix it? Yes! Since $\cC$ is a regular category, our morphism
$(s', t) : R \times_B S \to A \times C$ factors as a [strong
epimorphism] onto its image

$$
R \times_B S \epi \im(s',t) \mono A \times B\text{,}
$$

which is the _free subobject_ generated by $(s', t)$. Having a nice
instrumental property is not a guarantee that this is the correct
definition, but it _does_ make it more likely to be correct.^[From a
point of view informed by parametricity, one might argue that this is
not only the correct move, but the _only possible_ way of turning a map
into a subobject.]

[strong epimorphism]: Cat.Morphism.StrongEpi.html

```agda
  it : Hom (inter .apex) (a ⊗₀ c)
  it = ⟨ ψ.src ∘ inter .p₁ , φ.tgt ∘ inter .p₂ ⟩

  composite : a ↬ c
  composite = Im it
```

<!--
```agda
∘-rel-assoc
  : ∀ {a b c d}
  → (φ : c ↬ d)
  → (ψ : b ↬ c)
  → (χ : a ↬ b)
  → (∘-rel φ (∘-rel ψ χ)) Sub.≅ (∘-rel (∘-rel φ ψ) χ)
∘-rel-assoc {a} {b} {c} {d} r s t = done where
  private
    module rs = ∘-rel r s
    module st = ∘-rel s t
    module [rs]t = ∘-rel (∘-rel r s) t
    module r[st] = ∘-rel r (∘-rel s t)
    v₂ = rs.inter .p₂
    v₁ = rs.inter .p₁

    u₂ = st.inter .p₂
    u₁ = st.inter .p₁
    open Relation r renaming (src to r₁ ; tgt to r₂) hiding (rel)
    open Relation s renaming (src to s₁ ; tgt to s₂) hiding (rel)
    open Relation t renaming (src to t₁ ; tgt to t₂) hiding (rel)

    i : ∀ {x y} {f : Hom x y} → Hom im[ f ] y
    i = factor _ .forget

    q : ∀ {x y} {f : Hom x y} → Hom x im[ f ]
    q = factor _ .mediate

    ξ₁ = [rs]t.inter .p₁
    ξ₂ = [rs]t.inter .p₂

    ζ₁ = r[st].inter .p₁
    ζ₂ = r[st].inter .p₂

  X : Pullback C (rs.inter .p₁) (st.inter .p₂)
  X = lex.pullbacks (rs.inter .p₁) (st.inter .p₂)
  private module X = Pullback X renaming (p₂ to x₁ ; p₁ to x₂)
  open X using (x₂ ; x₁)
```
-->

## Associativity of relational composition

If we are to make a bicategory out of relations, then we need to get our
hands on an _associator_ morphism --- put more plainly, using that
$\Sub(A \times B)$ is a preorder, a proof that $(\phi\psi)\chi \cong
\phi(\psi\chi)$. Suppose our relations are given by $\chi = (t_1, t_2) :
T \mono A \times B$, $\psi = (s_1, s_2) : S \mono B \times C$, and $\phi
= (r_1, r_2) : R \mono C \times D$. We'll prove that this composition is
associative by exhibiting both $(\phi\psi)\chi$ and $\phi(\psi\chi)$ as
quotients of a larger, "unbiased" composition.

Put all your maps in order and form the huge pullback

~~~{.quiver .tall-2}
\[\begin{tikzcd}
  &&& X \\
  && {T \times_B S} && {S \times_C R} \\
  & T && S && R \\
  A && B && C && {D\text{.}}
  \arrow["{u_2}"', from=2-3, to=3-4]
  \arrow["{s_1}", from=3-4, to=4-3]
  \arrow["{t_2}"', from=3-2, to=4-3]
  \arrow["\lrcorner"{anchor=center, pos=0.125, rotate=-45}, draw=none, from=2-3, to=4-3]
  \arrow["{s_2}"', from=3-4, to=4-5]
  \arrow["{r_1}", from=3-6, to=4-5]
  \arrow["{r_2}"', from=3-6, to=4-7]
  \arrow["{t_1}", from=3-2, to=4-1]
  \arrow["{v_1}", from=2-5, to=3-4]
  \arrow["{v_2}"', from=2-5, to=3-6]
  \arrow["\lrcorner"{anchor=center, pos=0.125, rotate=-45}, draw=none, from=2-5, to=4-5]
  \arrow["{x_1}", from=1-4, to=2-3]
  \arrow["{x_2}"', from=1-4, to=2-5]
  \arrow["\lrcorner"{anchor=center, pos=0.125, rotate=-45}, draw=none, from=1-4, to=3-4]
  \arrow["{u_1}", from=2-3, to=3-2]
\end{tikzcd}\]
~~~

whose sheer size might warrant the reader take a moment, out of respect.
My claim is that the composite $(\phi\psi)\chi$ is tabulated by the
image of

$$
\langle t_1u_1x_1 , r_2v_2x_2 \rangle : X \to A \times D\text{.}
$$

Let's see how to get there.

```agda
  j : Hom (X .apex) (a ⊗₀ d)
  j = ⟨ t₁ ∘ u₁ ∘ x₁ , r₂ ∘ v₂ ∘ x₂ ⟩
```

Factor $\langle t_1u_1 , s_2u_2 \rangle$ as

$$R \times_B S \xepi{q} I \xmono{i} B \times D\text{;}$$

That's the composite $\phi\psi$. To then add on $\chi$, the first step
is to take the pullback

~~~{.quiver}
\[\begin{tikzcd}
  {I \times_B T} && T \\
  \\
  I && {B\text{,}}
  \arrow["{\pi_1i}"', from=3-1, to=3-3]
  \arrow["{\xi_1}"', from=1-1, to=3-1]
  \arrow["{\xi_2}", from=1-1, to=1-3]
  \arrow["{t_2}", from=1-3, to=3-3]
  \arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=1-1, to=3-3]
\end{tikzcd}\]
~~~

but note that we have $t_2u_1x_1 = \pi_1iqx_2$, so we can construct a
map $\alpha : X \to I \times_B T$ satisfying $\xi_1\alpha = u_1x_1$ and
$\xi_2\beta = qx_2$.

```agda
  α : Hom (X .apex) ([rs]t.inter .apex)
  α = [rs]t.inter .universal {p₁' = u₁ ∘ x₁} {p₂' = q ∘ x₂} comm where abstract
```

<!--
```agda
    comm : t₂ ∘ u₁ ∘ x₁ ≡ (π₁ ∘ i {f = rs.it}) ∘ q ∘ x₂
    comm = pulll (st.inter .square)
         ∙ pullr (sym (X .square))
         ∙ sym ( pulll (pullr (sym (factor _ .factors)))
               ∙ ap₂ _∘_ π₁∘⟨⟩ refl ∙ sym (assoc _ _ _))
```
-->

Now, both squares in the diagram below are pullbacks, so the large
rectangle is a pullback, too.

~~~{.quiver .tall-1}
\[\begin{tikzcd}
  X && {T \times_CS} && T \\
  \\
  {S \times_B R} && S && B
  \arrow["{u_1}", from=1-3, to=1-5]
  \arrow["{x_1}", from=1-1, to=1-3]
  \arrow["{x_2}"', from=1-1, to=3-1]
  \arrow["{v_1}"', from=3-1, to=3-3]
  \arrow["{s_1}"', from=3-3, to=3-5]
  \arrow["{t_2}", from=1-5, to=3-5]
  \arrow["{u_2}", from=1-3, to=3-3]
  \arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=1-1, to=3-3]
  \arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=1-3, to=3-5]
\end{tikzcd}\]
~~~

```agda
  rem₀ : is-pullback C (u₁ ∘ x₁) t₂ x₂ (s₁ ∘ v₁)
  rem₀ = pasting-left→outer-is-pullback
    (st.inter .has-is-pb)
    (rotate-pullback (X .has-is-pb))
    (pulll (st.inter .square) ∙ extendr (sym (X .square)))
```

Now, by definition, we have $\xi_1\alpha = u_1x_1$, and $s_1v_1$ is also
the source map $\pi_1iq : I \to B$ in the composite $\phi\psi$, so we
may rewrite the pullback rectangle as

~~~{.quiver .tall-1}
\[\begin{tikzcd}
  X && {I \times_C T} && I \\
  \\
  {S \times_B R} && T && {B\text{,}}
  \arrow["{\xi_1}", from=1-3, to=1-5]
  \arrow["\alpha", from=1-1, to=1-3]
  \arrow["{x_2}"', from=1-1, to=3-1]
	\arrow["q"', two heads, from=3-1, to=3-3]
  \arrow["{\pi_1i}"', from=3-3, to=3-5]
  \arrow["{t_2}", from=1-5, to=3-5]
  \arrow["{u_2}", from=1-3, to=3-3]
  \arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=1-3, to=3-5]
\end{tikzcd}\]
~~~

which, since the right square is a pullback, means the left one is, too;
Since $q$ is a strong epi, $\alpha$ is, too.

```agda
  abstract
    rem₁ : is-pullback C (ξ₁ ∘ α) t₂ x₂ ((π₁ ∘ i {f = rs.it}) ∘ q)
    rem₁ = transport
      (ap₂ (λ x y → is-pullback C x (Relation.tgt t) (X .p₁) y)
        (sym ([rs]t.inter .p₁∘universal))
        (sym (pullr (sym (factor rs.it .factors)) ∙ π₁∘⟨⟩))) rem₀


    α-is-pb : is-pullback C α ξ₂ x₂ q
    α-is-pb = pasting-outer→left-is-pullback ([rs]t.inter .has-is-pb) rem₁ ([rs]t.inter .p₂∘universal)

  α-cover : is-strong-epi C α
  α-cover = stable _ _ (out! {pa = is-strong-epi-is-prop C _} (factor rs.it .mediate∈E)) α-is-pb
```

The purpose of all this calculation is the following: Postcomposing with
a strong epimorphism preserves images, so the image of $\langle
t_1\xi_1, \pi_2i\xi_2 \rangle$, which tabulates $(\phi\psi)\chi$, will
be the same as that of

$$
\langle t_1\xi_1 , \pi_2i\xi_2 \rangle\alpha\text{,}
$$

which we can calculate is exactly $\langle t_1u_1x_1 , r_2v_2x_2
\rangle$ --- just like we wanted!

```agda
  [rs]t≅i : Im ⟨ t₁ ∘ [rs]t.inter .p₁ , (π₂ ∘ i) ∘ [rs]t.inter .p₂ ⟩
      Sub.≅ Im ⟨ t₁ ∘ u₁ ∘ x₁ , r₂ ∘ v₂ ∘ x₂ ⟩
  [rs]t≅i = subst (λ e → Im [rs]t.it Sub.≅ Im e)
    (⟨⟩∘ _ ∙ ap₂ ⟨_,_⟩
      (pullr ([rs]t.inter .p₁∘universal))
      ( pullr ([rs]t.inter .p₂∘universal)
      ∙ extendl (pullr (sym (factor _ .factors)) ∙ π₂∘⟨⟩)))
    (image-pre-cover [rs]t.it _ α-cover)
```

Now do that whole thing over again. I'm not joking: start by forming the
pullback $R \times_B J$ that defines $\phi(\psi\chi)$, define a map
$\beta$ from $X$ into it, show that $\beta$ is a cover, so
$\phi(\psi\chi)$ is tabulated by the same map out of $X$ that we just
showed tabulates $(\phi\psi)\chi$. It's such blatant repetition that
I've omitted it from the page: you can choose to show hidden code if you
want to look at the formalisation.

<!--
```agda
  β : Hom (X .apex) (r[st].inter .apex)
  β = r[st].inter .universal {p₁' = q ∘ x₁} {p₂' = v₂ ∘ x₂} comm where abstract
    comm : (π₂ ∘ i) ∘ q {f = st.it} ∘ x₁ ≡ r₁ ∘ v₂ ∘ x₂
    comm = pulll (pullr (sym (factor st.it .factors)) ∙ π₂∘⟨⟩)
         ∙ pullr (sym (X .square)) ∙ extendl (rs.inter .square)

  abstract
    rem₂ : is-pullback C (ζ₂ ∘ β) r₁ x₁ ((π₂ ∘ i) ∘ q {f = st.it})
    rem₂ = transport
      (ap₂ (λ x y → is-pullback C x (Relation.src r) x₁ y)
        (sym (r[st].inter .p₂∘universal))
        (sym (pullr (sym (factor st.it .factors)) ∙ π₂∘⟨⟩)))
      (pasting-left→outer-is-pullback
        (rotate-pullback (rs.inter .has-is-pb)) (X .has-is-pb)
        (extendl (sym (rs.inter .square)) ∙ pushr (X .square)))

    β-is-pb : is-pullback C β ζ₁ x₁ q
    β-is-pb = pasting-outer→left-is-pullback
      (rotate-pullback (r[st].inter .has-is-pb))
      rem₂
      (r[st].inter .p₁∘universal)

  β-cover : is-strong-epi C β
  β-cover = stable _ _ (out! {pa = is-strong-epi-is-prop C _} (factor st.it .mediate∈E)) β-is-pb

  r[st]≅i : Im r[st].it Sub.≅ Im j
  r[st]≅i = subst (λ e → Im r[st].it Sub.≅ Im e)
    (⟨⟩∘ _ ∙ ap₂ ⟨_,_⟩ (pullr (r[st].inter .p₁∘universal) ∙ extendl (pullr (sym (factor _ .factors)) ∙ π₁∘⟨⟩))
                       (pullr (r[st].inter .p₂∘universal)))
    (image-pre-cover r[st].it _ β-cover)

  done : Im r[st].it Sub.≅ Im [rs]t.it
  done = r[st]≅i Sub.∘Iso ([rs]t≅i Sub.Iso⁻¹)
```
-->

## The bicategory of relations

That is, fortunately, the hardest part of the proof. It remains to
construct these three maps:

```agda
∘-rel-monotone
  : ∀ {b c d} {r r' : c ↬ d} {s s' : b ↬ c}
  → r ≤ₘ r' → s ≤ₘ s' → ∘-rel r s ≤ₘ ∘-rel r' s'

∘-rel-idr : ∀ {a b} (f : a ↬ b) → ∘-rel f id-rel Sub.≅ f
∘-rel-idl : ∀ {a b} (f : a ↬ b) → ∘-rel id-rel f Sub.≅ f
```

Witnessing, respectively, that relational composition respects inclusion
of subobjects in both its arguments, and that it has the identity
relation as right and left identities. These proofs are less
interesting, since they are routine applications of the universal
property of images, and a lot of annoying calculations with products and
pullbacks.

The curious reader can choose to show hidden code to display the proofs,
but keep in mind that they are not commented.

<!--
```agda
∘-rel-monotone {r = r} {r'} {s} {s'} α β =
  Im-universal (∘-rel.it r s) _
    {e = factor _ .mediate ∘ ∘-rel.inter r' s' .universal
      {p₁' = β .map ∘ ∘-rel.inter _ _ .p₁}
      {p₂' = α .map ∘ ∘-rel.inter _ _ .p₂}
      ( pullr (pulll (sym (β .sq) ∙ idl _))
      ∙ sym (pullr (pulll (sym (α .sq) ∙ idl _))
      ∙ (assoc _ _ _ ·· sym (∘-rel.inter r s .square) ·· sym (assoc _ _ _))))}
    (Product.unique₂ (lex.products _ _)
      (π₁∘⟨⟩ ∙ pullr refl)
      (π₂∘⟨⟩ ∙ pullr refl)
      (  ap₂ _∘_ refl (pulll (sym (factor _ .factors)))
      ·· pulll π₁∘⟨⟩ ∙ pullr (∘-rel.inter r' s' .p₁∘universal)
      ·· pullr (pulll (sym (β .sq) ∙ idl _)))
      (  ap₂ _∘_ refl (pulll (sym (factor _ .factors)))
      ·· pulll π₂∘⟨⟩ ∙ pullr (∘-rel.inter r' s' .p₂∘universal)
      ·· pullr (pulll (sym (α .sq) ∙ idl _))))

∘-rel-idr f = Sub-antisym fid≤f f≤fid where
  fid≤f : ∘-rel f id-rel ≤ₘ f
  fid≤f = Im-universal _ _ {e = ∘-rel.inter f id-rel .p₂} $ sym $ ⟨⟩-unique _
    (sym (∘-rel.inter f id-rel .square ∙ sym (assoc _ _ _)) ∙ eliml π₂∘⟨⟩ ∙ introl π₁∘⟨⟩)
    (assoc _ _ _)

  f≤fid : f ≤ₘ ∘-rel f id-rel
  f≤fid .map = factor _ .mediate ∘
    ∘-rel.inter f id-rel .universal {p₁' = Relation.src f} {p₂' = id}
      (eliml π₂∘⟨⟩ ∙ intror refl)
  f≤fid .sq = idl _ ∙ sym (pulll (sym (factor _ .factors)) ∙ ⟨⟩∘ _ ∙ sym (⟨⟩-unique _
    (sym (ap₂ _∘_ (eliml π₁∘⟨⟩) refl ∙ ∘-rel.inter _ _ .p₁∘universal))
    (sym (pullr (∘-rel.inter _ _ .p₂∘universal) ∙ idr _))))

∘-rel-idl f = Sub-antisym idf≤f f≤idf where
  idf≤f : ∘-rel id-rel f ≤ₘ f
  idf≤f = Im-universal _ _ {e = ∘-rel.inter id-rel f .p₁} $ sym $ ⟨⟩-unique _
    (assoc _ _ _)
    (assoc _ _ _ ∙ ∘-rel.inter id-rel f .square ∙ eliml π₁∘⟨⟩ ∙ introl π₂∘⟨⟩)

  f≤idf : f ≤ₘ ∘-rel id-rel f
  f≤idf .map = factor _ .mediate ∘
    ∘-rel.inter id-rel f .universal {p₁' = id} {p₂' = Relation.tgt f}
      (idr _ ∙ sym (eliml π₁∘⟨⟩))
  f≤idf .sq = idl _ ∙ sym (pulll (sym (factor _ .factors)) ∙ ⟨⟩∘ _ ∙ sym (⟨⟩-unique _
    (sym (pullr (∘-rel.inter id-rel f .p₁∘universal) ∙ idr _))
    (sym (pullr (∘-rel.inter id-rel f .p₂∘universal) ∙ eliml π₂∘⟨⟩))))

open Prebicategory hiding (Ob ; Hom)
open make-natural-iso
open Functor
```
-->

That aside over with, we can set up the bicategory of relations in
$\cC$: Monotonicity of the composition operation is all we need for
functoriality, and our coherence isomorphisms automatically satisfy
naturality _and_ their identities (triangle/pentagon) since $\Sub(-
\times -)$ is always a preorder.

```agda
private
  ∘-rel-fun : ∀ {a b c} → Functor (Sub (b ⊗₀ c) ×ᶜ Sub (a ⊗₀ b)) (Sub (a ⊗₀ c))
  ∘-rel-fun .F₀ (a , b) = ∘-rel a b
  ∘-rel-fun .F₁ (f , g) = ∘-rel-monotone  f g

  ∘-rel-fun .F-id    = hlevel 1 _ _
  ∘-rel-fun .F-∘ _ _ = hlevel 1 _ _

Rel[_] : Prebicategory o (o ⊔ ℓ) ℓ
Rel[_] .Prebicategory.Ob = Ob
Rel[_] .Prebicategory.Hom a b = Sub (a ⊗₀ b)
Rel[_] .id      = id-rel
Rel[_] .compose = ∘-rel-fun
```

The objects are those of $\cC$; The maps $a \rel b$ are all the
subobjects $\Sub(a \times b)$; The identity relation is the graph of the
identity function, and relational composition is a mess.

```agda
Rel[_] .unitor-l = to-natural-iso mk where
  mk : make-natural-iso Id (Bifunctor.Right ∘-rel-fun id-rel)
  mk .eta x = ∘-rel-idl x .Sub.from
  mk .inv x = ∘-rel-idl x .Sub.to
  mk .eta∘inv x = Sub.invr (∘-rel-idl x)
  mk .inv∘eta x = Sub.invl (∘-rel-idl x)
  mk .natural x y f = hlevel 1 _ _
Rel[_] .unitor-r = to-natural-iso mk where
  mk : make-natural-iso Id (Bifunctor.Left ∘-rel-fun id-rel)
  mk .eta x = ∘-rel-idr x .Sub.from
  mk .inv x = ∘-rel-idr x .Sub.to
  mk .eta∘inv x = Sub.invr (∘-rel-idr x)
  mk .inv∘eta x = Sub.invl (∘-rel-idr x)
  mk .natural x y f = hlevel 1 _ _
Rel[_] .associator {a} {b} {c} {d} = to-natural-iso mk where
  mk : make-natural-iso (compose-assocˡ ∘-rel-fun) (compose-assocʳ ∘-rel-fun {A = a} {b} {c} {d})
  mk .eta (x , y , z) = ∘-rel-assoc x y z .Sub.from
  mk .inv (x , y , z) = ∘-rel-assoc x y z .Sub.to
  mk .eta∘inv (x , y , z) = Sub.invr (∘-rel-assoc x y z)
  mk .inv∘eta (x , y , z) = Sub.invl (∘-rel-assoc x y z)
  mk .natural (x , y , z) (α , β , γ) f =
    ≤-over-is-prop
      (compose-assocʳ {H = λ x y → Sub (x ⊗₀ y)} ∘-rel-fun .F₁ f Sub.∘ ∘-rel-assoc x y z .Sub.from)
      (∘-rel-assoc α β γ .Sub.from Sub.∘ compose-assocˡ {H = λ x y → Sub (x ⊗₀ y)} ∘-rel-fun .F₁ f)
Rel[_] .triangle f g = hlevel 1 _ _
Rel[_] .pentagon f g h i = hlevel 1 _ _
```
