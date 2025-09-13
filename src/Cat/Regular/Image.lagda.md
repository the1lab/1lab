<!--
```agda
open import Cat.Morphism.Factorisation.Orthogonal
open import Cat.Diagram.Pullback.Properties
open import Cat.Displayed.Instances.Slice
open import Cat.Morphism.Factorisation
open import Cat.Displayed.Cocartesian
open import Cat.Morphism.Strong.Epi
open import Cat.Displayed.Doctrine
open import Cat.Displayed.Functor
open import Cat.Diagram.Pullback
open import Cat.Instances.Slice
open import Cat.Prelude
open import Cat.Regular

import Cat.Displayed.Instances.Subobjects.Reasoning as Sr
import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Regular.Image
  {o ℓ} {C : Precategory o ℓ}
  (reg : is-regular C)
  where
```

<!--
```agda
open reflects-cartesian-maps
open Regular-hyperdoctrine hiding (_^*_; _^!_)
open Displayed-functor
open is-fibred-functor
open is-regular reg
open Factorisation
open /-Obj
open /-Hom
open Cr C
open Sr lex.pullbacks

private
  module pb = lex.pullback
  Sub-opf = Subobject-opfibration Image[_] lex.pullbacks
open Cocartesian-fibration Subobjects Sub-opf
```
-->

# Images in regular categories

This module provides tools for working with the [[image factorisation]] of
morphisms in [[regular categories]], regarded as [[subobjects]] of the map's
codomain. We start by defining a `Subobject`{.Agda} of $y$ standing for
$\im f$ whenever $f : x \to y$.

```agda
Im : ∀ {x y} (f : Hom x y) → Subobject y
Im f .dom   = _
Im f .map   = factor f .right
Im f .monic = factor f .right∈R
```

We may then use this to rephrase the universal property of $\im f$ as
the initial subobject through which $f$ factors.

```agda
Im-universal
  : ∀ {x y} (f : Hom x y)
  → (m : Subobject y) {e : Hom x (m .dom)}
  → f ≡ m .map ∘ e
  → Im f ≤ₘ m
Im-universal f m {e = e} p = r where
  the-lift =
    factor f .left∈L .snd (m .map) (m .monic) _ _
      (sym (factor f .factors) ∙ p)

  r : _ ≤ₘ _
  r .map = the-lift .centre .fst
  r .com = idl _ ∙ sym (the-lift .centre .snd .snd)
```

An important fact that will be used in calculating associativity for
[relations in regular categories] is that precomposing with a [[strong
epimorphism]] preserves images. Intuitively, this is because a strong
epimorphism $a \epi b$ expresses $b$ as a quotient, but this
decomposition does not alter the image of a map $b \to c$.

[relations in regular categories]: Cat.Bi.Instances.Relations.html

We prove this by first showing a uniqueness property for images: as a
refinement of the previous universal property, if $f : a \to b$ factors
through a [[subobject]] $m$ of $b$ via a strong epimorphism $g : a \to m$,
then $m$ must be the image of $f$ by essential uniqueness of
[[orthogonal factorisations|orthogonal factorisation system]].

```agda
image-unique
  : ∀ {a b} (f : Hom a b) (m : Subobject b) (g : Hom a (m .dom))
  → is-strong-epi C g
  → (com : f ≡ m .map ∘ g)
  → Sub.is-invertible (Im-universal f m com)
image-unique f m g g-covers com =
  let
    f-fac = factorisation (m .dom) g (m .map) g-covers (λ {c} → m .monic {c}) com
    is , _ , is-com = factorisation-essentially-unique C _ _
      strong-epi-mono-is-ofs f (factor f) f-fac
  in Sub-cod-conservative _ (iso→invertible is)
```

The result then follows by noticing that the composite $a \xepi{g} b \epi
\im(f)$ is a strong epimorphism witnessing $\im(f)$ as the
image of $f \circ g$.

```agda
image-pre-cover
  : ∀ {a b c} (f : Hom b c) (g : Hom a b)
  → is-strong-epi C g
  → Im (f ∘ g) ≅ₘ Im f
image-pre-cover f g g-covers =
  Sub.invertible→iso _ $
    image-unique (f ∘ g) (Im f) (a↠im[ f ] ∘ g)
      (∘-is-strong-epic C a↠im[ f ]-strong-epic g-covers)
      (pushl im[ f ]-factors)
```

## Stability

In a regular category, images don't just exist; they also have the
good manners of being stable under [[pullback]]. This follows from the
property that [[strong epimorphisms]] are stable under pullback, which
is part of the definition of a regular category.

We will make this precise by showing that there is a vertical [[fibred
functor]] from the [[fundamental fibration]] of $\cC$ to its
[[subobject fibration]], which we can think of as modelling a
"propositional truncation" type former; since cartesian morphisms in
both fibrations are pullback squares, this is equivalent to the
usual formulation of pullback-stability, namely $f^*(\im(g)) =
\im(f^*g)$.

First, let a commutative square as in the following diagram be given: a
map $k : h \to_f g$ in the fundamental fibration.

~~~{.quiver}
\[\begin{tikzcd}
  c & d \\
  a & b
  \arrow["k", from=1-1, to=1-2]
  \arrow["h"', from=1-1, to=2-1]
  \arrow["g", from=1-2, to=2-2]
  \arrow["f"', from=2-1, to=2-2]
\end{tikzcd}\]
~~~

After replacing $h$ and $g$ with their image factorisations and pulling
$\im(g)$ back along $f$, we arrive at the following situation, where
the map $c \to f^*(\im(g))$ is given by the universal property of
the pullback, and the dashed comparison map by the universal
property of the image of $h$. The composite middle row gives us a map
$\im(h) \leq_f \im(g)$ in the subobject fibration.

~~~{.quiver}
\[\begin{tikzcd}
  & c & d \\
  {\im(h)} & {f^*(\im(g))} & {\im(g)} \\
  & a & b
  \arrow["k", from=1-2, to=1-3]
  \arrow[two heads, from=1-2, to=2-1]
  \arrow[from=1-2, to=2-2]
  \arrow[two heads, from=1-3, to=2-3]
  \arrow[dashed, from=2-1, to=2-2]
  \arrow[hook', from=2-1, to=3-2]
  \arrow[from=2-2, to=2-3]
  \arrow[hook', from=2-2, to=3-2]
  \arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=2-2, to=3-3]
  \arrow[hook', from=2-3, to=3-3]
  \arrow["f"', from=3-2, to=3-3]
\end{tikzcd}\]
~~~

```agda
Im-comparison
  : ∀ {a b c d} {f : Hom a b} {g : Hom d b} {h : Hom c a} {k : Hom c d}
  → f ∘ h ≡ g ∘ k
  → Im h ≤ₘ f ^* Im g
Im-comparison {f = f} {g} {h} {k} sq =
  Im-universal h _ {pb.universal _ _ (sq ∙ pushl im[ g ]-factors)}
    (sym (pb.p₁∘universal _ _))

Im-map
  : ∀ {a b c d} {f : Hom a b} {g : Hom d b} {h : Hom c a} {k : Hom c d}
  → f ∘ h ≡ g ∘ k
  → ≤-over f (Im h) (Im g)
Im-map {f = f} {g} {h} sq .map = pb.p₂ _ _ ∘ Im-comparison sq .map
Im-map {f = f} {g} {h} sq .com =
  f ∘ im[ h ]↪b                                 ≡⟨ refl⟩∘⟨ sym (idl _) ⟩
  f ∘ id ∘ im[ h ]↪b                            ≡⟨ refl⟩∘⟨ Im-comparison sq .com ⟩
  f ∘ pb.p₁ _ _ ∘ Im-comparison sq .map         ≡⟨ extendl (pb.square _ _) ⟩
  im[ g ]↪b ∘ pb.p₂ _ _ ∘ Im-comparison sq .map ∎
```

This data turns `Im`{.Agda} into a [[vertical functor]].

```agda
Images : Vertical-functor (Slices C) Subobjects
Images .F₀' m = Im (m .map)
Images .F₁' f = Im-map (sym (f .com))
Images .F-id' = prop!
Images .F-∘' = prop!
```

The claim is now that this is a [[*fibred* functor]], i.e., that it
takes cartesian morphisms in the fundamental fibration --- pullback
squares --- to cartesian morphisms between images in the subobject
fibration, which are also characterised as pullback squares.

```agda
image-stable
  : ∀ {a b c d} {f : Hom a b} {g : Hom d b} {h : Hom c a} {k : Hom c d}
  → (pb : is-pullback C h f k g) (open is-pullback pb)
  → is-pullback C im[ h ]↪b f (Im-map square .map) im[ g ]↪b
image-stable {a} {b} {c} {d} {f} {g} {h} {k} pb = done where
```

To that end, assume that the outer square in the above diagram is a
pullback square. By the [[pasting law for pullbacks]], the top square
is also a pullback square. By the assumed stability property of strong
epimorphisms, this implies that the vertical map $c \to f^*(\im(g))$ is
a strong epimorphism.

```agda
  down-is-cover : is-strong-epi C _
  down-is-cover = stable _ (pb.p₂ _ _) a↠im[ g ]-strong-epic
    (pasting-outer→left-is-pullback (pb.has-is-pb _ _)
      (subst-is-pullback (sym (pb.p₁∘universal _ _)) refl refl im[ g ]-factors pb)
      (pb.p₂∘universal _ _))
```

But this now gives two different factorisations of $h$ as a strong
epimorphism followed by a monomorphism, so by uniqueness of images
the dashed comparison map is invertible, and hence $\im(h)$ is the
pullback of $\im(g)$ along $f$.

```agda
  unique : Sub.is-invertible _
  unique = image-unique h (f ^* Im g) _ down-is-cover
    (sym (pb.p₁∘universal _ _))

  done = is-pullback-iso'
    (≅ₘ→iso (Sub.invertible→iso _ unique))
    (pb.has-is-pb _ _)
    (sym (Im-universal h (f ^* Im g) _ .com) ∙ idl _)
    refl

Images-is-fibred : is-fibred-functor Images
Images-is-fibred .F-cartesian cart = pullback→cartesian-sub
  (image-stable (cartesian→pullback C cart))
```

## The regular hyperdoctrine of subobjects {defines="regular-hyperdoctrine-of-subobjects"}

One of the main motivations for [[regular categories]], as discussed
there, is that their fibrations of [[subobjects]] have
well-behaved existential quantifiers. We can summarise this by
constructing the [[regular hyperdoctrine]] of subobjects of a regular
[[univalent category]] $\cC$.

Since $\cC$ has pullbacks, the displayed category $\Sub$ over $\cC$
is a [[cartesian fibration]]; since $\cC$ has image factorisations, it
is also a [[cocartesian fibration]]. Observe that the cocartesian lift
$f_!(\alpha)$, which models the existential quantifier $\exists_f
\alpha$, is, almost by definition, the image of $f \circ \alpha$.

```agda
^!-is-Im
  : ∀ {a b} {f : Hom a b} {α : Subobject a}
  → f ^! α ≅ₘ Im (f ∘ α .map)
^!-is-Im = iso→≅ₘ id-iso (sym (idr _))
```

$\Sub$ also has fibrewise finite products, and those are well-behaved
under pullback.

```agda
module _ (cat : is-category C) where
  Sub-regular : Regular-hyperdoctrine C (o ⊔ ℓ) ℓ
  Sub-regular .ℙ = Subobjects
  Sub-regular .has-is-thin _ _ = hlevel 1
  Sub-regular .has-univalence x = Sub-is-category cat
  Sub-regular .cartesian = Subobject-fibration
  Sub-regular .cocartesian = Sub-opf
  Sub-regular .fibrewise-meet = Sub-products lex.pullbacks
  Sub-regular .fibrewise-top x = Sub-terminal
  Sub-regular .subst-& f m n = Sub-is-category cat .to-path ^*-∩ₘ
  Sub-regular .subst-aye f = Sub-is-category cat .to-path ^*-⊤ₘ
```

It remains to check the Beck-Chevalley condition and Frobenius
reciprocity. The Beck-Chevalley condition follows directly from
stability of images: we compute

$$
\exists_h (\alpha[k]) = \im(h \circ \alpha[k]) = \im(g \circ \alpha)[f] = (\exists_g \alpha)[f]
$$

using the [[pasting law for pullbacks]].

```agda
  Sub-regular .beck-chevalley pb {α} = Sub-is-category cat .to-path
    (invertible→≅ₘ
      (record { map = _ ; com = idl _ ∙ sym (pb.p₁∘universal _ _) })
      (pullback-unique (pb.has-is-pb _ _)
        (image-stable (pasting-left→outer-is-pullback pb (pb.has-is-pb _ _)))))
```

Remembering that the intersection $\alpha \cap \beta$ is computed as the
pullback $\alpha^* \beta$, Frobenius reciprocity can be seen as a
consequence of the Beck-Chevalley condition. Rather than reuse our
proof above, we take the opportunity to present an alternative, more
diagrammatic proof. The following diagram summarises the setup:

~~~{.quiver}
\[\begin{tikzcd}
  {\alpha \cap f^* \beta} &&& {f_!\alpha \cap \beta} \\
  & \alpha &&& {f_! \alpha} \\
  {f^*\beta} &&& \beta \\
  & X &&& Y
  \arrow[dashed, two heads, from=1-1, to=1-4]
  \arrow[hook', from=1-1, to=2-2]
  \arrow[hook', from=1-1, to=3-1]
  \arrow[hook', from=1-4, to=2-5]
  \arrow[hook', from=1-4, to=3-4]
  \arrow[two heads, from=2-2, to=2-5]
  \arrow[hook', from=2-2, to=4-2]
  \arrow[hook', from=2-5, to=4-5]
  \arrow[from=3-1, to=3-4]
  \arrow[hook', from=3-1, to=4-2]
  \arrow[hook', from=3-4, to=4-5]
  \arrow["f"', from=4-2, to=4-5]
\end{tikzcd}\]
~~~

We start by constructing the dashed map using the universal property
of the pullback, as the unique map that makes the cube commute.

```agda
  Sub-regular .frobenius f {α} {β} = Sub-is-category cat .to-path
    ((is Sub.∘Iso ^!-is-Im) Sub.Iso⁻¹)
    where
      dashed : Hom ((α ∩ₘ f ^* β) .dom) (((f ^! α) ∩ₘ β) .dom)
      dashed = pb.universal _ _ $ sym $
        β .map ∘ _ ∘ _             ≡⟨ pulll (sym (pb.square _ _)) ⟩
        (f ∘ _) ∘ _                ≡⟨ pullr (sym (pb.square _ _)) ⟩
        f ∘ _ ∘ _                  ≡⟨ extendl im[ f ∘ α .map ]-factors ⟩
        im[ f ∘ α .map ]↪b ∘ _ ∘ _ ∎
```

We then observe that the left, bottom, and right faces of the cube are
pullback squares, hence so is the top face by the [[pasting law for
pullbacks]]. This directly implies that the dashed map is a strong
epimorphism, since those are stable under pullback.

```agda
      dashed-is-cover : is-strong-epi C dashed
      dashed-is-cover = stable _ _ a↠im[ f ∘ α .map ]-strong-epic
        (pasting-outer→left-is-pullback
          (rotate-pullback (pb.has-is-pb _ _))
          (subst-is-pullback (sym (pb.p₂∘universal _ _)) refl refl im[ _ ]-factors
            (pasting-left→outer-is-pullback
              (rotate-pullback (pb.has-is-pb _ _))
              (rotate-pullback (pb.has-is-pb _ _))))
          (pb.p₁∘universal _ _))
```

This gives two different image factorisations of the "great diagonal"
of the cube, which exhibits $f_!\alpha \cap \beta$ as
$f_!(\alpha \cap f^*\beta)$ by uniqueness of images.

```agda
      is : Im (f ∘ (α ∩ₘ f ^* β) .map) ≅ₘ (f ^! α) ∩ₘ β
      is = Sub.invertible→iso _
         $ image-unique _ ((f ^! α) ∩ₘ β) dashed dashed-is-cover
         $ sym (pullr (pb.p₁∘universal _ _) ∙ extendl (sym im[ _ ]-factors))
```
