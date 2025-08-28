---
description: |
  Strong monomorphisms.
---
<!--
```agda
open import Cat.Morphism.Orthogonal
open import Cat.Morphism.Class
open import Cat.Morphism.Lifts
open import Cat.Prelude

import Cat.Reasoning
```
-->
```agda
module Cat.Morphism.Strong.Mono {o ℓ} (C : Precategory o ℓ) where
```

<!--
```agda
open Cat.Reasoning C
```
-->

# Strong monomorphisms {defines="strong-mono strong-monomorphism"}

A **strong monomorphism** is a [[monomorphism]] that is [[right orthogonal]]
to every [[epimorphism]]. Note that strong monomorphisms are the formal dual of
[[strong epimorphisms]]. Explicitly, $m : c \mono d$ is a strong mono
if every commutative square of the form

~~~{.quiver}
\begin{tikzcd}
  a && b \\
  \\
  c && d
  \arrow["e", two heads, from=1-1, to=1-3]
  \arrow["u"', from=1-1, to=3-1]
  \arrow["v", from=1-3, to=3-3]
  \arrow["m"', tail, from=3-1, to=3-3]
\end{tikzcd}
~~~

has a contractible space of lifts $b \to c$.

```agda
is-strong-mono : ∀ {c d} → Hom c d → Type _
is-strong-mono f = is-monic f × Orthogonal C Epis f
```

<!--
```agda
StrongMonos : Arrows C (o ⊔ ℓ)
StrongMonos .arrows = is-strong-mono
StrongMonos .is-tr = hlevel 1

Epis⊥StrongMonos : Orthogonal C Epis StrongMonos
Epis⊥StrongMonos f f-epi g (g-mono , Epis⊥g) = Epis⊥g f f-epi
```
-->

As it turns out, the contractibility requirement is redundant, as every
lift of a mono is unique.

```agda
lifts→is-strong-mono
  : ∀ {c d} {f : Hom c d}
  → is-monic f
  → Lifts C Epis f
  → is-strong-mono f
lifts→is-strong-mono monic lifts =
  monic , right-monic-lift→orthogonal-class C Epis monic lifts
```

This condition seems somewhat arbitrary, so let's take a second to do
some exposition. First, note that in $\Sets$, every mono is strong.
The key insight here is that epis are surjections, and monos are
[[embeddings]]. In particular, suppose that $f : A \epi B$ is
some surjection and $m : C \to D$ is some embedding, and $u : A \to C$,
$v : B \to D$ are a pair of arbitrary maps; our job is to build a function
$B \to C$. Now, $f$ is a surjection, so we know that each fibre $f^{-1}(b)$
is *merely* inhabited. However, $m$ is an embedding, so its fibres
are [[propositions]]: therefore, we can eliminate from the truncation of $f^{-1}(b)$
to $m^{-1}(v(b))$ via $u$. This suggests that we ought to think of strong
monomorphisms as a categorical generalization of maps with propositional
fibres.

<!--
```agda
abstract
  is-strong-mono-is-prop
    : ∀ {a b} (f : Hom a b) → is-prop (is-strong-mono f)
  is-strong-mono-is-prop f = hlevel 1
```
-->

With that bit of intuition out of the way, we can proceed to prove some
basic facts. Let's start by showing that every isomorphism is a strong mono.

```agda
invertible→strong-mono
  : ∀ {a b} {f : Hom a b} → is-invertible f → is-strong-mono f
```

-- The argument here is quite straightforward: every iso is monic, and
isos are right orthogonal to every map.

```agda
invertible→strong-mono f-inv =
  invertible→monic f-inv ,
  invertible→right-orthogonal-class C Epis f-inv
```

Next, let's show that strong monos compose. This is completely dual
to the proof that [strong epis compose], so we direct the reader there
for exposition.

[strong epis compose]: Cat.Morphism.Strong.Epi.html#properties

```agda
∘-is-strong-monic
  : ∀ {a b c} {f : Hom b c} {g : Hom a b}
  → is-strong-mono f
  → is-strong-mono g
  → is-strong-mono (f ∘ g)
∘-is-strong-monic (f-mono , f-str) (g-mono , g-str) =
  lifts→is-strong-mono (∘-is-monic f-mono g-mono) $
    ∘r-lifts-class C Epis
      (orthogonal→lifts-left-class C Epis f-str)
      (orthogonal→lifts-left-class C Epis g-str)
```

Like their non-strong counterparts, strong monomorphisms satisfy a
left cancellation property. This is dual to the proof that [strong epis
cancel], so we omit the details.

[strong epis cancel]: Cat.Morphism.Strong.Epi.html#properties

```agda
strong-mono-cancell
  : ∀ {a b c} (f : Hom b c) (g : Hom a b)
  → is-strong-mono (f ∘ g)
  → is-strong-mono g
```

<details>
<summary>
</summary>
```agda
strong-mono-cancell f g (fg-mono , fg-str) =
  lifts→is-strong-mono g-mono g-str
  where
    g-mono : is-monic g
    g-mono = monic-cancell fg-mono

    g-str : Lifts C Epis g
    g-str e e-epi u v ve=gu =
      let (w , we=u , fgw=fv) = fg-str e e-epi u (f ∘ v) (extendr ve=gu) .centre
      in pure (w , we=u , e-epi (g ∘ w) v (pullr we=u ∙ sym ve=gu))
```
</details>

If a morphism is both strong monic and epic, then it is orthogonal to
itself, and thus invertible.

```agda
strong-mono+epi→invertible
  : ∀ {a b} {f : Hom a b} → is-strong-mono f → is-epic f → is-invertible f
strong-mono+epi→invertible {f = f} (_ , strong) epi =
  self-orthogonal→invertible C f (strong f epi)
```

<!--
```agda
subst-is-strong-mono
  : ∀ {a b} {f g : Hom a b}
  → f ≡ g
  → is-strong-mono f
  → is-strong-mono g
subst-is-strong-mono f=g f-strong-mono =
  lifts→is-strong-mono (subst-is-monic f=g (f-strong-mono .fst)) λ e e-epic u v vg=mu →
    let (h , he=u , fh=v) = f-strong-mono .snd e e-epic u v (vg=mu ∙ ap₂ _∘_ (sym f=g) refl) .centre
    in pure (h , he=u , ap (_∘ h) (sym f=g) ∙ fh=v)
```
-->
