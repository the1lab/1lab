<!--
```agda
open import Cat.Diagram.Colimit.Weighted
open import Cat.Functor.Hom.Yoneda
open import Cat.Functor.Properties
open import Cat.Instances.Elements
open import Cat.Instances.Functor
open import Cat.Instances.Product
open import Cat.Diagram.Initial
open import Cat.Prelude

import Cat.Functor.Hom
import Cat.Reasoning
```
-->

```agda
module Cat.Functor.Hom.Coyoneda {o h} (C : Precategory o h) where
```

<!--
```agda
open import Cat.Reasoning C
open Cat.Functor.Hom C

open Functor
open _=>_
```
-->

## The Coyoneda lemma {defines="coyoneda coyoneda-lemma"}

The Coyoneda lemma is, like its dual, a statement about presheaves.  It
states that "every presheaf is a colimit of representables", which, in
less abstract terms, means that every presheaf arises as some way of
gluing together a bunch of (things isomorphic to) hom functors!

```agda
module _ (P : Functor (C ^op) (Sets h)) where
  private
    module P = Functor P
  open is-weighted-colimit
```

We start by fixing some presheaf $P$, and constructing a colimit
whose coapex is $P$. This involves a clever choice of diagram category:
specifically, the [category of elements] of $P$. This may seem like a
somewhat odd choice, but recall that the data contained in $\int P$ is
the _same_ data as $P$, just melted into a soup of points.  The colimit
we construct will then glue all those points back together into $P$.

[category of elements]: Cat.Instances.Elements.html

```agda
  coyoneda : is-weighted-colimit P よ P (λ x p → yo P p)
  coyoneda .commutes f p = ext λ y g → P.F-∘ g f ·ₚ p
  coyoneda .universal {Q} ψ ψ-nat .η x p = unyo Q (ψ x p)
  coyoneda .universal {Q} ψ ψ-nat .is-natural x y f = ext λ p →
    ψ y (P ⟪ f ⟫ p) .η y id ≡˘⟨ ψ-nat f p ·ₚ y ·ₚ id ⟩
    ψ x p .η y (f ∘ id)     ≡⟨ ap (ψ x p .η y) id-comm ⟩
    ψ x p .η y (id ∘ f)     ≡⟨ ψ x p .is-natural x y f ·ₚ id ⟩
    (Q ⟪ f ⟫ ψ x p .η x id) ∎
  coyoneda .factors ψ ψ-nat x p = ext λ y f →
    ψ y (P ⟪ f ⟫ p) .η y id ≡˘⟨ ψ-nat f p ·ₚ y ·ₚ id ⟩
    ψ x p .η y (f ∘ id)     ≡⟨ ap (ψ x p .η y) (idr f) ⟩
    ψ x p .η y f            ∎
  coyoneda .unique ψ ψ-nat u q = ext λ x p →
    ψ x p .η x id       ≡˘⟨ q x p ·ₚ x ·ₚ id ⟩
    u .η x (P ⟪ id ⟫ p) ≡⟨ ap (u .η x) (P.F-id ·ₚ p) ⟩
    u .η x p            ∎
```

An important consequence of being able to disassemble presheaves into
colimits of representables is that **representables generate
$\psh(C)$**, in that if a pair $f, g$ of natural transformations that
agrees on all representables, then $f = g$ all along.

```agda
  module _ {Y} (f : P => Y) where
    private
      module Y = Functor Y
```

<!--
```agda
module _ {X Y : Functor (C ^op) (Sets h)} where
  private
    module PSh = Cat.Reasoning (Cat[ C ^op , Sets h ])
    module X = Functor X
    module Y = Functor Y
    open Initial
```
-->

Suppose that $f, g : X \To Y$ are two maps such that, for
every map with representable domain $h : \yo(A) \to X$, $fh = gh$, then
$f = g$. The quantifier structure of this sentence is a bit funky, so
watch out for the formalisation below:

```agda
  Representables-generate-presheaf
    : {f g : X => Y}
    → (∀ {A : Ob} (h : よ₀ A => X) → f PSh.∘ h ≡ g PSh.∘ h)
    → f ≡ g
```

A map $h : \yo(A) \To X$ can be seen as a "generalised element" of $X$,
so that the precondition for $f = g$ can be read as "$f$ and $g$ agree
for _all_ generalised elements with domain _any_ representable". The
proof is deceptively simple: Since $X$ is a weighted colimit, we can
deduce that two maps out of $X$ are equal by testing them at the
inclusions into $X$[^joint-epi]. In our case, these inclusions are
given by $\operatorname{yo} (x) : \yo(X) \to X$, which is exactly our
hypothesis!

[^joint-epi]: In other words, the inclusions form a jointly epic family.

```agda
  Representables-generate-presheaf {f} {g} sep =
    X-colim.unique₂ f g λ j xj → ext λ i h → sep (yo X xj) ·ₚ i ·ₚ h
    where module X-colim = is-weighted-colimit (coyoneda X)
```

An immediate consequence is that, since any pair of maps $f, g : X \to
Y$ in $\cC$ extend to maps $\yo(f), \yo(g) : \yo(X) \to \yo(Y)$, and the
functor $\yo(-)$ is [[fully faithful]], two maps in $\cC$ are equal iff.
they agree on all generalised elements:

```agda
private module _ where private
  よ-cancelr
    : ∀ {X Y : Ob} {f g : Hom X Y}
    → (∀ {Z} (h : Hom Z X) → f ∘ h ≡ g ∘ h)
    → f ≡ g
  よ-cancelr sep =
    ff→faithful {F = よ} よ-is-fully-faithful $
      Representables-generate-presheaf λ h → ext λ x a →
        sep (h .η x a)
```

However note that we have eliminated a mosquito using a low-orbit ion
cannon:

```agda
よ-cancelr
  : ∀ {X Y : Ob} {f g : Hom X Y}
  → (∀ {Z} (h : Hom Z X) → f ∘ h ≡ g ∘ h)
  → f ≡ g
よ-cancelr sep = sym (idr _) ∙ sep id ∙ idr _
```
