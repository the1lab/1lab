<!--
```agda
open import Cat.Diagram.Colimit.Cocone
open import Cat.Diagram.Colimit.Base
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
  open Element
  open Element-hom
```

We start by fixing some presheaf $P$, and constructing a colimit
whose coapex is $P$. This involves a clever choice of diagram category:
specifically, the [category of elements] of $P$. This may seem like a
somewhat odd choice, but recall that the data contained in $\int P$ is
the _same_ data as $P$, just melted into a soup of points.  The colimit
we construct will then glue all those points back together into $P$.

[category of elements]: Cat.Instances.Elements.html

```agda
  coyoneda : is-colimit (よ F∘ πₚ C P) P _
  coyoneda = to-is-colimit colim where
```

This is done by projecting out of $\int P$ into $\cC$ via the
[canonical projection], and then embedding $\cC$ into the category of
presheaves over $\cC$ via the yoneda embedding. Concretely, what this
diagram gives us is a bunch of copies of the hom functor, one for each
$px : P(X)$. Then, to construct the injection map, we can just use the
(contravariant) functorial action of $P$ to take a $px : P(X)$ and a $f
: Hom(A, X)$ to a $P(A)$. This map is natural by functoriality of $P$.

[canonical projection]: Cat.Instances.Elements.html#projection

```agda
    open make-is-colimit
    module ∫ = Precategory (∫ C P)

    colim : make-is-colimit (よ F∘ πₚ C P) P
    colim .ψ x .η y f = P.F₁ f (x .section)
    colim .ψ x .is-natural y z f =
      funext (λ g → happly (P.F-∘ f g) (x .section))
    colim .commutes {x = x} {y = y} f = ext λ z g →
      P.F₁ (f .hom ∘ g) (y .section)      ≡⟨ happly (P.F-∘ g (f .hom)) (y .section) ⟩
      P.F₁ g (P.F₁ (f .hom) (y .section)) ≡⟨ ap (P.F₁ g) (f .commute) ⟩
      P.F₁ g (x .section)                 ∎
```

Now that we've constructed a cocone, all that remains is to see that
this is a _colimiting_ cocone. Intuitively, it makes sense that
`Reassemble`{.Agda} should be colimiting: all we've done is taken all
the data associated with $P$ and glued it back together.  However,
proving this does involve futzing about with various naturality + cocone
commuting conditions.

We start by constructing the universal map from $P$ into the coapex of
some other cocone $K$. The components of this natural transformation are
obtained in a similar manner to the yoneda lemma; we bundle up the data
to construct an object of $\int P$, and then apply the function we
construct to the identity morphism. Naturality follows from the fact
that $K$ is a cocone, and the components of $K$ are natural.

```agda
    colim .universal eta _ .η x px =  eta (elem x px) .η x id
    colim .universal {Q} eta comm .is-natural x y f = funext λ px →
      eta (elem y (P.F₁ f px)) .η y id        ≡˘⟨ (λ i → comm (induce C P f px) i .η y id) ⟩
      eta (elem x px) .η y (f ∘ id)           ≡⟨ ap (eta (elem x px) .η y) id-comm ⟩
      eta (elem x px) .η y (id ∘ f)           ≡⟨ happly (eta (elem x px) .is-natural x y f) id ⟩
      Q .F₁ f (eta (elem x px) .η x id)       ∎
```

Next, we need to show that this morphism factors each of the components
of $K$. The tricky bit of the proof here is that we need to use
`induce`{.Agda} to regard `f` as a morphism in the category of elements.

```agda
    colim .factors {o} eta comm = ext λ x f →
      eta (elem x (P.F₁ f (o .section))) .η x id ≡˘⟨ (λ i → comm (induce C P f (o .section)) i .η x id) ⟩
      eta o .η x (f ∘ id)                        ≡⟨ ap (eta o .η x) (idr f) ⟩
      eta o .η x f                               ∎
```

Finally, uniqueness: This just follows by the commuting conditions on
`α`.

```agda
    colim .unique eta comm α p = ext λ x px →
      α .η x px               ≡˘⟨ ap (α .η x) (happly P.F-id px) ⟩
      α .η x (P.F₁ id px)     ≡⟨ happly (p _ ηₚ x) id ⟩
      eta (elem x px) .η x id ∎
```

And that's it! The important takeaway here is not the shuffling around
of natural transformations required to prove this lemma, but rather the
idea that, unlike Humpty Dumpty, if a presheaf falls off a wall, we
_can_ put it back together again.

An important consequence of being able to disassemble presheaves into
colimits of representables is that **representables generate
$\psh(C)$**, in that if a pair $f, g$ of natural transformations that
agrees on all representables, then $f = g$ all along.

```agda
  module _ {Y} (f : P => Y) where
    private
      module Y = Functor Y
      open Cocone
```

The first thing we prove is that any map $P \To Y$ of presheaves
expresses $Y$ as a cocone over $\yo (\pi P)$. The special case
`Reassemble`{.Agda} above is this procedure for the identity map ---
whence we see that `coyoneda`{.Agda} is essentially a restatement of the
fact that $\id$ is initial the coslice category under $P$.

```agda
    Map→cocone-under : Cocone (よ F∘ πₚ C P)
    Map→cocone-under .coapex = Y

    Map→cocone-under .ψ (elem ob sect) .η x i = f .η x (P.₁ i sect)
    Map→cocone-under .ψ (elem ob sect) .is-natural x y h = funext λ a →
      f .η _ (P.₁ (a ∘ h) sect)   ≡⟨ happly (f .is-natural _ _ _) _ ⟩
      Y.₁ (a ∘ h) (f .η _ sect)   ≡⟨ happly (Y.F-∘ _ _) _ ⟩
      Y.₁ h (Y.₁ a (f .η _ sect)) ≡˘⟨ ap (Y .F₁ h) (happly (f .is-natural _ _ _) _) ⟩
      Y.₁ h (f .η _ (P.₁ a sect)) ∎

    Map→cocone-under .commutes {x} {y} o = ext λ i a → ap (f .η _) $
      P.₁ (o .hom ∘ a) (y .section)     ≡⟨ happly (P.F-∘ _ _) _ ⟩
      P.₁ a (P.₁ (o .hom) (y .section)) ≡⟨ ap (P.F₁ _) (o .commute) ⟩
      P.₁ a (x .section)                ∎
```

<!--
```agda
module _ {X Y : Functor (C ^op) (Sets h)} where
  private
    module PSh = Cat.Reasoning (Cat[ C ^op , Sets h ])
    module P = Functor X
    module Y = Functor Y
    open Cocone-hom
    open Element
    open Initial
    open Cocone
```
-->

We can now prove that, if $f, g : X \To Y$ are two maps such that, for
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
proof is deceptively simple: Since $X$ is a colimit, it is an initial
object in the category of cocones under $\yo (\pi X)$.

The construction `Map→cocone-under`{.Agda} lets us express $Y$ as a
cocone under $\yo (\pi X)$ in a way that $f$ becomes a cocone
homomorphism $X \to Y$; The condition that $g$ agrees with $f$ on all
generalised elements with representable domains ensures that $g$ is
_also_ a cocone homomorphism $X \to Y$; But $X$ is initial, so $f = g$!

```agda
  Representables-generate-presheaf {f} {g} sep =
    ap hom $ is-contr→is-prop
      (is-colimit→is-initial-cocone _ (coyoneda X) (Map→cocone-under X f))
      f' g'
    where
      f' : Cocone-hom (よ F∘ πₚ C X) _ (Map→cocone-under X f)
      f' .hom = f
      f' .commutes o = trivial!

      g' : Cocone-hom (よ F∘ πₚ C X) _ (Map→cocone-under X f)
      g' .hom = g
      g' .commutes o = sym $ ext $ unext $ sep $ NT
        (λ i a → P.₁ a (o .section))
        (λ x y h → ext λ a → P.F-∘ _ _ # o .section)
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
