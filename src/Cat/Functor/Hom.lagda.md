```agda
open import Cat.Diagram.Colimit.Base
open import Cat.Instances.Functor
open import Cat.Instances.Product
open import Cat.Diagram.Initial
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Instances.Elements as El
import Cat.Reasoning

module Cat.Functor.Hom {o h} (C : Precategory o h) where
```

# The Hom functor

We prove that the assignment of $\hom$-sets in a `Precategory`{.Agda}
$\ca{C}$ is a `functor`{.Agda}, specifically a bifunctor from $\ca{C}\op
\times_\cat \ca{C}$ to $\sets$. The action of $(f, h)$ on a morphism $g$
is given by $h \circ g \circ f$; Since $f$ is acting by precomposition,
the first coordinate is contravariant ($\ca{C}\op$).

<!--
```agda
open import Cat.Reasoning C
open Functor
open _=>_
private variable
  a b : Ob
```
-->

```agda
Hom[-,-] : Functor ((C ^op) ×ᶜ C) (Sets h)
Hom[-,-] .F₀ (a , b) = Hom a b , Hom-set a b
Hom[-,-] .F₁ (f , h) g = h ∘ g ∘ f
Hom[-,-] .F-id = funext λ x → ap (_ ∘_) (idr _) ∙ idl _
Hom[-,-] .F-∘ (f , h) (f' , h') = funext λ where
  g → (h ∘ h') ∘ g ∘ f' ∘ f ≡⟨ solve C ⟩
      h ∘ (h' ∘ g ∘ f') ∘ f ∎
```

We also can define "partially applied" versions of the hom functor:
```agda
Hom[_,-] : Ob → Functor C (Sets h)
Hom[ x ,-] .F₀ y = Hom x y , Hom-set x y
Hom[ x ,-] .F₁ f g = f ∘ g
Hom[ x ,-] .F-id = funext (λ f → idl f)
Hom[ x ,-] .F-∘ f g = funext λ h → sym (assoc f g h)
```


## The Yoneda embedding

Abstractly and nonsensically, one could say that the Yoneda embedding
`よ`{.Agda} is the [exponential transpose] of `flipping`{.Agda
ident=Flip} the `Hom[-,-]`{.Agda} [bifunctor]. However, this
construction generates _awful_ terms, so in the interest of
computational efficiency we build up the functor explicitly.

[exponential transpose]: Cat.Instances.Functor.html#currying
[bifunctor]: Cat.Functor.Bifunctor.html

```agda
module _ where private
  よ : Functor C (Cat[ C ^op , Sets h ])
  よ = Curry Flip where
    open import
      Cat.Functor.Bifunctor {C = C ^op} {D = C} {E = Sets h} Hom[-,-]
```

We can describe the object part of this functor as taking an object $c$
to the functor $\hom(-,c)$ of map into $c$, with the transformation
$\hom(x,y) \to \hom(x,z)$ given by precomposition.

```agda
よ₀ : Ob → Functor (C ^op) (Sets h)
よ₀ c .F₀ x    = Hom x c , Hom-set _ _
よ₀ c .F₁ f    = _∘ f
よ₀ c .F-id    = funext idr
よ₀ c .F-∘ f g = funext λ h → assoc _ _ _

```

We also define a synonym for よ₀ to better line up with the covariant
direction.

```agda
Hom[-,_] : Ob → Functor (C ^op) (Sets h)
Hom[-,_] x = よ₀ x
```

The morphism part takes a map $f$ to the transformation given by
postcomposition; This is natural because we must show $f \circ x \circ g
= (f \circ x) \circ g$, which is given by associativity in $C$.

```agda
よ₁ : Hom a b → よ₀ a => よ₀ b
よ₁ f .η _ g            = f ∘ g
よ₁ f .is-natural x y g = funext λ x → assoc f x g
```

The other category laws from $\ca{C}$ ensure that this assigment of
natural transformations is indeed functorial:

```agda
よ : Functor C Cat[ C ^op , Sets h ]
よ .F₀      = よ₀
よ .F₁      = よ₁
よ .F-id    = Nat-path λ _ i g → idl g i
よ .F-∘ f g = Nat-path λ _ i h → assoc f g h (~ i)
```

The morphism mapping `よ₁`{.Agda} has an inverse, given by evaluating the
natural transformation with the identity map; Hence, the Yoneda
embedding functor is fully faithful.

```agda
よ-is-fully-faithful : is-fully-faithful よ
よ-is-fully-faithful = is-iso→is-equiv isom where
  open is-iso

  isom : is-iso よ₁
  isom .inv nt = nt .η _ id
  isom .rinv nt = Nat-path λ c → funext λ g →
    happly (sym (nt .is-natural _ _ _)) _ ∙ ap (nt .η c) (idl g)
  isom .linv _ = idr _
```


## The Coyoneda Lemma

The Coyoneda lemma is, like its dual, a statement about presheaves.  It
states that "every presheaf is a colimit of representables", which, in
less abstract terms, means that every presheaf arises as some way of
gluing together a bunch of (things isomorphic to) hom functors!

```agda
module _ (P : Functor (C ^op) (Sets h)) where
  private
    module P = Functor P

  open El C P
  open Element
  open Element-hom
```

We start by fixing some presheaf $P$, and constructing a `Cocone`{.Agda}
whose coapex is $P$. This involves a clever choice of diagram category:
specifically, the [category of elements] of $P$. This may seem like a
somewhat odd choice, but recall that the data contained in $\int P$ is
the _same_ data as $P$, just melted into a soup of points.  The cocone
we construct will then glue all those points back together into $P$.

[category of elements]: Cat.Instances.Elements.html

This is done by projecting out of $\int P$ into $\ca{C}$ via the
[canonical projection], and then embedding $\ca{C}$ into the category of
presheaves over $\ca{C}$ via the yoneda embedding. Concretely, what this
diagram gives us is a bunch of copies of the hom functor, one for each
$px : P(X)$. Then, to construct the injection map, we can just use the
(contravariant) functorial action of $P$ to take a $px : P(X)$ and a $f
: Hom(A, X)$ to a $P(A)$. This map is natural by functoriality of $P$.

[canonical projection]: Cat.Instances.Elements.html#Projection


```agda
  Reassemble : Cocone (よ F∘ πₚ)
  Reassemble .Cocone.coapex = P
  Reassemble .Cocone.ψ x .η y f = P.F₁ f (x .section)
  Reassemble .Cocone.ψ x .is-natural y z f =
    funext (λ g → happly (P.F-∘ f g) (x .section))
  Reassemble .Cocone.commutes {x = x} {y = y} f =
    Nat-path λ z → funext λ g →
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

```agda
  coyoneda : is-colimit (よ F∘ πₚ) Reassemble
  coyoneda K = contr (cocone-hom universal factors) unique
    where
      module K = Cocone K
      module ∫ = Precategory ∫
      module Reassemble = Cocone Reassemble
      open Cocone-hom
```

We start by constructing the universal map from $P$ into the coapex of
some other cocone $K$. The components of this natural transformation are
obtained in a similar manner to the yoneda lemma; we bundle up the data
to construct an object of $\int P$, and then apply the function we
construct to the identity morphism. Naturality follows from the fact
that $K$ is a cocone, and the components of $K$ are natural.

```agda
      universal : P => K.coapex
      universal .η x px = K.ψ (elem x px) .η x id
      universal .is-natural x y f = funext λ px →
        K.ψ (elem y (P.F₁ f px)) .η y id        ≡˘⟨ (λ i → K.commutes (induce f px) i .η y id) ⟩
        K.ψ (elem x px) .η y (f ∘ id)           ≡⟨ ap (K.ψ (elem x px) .η y) id-comm ⟩
        K.ψ (elem x px) .η y (id ∘ f)           ≡⟨ happly (K.ψ (elem x px) .is-natural x y f) id ⟩
        F₁ K.coapex f (K.ψ (elem x px) .η x id) ∎
```

Next, we need to show that this morphism factors each of the components
of $K$. The tricky bit of the proof here is that we need to use
`induce`{.Agda} to regard `f` as a morphism in the category of elements.

```agda
      factors : ∀ o → universal ∘nt Reassemble.ψ o ≡ K.ψ o
      factors o = Nat-path λ x → funext λ f →
        K.ψ (elem x (P.F₁ f (o .section))) .η x id ≡˘⟨ (λ i → K.commutes (induce f (o .section)) i .η x id) ⟩
        K.ψ o .η x (f ∘ id)                        ≡⟨ ap (K.ψ o .η x) (idr f) ⟩
        K.ψ o .η x f ∎
```

Finally, uniqueness: This just follows by the commuting conditions on
`α`.

```agda
      unique : (α : Cocone-hom (よ F∘ πₚ) Reassemble K)
             → cocone-hom universal factors ≡ α
      unique α = Cocone-hom-path (よ F∘ πₚ) $ Nat-path λ x → funext λ px →
        K.ψ (elem x px) .η x id                        ≡˘⟨ (λ i → α .commutes (elem x px) i .η x id) ⟩
        α .hom .η x (Reassemble.ψ (elem x px) .η x id) ≡⟨ ap (α .hom .η x) (happly (P.F-id) px) ⟩
        α .hom .η x px ∎
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
fact that $\id{id}$ is initial the coslice category under $P$.

```agda
    Map→cocone-under : Cocone (よ F∘ πₚ)
    Map→cocone-under .coapex = Y

    Map→cocone-under .ψ (elem ob sect) .η x i = f .η x (P.₁ i sect)
    Map→cocone-under .ψ (elem ob sect) .is-natural x y h = funext λ a →
      f .η _ (P.₁ (a ∘ h) sect)   ≡⟨ happly (f .is-natural _ _ _) _ ⟩
      Y.₁ (a ∘ h) (f .η _ sect)   ≡⟨ happly (Y.F-∘ _ _) _ ⟩
      Y.₁ h (Y.₁ a (f .η _ sect)) ≡˘⟨ ap (Y .F₁ h) (happly (f .is-natural _ _ _) _) ⟩
      Y.₁ h (f .η _ (P.₁ a sect)) ∎

    Map→cocone-under .commutes {x} {y} o = Nat-path λ i → funext λ a → ap (f .η _) $
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
    open El.Element
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
    → ( ∀ {A : Ob} (h : よ₀ A => X) → f PSh.∘ h ≡ g PSh.∘ h )
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
    ap hom $ is-contr→is-prop (coyoneda X (Map→cocone-under X f)) f′ g′ where
      f′ : Cocone-hom (よ F∘ El.πₚ C X) (Reassemble X) (Map→cocone-under X f)
      f′ .hom = f
      f′ .commutes o = Nat-path (λ _ → refl)

      g′ : Cocone-hom (よ F∘ El.πₚ C X) (Reassemble X) (Map→cocone-under X f)
      g′ .hom = g
      g′ .commutes o = Nat-path λ x → ap (λ e → e .η x) $ sym $ sep $
        NT (λ i a → P.₁ a (o .section)) λ x y h →
          funext λ _ → happly (P.F-∘ _ _) _
```

An immediate consequence is that, since any pair of maps $f, g : X \to
Y$ in $\ca{C}$ extend to maps $\yo(f), \yo(g) : \yo(X) \to \yo(Y)$, and
the functor $\yo(-)$ is fully faithful, two maps in $\ca{C}$ are equal
iff. they agree on all generalised elements:

```agda
private module _ where private
  よ-cancelr
    : ∀ {X Y : Ob} {f g : Hom X Y}
    → (∀ {Z} (h : Hom Z X) → f ∘ h ≡ g ∘ h)
    → f ≡ g
  よ-cancelr sep =
    fully-faithful→faithful {F = よ} よ-is-fully-faithful $
      Representables-generate-presheaf λ h → Nat-path λ x → funext λ a →
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
