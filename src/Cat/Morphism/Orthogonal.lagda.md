<!--
```agda
open import Cat.Functor.Adjoint.Reflective
open import Cat.Functor.Properties
open import Cat.Diagram.Terminal
open import Cat.Functor.Adjoint
open import Cat.Prelude

import Cat.Functor.Reasoning as Func
import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Morphism.Orthogonal where
```

# Orthogonal maps {defines="left-orthogonal right-orthogonal orthogonality"}

A pair of maps $f : a \to b$ and $g : c \ to d$ are called
**orthogonal**, written $f \ortho g$^[Though hang tight for a note on
formalised notation], if for every $u, v$ fitting into a commutative
diagram like

~~~{.quiver}
\[\begin{tikzcd}
  a && b \\
  \\
  c && {d\text{,}}
  \arrow["f", from=1-1, to=1-3]
  \arrow["g", from=3-1, to=3-3]
  \arrow["u"', from=1-1, to=3-1]
  \arrow["v", from=1-3, to=3-3]
	\arrow[dashed, from=1-3, to=3-1]
\end{tikzcd}\]
~~~

the space of arrows $c \to b$ (dashed) which commute with everything is
contractible. We refer to the type of these dashed arrows as a
`Lifting`{.Agda}, and this type is parametrised over all maps in the
square.

<!--
```agda
module _ {o ℓ} (C : Precategory o ℓ) where
  private
    module C = Cr C
    variable
      a b c d : ⌞ C ⌟
      f g h u v : C.Hom a b
  open C using (Ob ; Hom ; _∘_ ; _≅_)
```
-->

```agda
  Lifting
    : (f : Hom a b) (g : Hom c d) (u : Hom a c) (v : Hom b d)
    → Type _
  Lifting f g u v = Σ[ w ∈ Hom _ _ ] w ∘ f ≡ u × g ∘ w ≡ v

  m⊥m : Hom a b → Hom c d → Type _
  m⊥m {b = b} {c = c} f g =
    ∀ {u v} → v ∘ f ≡ g ∘ u
    → is-contr (Lifting f g u v)
```

:::{.definition #lifts-against}
In some of the proofs below, we'll also need a name for a weakening of
orthogonality, where the requirement that lifts are unique is dropped.
We say $f$ *lifts against* $g$ if there is a map assigning lifts to
every commutative squares with opposing $f$ and $g$ faces, as above.

```agda
  lifts-against : (f : Hom a b) (g : Hom c d) → Type _
  lifts-against f g = ∀ {u v} → v ∘ f ≡ g ∘ u → Lifting f g u v
```
:::

We also outline concepts of a map being orthogonal to an object, which
is informally written $f \ortho X$, and an object being orthogonal to a
map $Y \ortho f$.

```agda
  m⊥o : Hom a b → ⌞ C ⌟ → Type _
  m⊥o {a} {b} f X = (a : Hom a X) → is-contr (Σ[ b ∈ Hom b X ] (b ∘ f ≡ a))

  o⊥m : ⌞ C ⌟ → Hom a b → Type _
  o⊥m {a} {b} Y f = (c : Hom Y b) → is-contr (Σ[ d ∈ Hom Y a ] (f ∘ d ≡ c))
```

:::{.note}
In the formalisation, we don't write $\bot$ infix, since it
must be explicitly applied to the category in which the morphisms live.
Thus, we define three distinct predicates expressing orthogonality:
`m⊥m`{.Agda} ("map-map"), `m⊥o`{.Agda} ("map-object"), and `o⊥m`
("object-map"). If the ambient category $\cC$ has enough co/limits,
being orthogonal to an object is equivalent to being orthogonal to an
object. For example, $f \ortho X$ iff. $f \ortho \mathop{!}_X$, where
$!_X : X \to 1$ is the unique map from $X$ into the [[terminal object]].
:::

<!--
```agda
  open Terminal
  open is-iso
```
-->

The proof is mostly a calculation, so we present it without a lot of comment.

```agda
  object-orthogonal-!-orthogonal
    : ∀ {X} (T : Terminal C) (f : Hom a b) → m⊥o f X ≃ m⊥m f (! T)
  object-orthogonal-!-orthogonal {X = X} T f =
    prop-ext (hlevel 1) (hlevel 1) to from
    where
      to : m⊥o f X → m⊥m f (! T)
      to f⊥X {u} {v} sq =
        contr (f⊥X u .centre .fst , f⊥X u .centre .snd , !-unique₂ T _ _) λ m →
          Σ-prop-path! (ap fst (f⊥X u .paths (m .fst , m .snd .fst)))

      from : m⊥m f (! T) → m⊥o f X
      from f⊥! a = contr
        ( f⊥! {v = ! T} (!-unique₂ T _ _) .centre .fst
        , f⊥! (!-unique₂ T _ _) .centre .snd .fst ) λ x → Σ-prop-path!
          (ap fst (f⊥! _ .paths (x .fst , x .snd , !-unique₂ T _ _)))
```

As a passing observation we note that if $f \ortho X$ and $X \cong Y$,
then $f \ortho Y$. Of course, this is immediate in categories, but it
holds in the generality of precategories.

```agda
  m⊥-iso : ∀ {a b} {X Y} (f : Hom a b) → X ≅ Y → m⊥o f X → m⊥o f Y
```

<!--
```agda
  m⊥-iso f x≅y f⊥X a =
    contr
      ( g.to ∘ contr' .centre .fst
      , C.pullr (contr' .centre .snd) ∙ C.cancell g.invl )
      λ x → Σ-prop-path! $
        ap₂ _∘_ refl (ap fst (contr' .paths (g.from ∘ x .fst , C.pullr (x .snd))))
        ∙ C.cancell g.invl
    where
      module g = C._≅_ x≅y
      contr' = f⊥X (g.from ∘ a)
```
-->

A slightly more interesting lemma is that, if $f$ is orthogonal to
itself, then it is an isomorphism:

```agda
  self-orthogonal→invertible : ∀ {a b} (f : Hom a b) → m⊥m f f → C.is-invertible f
  self-orthogonal→invertible f f⊥f =
    C.make-invertible (gpq .fst) (gpq .snd .snd) (gpq .snd .fst)
    where
      gpq = f⊥f (C.idl _ ∙ C.intror refl) .centre
```

For the next few lemmas, consider a square of the following form, where
$l$ and $k$ are both lifts of the outer square.

~~~{.quiver}
\begin{tikzcd}
  a && b \\
  \\
  c && d
  \arrow["f", from=1-1, to=1-3]
  \arrow["u"', from=1-1, to=3-1]
  \arrow["l"', shift right, from=1-3, to=3-1]
  \arrow["k", shift left, from=1-3, to=3-1]
  \arrow["v", from=1-3, to=3-3]
  \arrow["g"', from=3-1, to=3-3]
\end{tikzcd}
~~~

If $f$ is an [[epimorphism]], then $l = k$. In more succinct terms, the
type of lifts of such a square is a proposition.

```agda
  left-epic→lift-is-prop
    : C.is-epic f → v C.∘ f ≡ g C.∘ u → is-prop (Lifting f g u v)
  left-epic→lift-is-prop f-epi vf=gu (l , lf=u , _) (k , kf=u , _) =
    Σ-prop-path! (f-epi l k (lf=u ∙ sym kf=u))
```

Dually, if $g$ is a [[monomorphism]], then we the type of lifts is also
a propostion.

```agda
  right-monic→lift-is-prop
    : C.is-monic g → v C.∘ f ≡ g C.∘ u → is-prop (Lifting f g u v)
  right-monic→lift-is-prop g-mono vf=gu (l , _ , gl=v) (k , _ , gk=v) =
    Σ-prop-path! (g-mono l k (gl=v ∙ sym gk=v))
```

As a corollary, if $f$ is an epi or $g$ is a mono, then it is sufficient
to find _any_ lift to establish that $f \bot g$.

```agda
  left-epic-lift→orthogonal
    : (g : C.Hom c d)
    → C.is-epic f → lifts-against f g → m⊥m f g
  left-epic-lift→orthogonal g f-epi lifts vf=gu =
    is-prop∙→is-contr (left-epic→lift-is-prop f-epi vf=gu) (lifts vf=gu)

  right-monic-lift→orthogonal
    : (f : C.Hom a b)
    → C.is-monic g → lifts-against f g → m⊥m f g
  right-monic-lift→orthogonal f g-mono lifts vf=gu =
    is-prop∙→is-contr (right-monic→lift-is-prop g-mono vf=gu) (lifts vf=gu)
```

Isomorphisms are left and right orthogonal to every other morphism.

```agda
  invertible→left-orthogonal  : (g : C.Hom c d) → C.is-invertible f → m⊥m f g
  invertible→right-orthogonal : (f : C.Hom a b) → C.is-invertible g → m⊥m f g
```

We will focus our attention on the left orthogonal case, as the proof
for right orthogonality is completely dual. Suppose that $f$ is invertible,
and $g$ is an arbitrary morphism. Invertible morphisms are epis, so it
suffices to establish the existence of lifts to prove that $f$ is orthogonal
to $g$. Luckily, these lifts are easy to find: if we have some square
$v \circ f = u \circ g$, then $u \circ f^{-1}$ fits perfectly along the
diagonal:

~~~{.quiver}
\begin{tikzcd}
  a && b \\
  \\
  c && d
  \arrow["f", from=1-1, to=1-3]
  \arrow["u"', from=1-1, to=3-1]
  \arrow["{u \circ f^{-1}}"{description}, from=1-3, to=3-1]
  \arrow["v", from=1-3, to=3-3]
  \arrow["g"', from=3-1, to=3-3]
\end{tikzcd}
~~~

A short calculation verifies that $u \circ f^{-1}$ is indeed a lift.

```agda
  invertible→left-orthogonal {f = f} g f-inv =
    left-epic-lift→orthogonal g (C.invertible→epic f-inv) λ {u} {v} vf=gu →
      u ∘ f.inv ,
      C.cancelr f.invr ,
      Equiv.from
        (g ∘ u ∘ f.inv ≡ v   ≃⟨ C.reassocl e⁻¹ ∙e C.pre-invr f-inv ⟩
         g ∘ u ≡ v ∘ f       ≃⟨ sym-equiv ⟩
         v ∘ f ≡ g ∘ u       ≃∎)
        vf=gu
    where module f = C.is-invertible f-inv
```

<details>
<summary>The proof of right orthogonality follows the exact same plan,
so we omit the details.
</summary>
```agda
  invertible→right-orthogonal {g = g} f g-inv =
    right-monic-lift→orthogonal f (C.invertible→monic g-inv) λ {u} {v} vf=gu →
      g.inv ∘ v ,
      Equiv.from
        ((g.inv ∘ v) ∘ f ≡ u ≃⟨ C.reassocl ∙e C.pre-invl g-inv ⟩
          v ∘ f ≡ g ∘ u      ≃∎)
        vf=gu ,
      C.cancell g.invl
    where module g = C.is-invertible g-inv
```
</details>

<!--
```agda
  orthogonal→lifts-against : m⊥m f g → lifts-against f g
  orthogonal→lifts-against o p = o p .centre
```
-->

We also have the following two properties, which state that "lifting
against" is, as a property of morphisms, closed under composition on
both the left and the right. To understand the proof, it's helpful to
visualise the inputs in a diagram. Suppose we have $f : b \to c$, $g : a
\to b$, $h : x \to y$, and assume that both $f$ and $g$ lift against
$h$. Showing that $fg$ lifts against $h$ amounts to finding a diagonal
for the rectangle

~~~{.quiver}
\[\begin{tikzcd}[ampersand replacement=\&]
  a \&\& b \&\& c \\
  \\
  x \&\&\&\& y
  \arrow["g", from=1-1, to=1-3]
  \arrow["u"', from=1-1, to=3-1]
  \arrow["f", from=1-3, to=1-5]
  \arrow["v", from=1-5, to=3-5]
  \arrow["h"', from=3-1, to=3-5]
\end{tikzcd}\]
~~~

under the assumption that $vfg = hu$. We'll populate this diagram a bit
by observing that, by composing the $f$ and $v$ edges together, we have
a commutative square with faces $g$, $vf$, $u$ and $h$ --- and since $g$
lifts against $h$, this implies that we have a diagonal map $w$, which
appears dashed in

~~~{.quiver}
\[\begin{tikzcd}[ampersand replacement=\&]
  a \&\& b \&\& c \\
  \\
  x \&\&\&\& {y.}
  \arrow["g", from=1-1, to=1-3]
  \arrow["u"', from=1-1, to=3-1]
  \arrow["f", from=1-3, to=1-5]
  \arrow["w"', dashed, from=1-3, to=3-1]
  \arrow["v", from=1-5, to=3-5]
  \arrow["h"', from=3-1, to=3-5]
\end{tikzcd}\]
~~~

This map satisfies $wg = u$, and, importantly, $hw = vf$. This latter
equation implies that we can now treat the right half of the diagram as
another square, with faces $f$, $h$, $w$, and $v$. Since $f$ *also*
lifts against $h$, this implies that we can find the *dotted* map $t$ in
the diagram

~~~{.quiver}
\[\begin{tikzcd}[ampersand replacement=\&]
  a \&\& b \&\& c \\
  \\
  x \&\&\&\& y
  \arrow["g", from=1-1, to=1-3]
  \arrow["u"', from=1-1, to=3-1]
  \arrow["f", from=1-3, to=1-5]
  \arrow["w"', dashed, from=1-3, to=3-1]
  \arrow["t", dotted, from=1-5, to=3-1]
  \arrow["v", from=1-5, to=3-5]
  \arrow["h"', from=3-1, to=3-5]
\end{tikzcd}\]
~~~

satisfying $tf = w$ and $mt = v$. The map $t$ fits the *type* of fillers
for our original rectangle, but we must still show that it makes both
triangles commute. But this is easy: we have $tfg = wg = u$ by a short
calculation and $ht = w$ immediately.

```agda
  ∘l-lifts-against : lifts-against f h → lifts-against g h → lifts-against (f ∘ g) h
  ∘l-lifts-against f-lifts g-lifts vfg=hu =
    let (w , wg=u , hw=vf) = g-lifts (C.reassocl.from vfg=hu)
        (t , tf=w , ht=v)  = f-lifts (sym hw=vf)
    in t , C.pulll tf=w ∙ wg=u , ht=v
```

This proof dualises almost term-for-term the case where we're composing
on the bottom face, i.e., when we have some $f$ which lifts against both
$g$ and $h$, and we want to show $f$ lifts against $gh$.

```agda
  ∘r-lifts-against : lifts-against f g → lifts-against f h → lifts-against f (g ∘ h)
  ∘r-lifts-against f-lifts g-lifts ve=fgu =
    let (w , we=gu , fw=v) = f-lifts (C.reassocr.to ve=fgu)
        (t , te=u , gt=w)  = g-lifts we=gu
    in t , te=u , C.pullr gt=w ∙ fw=v
```

## Regarding reflections

<!--
```agda
module
  _ {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'}
    {r : Functor C D} {ι : Functor D C}
    (r⊣ι : r ⊣ ι) (ι-ff : is-fully-faithful ι)
  where
  private
    module C = Cr C
    module D = Cr D
    module ι = Func ι
    module r = Func r
    module rι = Func (r F∘ ι)
    module ιr = Func (ι F∘ r)
  open _⊣_ r⊣ι
```
-->

Let $r \dashv \iota : \cD \adj \cC$ be an arbitrary [[reflective
subcategory]]. Speaking abstractly, there is a "universal" choice of
test for whether an object is "in" the subcategory: Whether the
adjunction unit: $\eta_x : x \to \iota{}r(x)$ is an isomorphism.  The
theory of orthogonality gives a second way to detect this situation.
The proof here is from [@Borceux:vol1, §5.4].

The first thing we observe is that any map $f$ such that $r(f)$ is an
isomorphism is orthogonal to every object in the subcategory:
$f \ortho \iota(X)$. Let $f : a \to b$ be inverted by $r$, and $X$ be
the object. Given a map $a : a \to \iota X$,

```agda
  in-subcategory→orthogonal-to-inverted
    : ∀ {X} {a b} {f : C.Hom a b} → D.is-invertible (r.₁ f) → m⊥o C f (ι.₀ X)
  in-subcategory→orthogonal-to-inverted {X} {A} {B} {f} rf-inv a→x =
    contr (fact , factors) λ { (g , factors') →
      Σ-prop-path! (h≡k factors factors') }
    where
      module rf = D.is-invertible rf-inv
      module η⁻¹ {a} = C.is-invertible (is-reflective→unit-G-is-iso r⊣ι ι-ff {a})
```

Observe that, since $r \dashv \iota$ is a reflective subcategory, every
unit morphism $\eta_{\iota X}$ is an isomorphism; We define a morphism
$b : \iota r(A) \to \iota X$ as the composite

$$
\iota r(A) \xto{\iota r(a)} \iota r \iota(X) \xto{\eta\inv} \iota(X)
$$,

```agda
      b : C.Hom (ι.₀ (r.₀ A)) (ι.₀ X)
      b = η⁻¹.inv C.∘ ι.₁ (r.₁ a→x)
```

satisfying (by naturality of the unit map) the property that $b\eta =
a$. This is an intermediate step in what we have to do: construct a map
$B \to \iota(X)$.

```agda
      p : a→x ≡ b C.∘ unit.η _
      p = sym (C.pullr (sym (unit.is-natural _ _ _)) ∙ C.cancell zag)
```

We define _that_ using the map $b$ we just constructed. It's the composite

$$
B \xto{\eta} \iota r(B) \xto{\iota(r(f)\inv)} \iota r(A) \xto{b} \iota(X)
$$,

and a calculation shows us that this map is indeed a factorisation of
$a$ through $f$.

```agda
      fact : C.Hom B (ι.₀ X)
      fact = b C.∘ ι.₁ rf.inv C.∘ unit.η _

      factors =
        (b C.∘ ι.₁ rf.inv C.∘ unit.η B) C.∘ f      ≡⟨ C.pullr (C.pullr (unit.is-natural _ _ _)) ⟩
        b C.∘ ι.₁ rf.inv C.∘ (ιr.₁ f) C.∘ unit.η A ≡⟨ C.refl⟩∘⟨ C.cancell (ι.annihilate rf.invr) ⟩
        b C.∘ unit.η A                             ≡˘⟨ p ⟩
        a→x                                        ∎
```

The proof that this factorisation is unique is surprisingly totally
independent of the actual map we just constructed: If $hf = a = kf$,
note that we must have $r(h) = r(k)$ (since $r(f)$ is invertible, it is
epic); But then we have

$$
\eta_{\iota X} h = \iota r(h) \eta = \iota r(k) \eta = \eta_{\iota X} k
$$,

and since $\eta_{\iota X}$ is an isomorphism, thus monic, we have $h =
k$.

```agda
      module _ {h k : C.Hom B (ι.₀ X)} (p : h C.∘ f ≡ a→x) (q : k C.∘ f ≡ a→x) where
        rh≡rk : r.₁ h ≡ r.₁ k
        rh≡rk = D.invertible→epic rf-inv (r.₁ h) (r.₁ k) (r.weave (p ∙ sym q))

        h≡k = C.invertible→monic (is-reflective→unit-G-is-iso r⊣ι ι-ff) _ _ $
          unit.η (ι.₀ X) C.∘ h ≡⟨ unit.is-natural _ _ _ ⟩
          ιr.₁ h C.∘ unit.η B  ≡⟨ ap ι.₁ rh≡rk C.⟩∘⟨refl ⟩
          ιr.₁ k C.∘ unit.η B  ≡˘⟨ unit.is-natural _ _ _ ⟩
          unit.η (ι.₀ X) C.∘ k ∎
```

As a partial converse, if an object $X$ is orthogonal to every unit map
(it suffices to be orthogonal to its _own_ unit map), then it lies in
the subcategory:

```agda
  orthogonal-to-ηs→in-subcategory
    : ∀ {X} → (∀ B → m⊥o C (unit.η B) X) → C.is-invertible (unit.η X)
  orthogonal-to-ηs→in-subcategory {X} ortho =
    C.make-invertible x lemma (ortho X C.id .centre .snd)
    where
      x = ortho X C.id .centre .fst
      lemma = unit.η _ C.∘ x             ≡⟨ unit.is-natural _ _ _ ⟩
              ιr.₁ x C.∘ unit.η (ιr.₀ X) ≡⟨ C.refl⟩∘⟨ η-comonad-commute r⊣ι ι-ff ⟩
              ιr.₁ x C.∘ ιr.₁ (unit.η X) ≡⟨ ιr.annihilate (ortho X C.id .centre .snd) ⟩
              C.id                       ∎
```

And the converse to *that* is a specialisation of the first thing we
proved: We established that $f \ortho \iota(X)$ if $f$ is invertible by
the reflection functor, and we know that $\eta$ is invertible by the
reflection functor; It remains to replace $\iota(X)$ with any object for
which $\eta$ is an isomorphism.

```agda
  in-subcategory→orthogonal-to-ηs
    : ∀ {X B} → C.is-invertible (unit.η X) → m⊥o C (unit.η B) X
  in-subcategory→orthogonal-to-ηs inv =
    m⊥-iso C (unit.η _) (C.invertible→iso _ (C.is-invertible-inverse inv))
      (in-subcategory→orthogonal-to-inverted
        (is-reflective→F-unit-is-iso r⊣ι ι-ff))
```
