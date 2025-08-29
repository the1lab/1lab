<!--
```agda
open import Cat.Functor.Adjoint.Reflective
open import Cat.Functor.Properties
open import Cat.Diagram.Terminal
open import Cat.Functor.Adjoint
open import Cat.Morphism.Class
open import Cat.Morphism.Lifts
open import Cat.Prelude

import Cat.Functor.Reasoning
import Cat.Reasoning
```
-->

```agda
module Cat.Morphism.Orthogonal where
```

# Orthogonal maps {defines="left-orthogonal right-orthogonal orthogonality"}

A pair of maps $f : a \to b$ and $g : c \to d$ are called
**orthogonal**, written $f \ortho g$^[Though hang tight for a note on
formalised notation], if for every $u, v$ fitting into a commutative
diagram like

~~~{.quiver}
\[\begin{tikzcd}
  a && b \\
  \\
  c && {d\text{,}}
  \arrow["u", from=1-1, to=1-3]
  \arrow["v", from=3-1, to=3-3]
  \arrow["f"', from=1-1, to=3-1]
  \arrow["g", from=1-3, to=3-3]
  \arrow[dashed, from=3-1, to=1-3]
\end{tikzcd}\]
~~~

the space of [[liftings]] $c \to b$ (dashed) which commute with everything is
[[contractible]]. We will also speak of orthogonality of an object and a
morphism, a morphism and a class of morphisms, and so on.

:::{.note}
In the formalisation, we will write `Orthogonal`{.Agda} to denote all of the
aforementioned orthogonality properties.
:::

<!--
```agda
module _ {o ℓ} (C : Precategory o ℓ) where
  open Cat.Reasoning C
  open Terminal
  private
    variable
      a b c d x y : ⌞ C ⌟
      f g h u v : Hom a b
```
-->

If the ambient category $\cC$ has enough co/limits,
being orthogonal to an object is equivalent to being orthogonal to a
morphism. For example, $f \ortho X$ iff. $f \ortho \mathop{!}_X$, where
$!_X : X \to 1$ is the unique map from $X$ into the [[terminal object]].

```agda
  object-orthogonal-!-orthogonal
    : ∀ {X : Ob} (T : Terminal C) (f : Hom a b)
    → Orthogonal C f X ≃ Orthogonal C f (! T {X})
```

The proof is mostly a calculation, so we present it without a lot of comment.

```agda
  object-orthogonal-!-orthogonal {X = X} T f =
    prop-ext! fwd bwd
    where
      module T = Terminal T

      fwd : Orthogonal C f X → Orthogonal C f (! T)
      fwd f⊥X u v sq .centre = f⊥X u .centre .fst , f⊥X u .centre .snd , T.!-unique₂ _ _
      fwd f⊥X u v sq .paths m = Σ-prop-path! (ap fst (f⊥X u .paths (m .fst , m .snd .fst)))

      bwd : Orthogonal C f (! T) → Orthogonal C f X
      bwd f⊥! u .centre =  f⊥! u T.! (T.!-unique₂ _ _) .centre .fst , f⊥! u T.! (T.!-unique₂ _ _) .centre .snd .fst
      bwd f⊥! u .paths (w , eq) = Σ-prop-path! (ap fst (f⊥! _ _ _ .paths (w , eq , (T.!-unique₂ _ _))))
```

As a passing observation we note that if $f \ortho X$ and $X \cong Y$,
then $f \ortho Y$. Of course, this is immediate in categories, but it
holds in the generality of precategories.

```agda
  obj-orthogonal-iso : ∀ {a b} {X Y} (f : Hom a b) → X ≅ Y → Orthogonal C f X → Orthogonal C f Y
```

<!--
```agda
  obj-orthogonal-iso f x≅y f⊥X a =
    contr
      ( g.to ∘ contr' .centre .fst
      , pullr (contr' .centre .snd) ∙ cancell g.invl )
      λ x → Σ-prop-path! $
        ap₂ _∘_ refl (ap fst (contr' .paths (g.from ∘ x .fst , pullr (x .snd))))
        ∙ cancell g.invl
    where
      module g = _≅_ x≅y
      contr' = f⊥X (g.from ∘ a)
```
-->

A slightly more interesting lemma is that, if $f$ is orthogonal to
itself, then it is an isomorphism:

```agda
  self-orthogonal→invertible : ∀ {a b} (f : Hom a b) → Orthogonal C f f → is-invertible f
  self-orthogonal→invertible f f⊥f =
    make-invertible (gpq .fst) (gpq .snd .snd) (gpq .snd .fst)
    where
      gpq = f⊥f id id (idl _ ∙ intror refl) .centre
```

If $f$ is an epi or $g$ is a mono, then the mere existence of
_any_ lift is enough to establish that $f \ortho g$.

```agda
  left-epic-lift→orthogonal
    : (g : Hom c d)
    → is-epic f → Lifts C f g → Orthogonal C f g
  left-epic-lift→orthogonal g f-epi lifts u v vf=gu =
    is-prop∥∥→is-contr (left-epic→lift-is-prop C f-epi vf=gu) (lifts u v vf=gu)

  right-monic-lift→orthogonal
    : (f : Hom a b)
    → is-monic g → Lifts C f g → Orthogonal C f g
  right-monic-lift→orthogonal f g-mono lifts u v vf=gu =
    is-prop∥∥→is-contr (right-monic→lift-is-prop C g-mono vf=gu) (lifts u v vf=gu)
```

<!--
```agda
  left-epic-lift→orthogonal-class
    : ∀ {κ} (R : Arrows C κ)
    → is-epic f → Lifts C f R → Orthogonal C f R
  left-epic-lift→orthogonal-class R f-epic lifts r r∈R =
    left-epic-lift→orthogonal r f-epic (lifts r r∈R)

  right-monic-lift→orthogonal-class
    : ∀ {κ} (L : Arrows C κ)
    → is-monic f → Lifts C L f → Orthogonal C L f
  right-monic-lift→orthogonal-class L f-epic lifts l l∈L =
    right-monic-lift→orthogonal l f-epic (lifts l l∈L)
```
-->

As a corollary, we get that isomorphisms are left and right orthogonal to every
other morphism.

```agda
  invertible→left-orthogonal : (g : Hom c d) → Orthogonal C Isos g
  invertible→left-orthogonal g f f-inv =
    left-epic-lift→orthogonal g (invertible→epic f-inv) $
    invertible-left-lifts C f f-inv

  invertible→right-orthogonal : (f : Hom a b) → Orthogonal C f Isos
  invertible→right-orthogonal f g g-inv =
    right-monic-lift→orthogonal f (invertible→monic g-inv) $
    invertible-right-lifts C g g-inv
```

Phrased another way, the class of isomorphisms is left and right orthogonal
to every other class.

```agda
  isos-left-orthogonal : ∀ {κ} (R : Arrows C κ) → Orthogonal C Isos R
  isos-left-orthogonal R f f-inv r r∈R = invertible→left-orthogonal r f f-inv

  isos-right-orthogonal : ∀ {κ} (L : Arrows C κ) → Orthogonal C L Isos
  isos-right-orthogonal L l l∈L f f-inv = invertible→right-orthogonal l f f-inv
```

<!--
```agda
  invertible→left-orthogonal-class : ∀ {κ} (R : Arrows C κ) → is-invertible f → Orthogonal C f R
  invertible→left-orthogonal-class R f-inv r _ = invertible→left-orthogonal r _ f-inv

  invertible→right-orthogonal-class : ∀ {κ} (L : Arrows C κ) → is-invertible f → Orthogonal C L f
  invertible→right-orthogonal-class L f-inv l _ = invertible→right-orthogonal l _ f-inv
```
-->

<!--
```agda
  orthogonal→lifts-against : Orthogonal C f g → Lifts C f g
  orthogonal→lifts-against o u v p = pure (o u v p .centre)

  orthogonal→lifts-left-class
    : ∀ {κ} (L : Arrows C κ)
    → Orthogonal C L f → Lifts C L f
  orthogonal→lifts-left-class L L⊥f l l∈L =
    orthogonal→lifts-against (L⊥f l l∈L)

  orthogonal→lifts-right-class
    : ∀ {κ} (R : Arrows C κ)
    → Orthogonal C f R → Lifts C f R
  orthogonal→lifts-right-class R f⊥R r r∈R =
    orthogonal→lifts-against (f⊥R r r∈R)
```
-->

## Regarding reflections

<!--
```agda
module
  _ {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'}
    {r : Functor C D} {ι : Functor D C}
    (r⊣ι : r ⊣ ι) (ι-ff : is-fully-faithful ι)
  where
  private
    module C = Cat.Reasoning C
    module D = Cat.Reasoning D
    module ι = Cat.Functor.Reasoning ι
    module r = Cat.Functor.Reasoning r
    module rι = Cat.Functor.Reasoning (r F∘ ι)
    module ιr = Cat.Functor.Reasoning (ι F∘ r)
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
    : ∀ {X} {a b} {f : C.Hom a b} → D.is-invertible (r.₁ f) → Orthogonal C f (ι.₀ X)
  in-subcategory→orthogonal-to-inverted {X} {A} {B} {f} rf-inv a→x =
    contr (fact , factors) λ { (g , factors') →
      Σ-prop-path! (h≡k factors factors') }
    where
      module rf = D.is-invertible rf-inv
      module η⁻¹ {a} = C.is-invertible (is-reflective→unit-right-is-iso r⊣ι ι-ff {a})
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

        h≡k = C.invertible→monic (is-reflective→unit-right-is-iso r⊣ι ι-ff) _ _ $
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
    : ∀ {X} → (∀ B → Orthogonal C (unit.η B) X) → C.is-invertible (unit.η X)
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
    : ∀ {X B} → C.is-invertible (unit.η X) → Orthogonal C (unit.η B) X
  in-subcategory→orthogonal-to-ηs inv =
    obj-orthogonal-iso C (unit.η _) (C.invertible→iso _ (C.is-invertible-inverse inv)) $
    in-subcategory→orthogonal-to-inverted (is-reflective→left-unit-is-iso r⊣ι ι-ff)
```
