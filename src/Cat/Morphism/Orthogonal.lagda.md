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

# Orthogonal maps

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
contractible.

<!--
```agda
module _ {o ℓ} (C : Precategory o ℓ) where
  private module C = Cr C
```
-->

```agda
  m⊥m : ∀ {a b c d} → C.Hom a b → C.Hom c d → Type _
  m⊥m {b = b} {c = c} f g =
    ∀ {u v} → v C.∘ f ≡ g C.∘ u
    → is-contr (Σ[ w ∈ C.Hom b c ] ((w C.∘ f ≡ u) × (g C.∘ w ≡ v)))
```

We also outline concepts of a map being orthogonal to an object, which
is informally written $f \ortho X$, and an object being orthogonal to a
map $Y \ortho f$.

```agda
  m⊥o : ∀ {a b} → C.Hom a b → C.Ob → Type _
  m⊥o {A} {B} f X = (a : C.Hom A X) → is-contr (Σ[ b ∈ C.Hom B X ] (b C.∘ f ≡ a))

  o⊥m : ∀ {a b} → C.Ob → C.Hom a b → Type _
  o⊥m {A} {B} Y f = (c : C.Hom Y B) → is-contr (Σ[ d ∈ C.Hom Y A ] (f C.∘ d ≡ c))
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
    : ∀ {A B X} (T : Terminal C) (f : C.Hom A B) → m⊥o f X ≃ m⊥m f (! T)
  object-orthogonal-!-orthogonal {X = X} T f =
    prop-ext (hlevel 1) (hlevel 1) to from
    where
      to : m⊥o f X → m⊥m f (! T)
      to f⊥X {u} {v} sq =
        contr (f⊥X u .centre .fst , f⊥X u .centre .snd , !-unique₂ T _ _) λ m →
          Σ-prop-path (λ _ → hlevel 1)
            (ap fst (f⊥X u .paths (m .fst , m .snd .fst)))

      from : m⊥m f (! T) → m⊥o f X
      from f⊥! a = contr
        ( f⊥! {v = ! T} (!-unique₂ T _ _) .centre .fst
        , f⊥! (!-unique₂ T _ _) .centre .snd .fst ) λ x →
          Σ-prop-path (λ _ → hlevel 1)
            (ap fst (f⊥! _ .paths (x .fst , x .snd , !-unique₂ T _ _)))
```

As a passing observation we note that if $f \ortho X$ and $X \cong Y$,
then $f \ortho Y$. Of course, this is immediate in categories, but it
holds in the generality of precategories.

```agda
  m⊥-iso : ∀ {a b} {X Y} (f : C.Hom a b) → X C.≅ Y → m⊥o f X → m⊥o f Y
```

<!--
```agda
  m⊥-iso f x≅y f⊥X a =
    contr
      ( g.to C.∘ contr' .centre .fst
      , C.pullr (contr' .centre .snd) ∙ C.cancell g.invl )
      λ x → Σ-prop-path (λ _ → hlevel 1) $
        ap₂ C._∘_ refl (ap fst (contr' .paths (g.from C.∘ x .fst , C.pullr (x .snd))))
        ∙ C.cancell g.invl
    where
      module g = C._≅_ x≅y
      contr' = f⊥X (g.from C.∘ a)
```
-->

A slightly more interesting lemma is that, if $f$ is orthogonal to
itself, then it is an isomorphism:

```agda
  self-orthogonal→is-iso : ∀ {a b} (f : C.Hom a b) → m⊥m f f → C.is-invertible f
  self-orthogonal→is-iso f f⊥f =
    C.make-invertible (gpq .fst) (gpq .snd .snd) (gpq .snd .fst)
    where
      gpq = f⊥f (C.idl _ ∙ C.intror refl) .centre
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
      Σ-prop-path (λ _ → hlevel 1) (h≡k factors factors') }
    where
      module rf = D.is-invertible rf-inv
      module η⁻¹ {a} = C.is-invertible (is-reflective→unit-G-is-iso r⊣ι ι-ff {a})
```

Observe that, since $r \dashv \iota$ is a reflective subcategory, every
unit morphism $\eta_{\iota X}$ is an isomorphism; We define a morphism
$b : \iota r(A) \to \iota X$ as the composite

$$
\iota r(A) \xto{\iota r(a)} \iota r \iota(X) \xto{\eta^{-1}} \iota(X)\text{,}
$$

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
B \xto{\eta} \iota r(B) \xto{\iota(r(f)^{-1})} \iota r(A) \xto{b} \iota(X)\text{,}
$$

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
\eta_{\iota X} h = \iota r(h) \eta = \iota r(k) \eta = \eta_{\iota X} k\text{,}
$$

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
      x = ortho X (C .Precategory.id) .centre .fst
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
