<!--
```agda
open import Cat.Functor.Adjoint.Unique
open import Cat.Functor.Equivalence
open import Cat.Instances.Functor
open import Cat.Prelude

import Cat.Functor.Reasoning as Fr
import Cat.Reasoning

open Functor
```
-->

```agda
module Cat.Functor.Equivalence.Path where
```

# Paths between categories {defines="path-between-precategories"}

We know that, _in_ a [[univalent category]], paths between objects are
the same thing as isomorphisms. A natural question to follow up is: what
are the paths _between_ univalent categories? We prove that the space of
functors $F : \cC \to \cD$ whose mappings on objects and on morphisms
are both equivalences ("isomorphisms of precategories") is an [[identity
system]] on the space of precategories.

The first thing we need to establish is that an isomorphism of
precategories induces a path between its domain and codomain categories.
This is essentially an application of univalence, done in direct cubical
style. In particular, we use Glue directly rather than `ua` to construct
the path between `Hom`{.Agda} families.

```agda
Precategory-path
  : ∀ {o ℓ} {C D : Precategory o ℓ} (F : Functor C D)
  → is-precat-iso F
  → C ≡ D
Precategory-path {o = o} {ℓ} {C} {D} F p = path where
  module C = Precategory C
  module D = Precategory D
  open is-precat-iso p renaming (has-is-iso to ob≃ ; has-is-ff to hom≃)
```

By assumption, $F$'s action on objects $F_0$ is an equivalence, so by
univalence it induces an equivalence $\cC_0 \equiv \cD_0$. The
path between `Hom`{.Agda}-sets is slightly more complicated. It is,
essentially, the dashed line in the diagram

~~~{.quiver}
\[\begin{tikzcd}
  {\mathbf{Hom}_\mathcal{C}(x,y)} && {\mathbf{Hom}_\mathcal{D}(x,y)} \\
  \\
  {\mathbf{Hom}_\mathcal{D}(F_0x,F_0y)} && {\mathbf{Hom}_\mathcal{D}(x,y)}
  \arrow["{\mathrm{id}}", from=1-3, to=3-3]
  \arrow["{F_1}"', from=1-1, to=3-1]
  \arrow["{\mathrm{Hom}_\mathcal{D}(\unglue x, \unglue y)}"', from=3-1, to=3-3, outer sep=0.5em]
  \arrow[dashed, from=1-1, to=1-3]
\end{tikzcd}\]
~~~

```agda
  obl : ∀ i → Type o
  obl i = ua (F .F₀ , ob≃) i

  hom : PathP (λ i → obl i → obl i → Type ℓ) C.Hom D.Hom
  hom i x y = Glue (D.Hom (unglue x) (unglue y)) λ where
    (i = i0) → C.Hom x y , F .F₁ , hom≃
    (i = i1) → D.Hom x y , id≃
```

Note that $\unglue_{i \lor \neg i}x$ is a term in $\cD_0$ which
evaluates to $F_0(x)$ when $i = i0$ (and thus $x$ has type $\cC_0$) and $x$
when $i = i1$ (and thus $x$ has type $\cD_0$), so that the system
described above can indeed be built. The introduction rule for
`hom`{.Agda} is `hom-glue`{.Agda}: If we have a partial element $\neg i
\vdash f : \hom_\cC(x, y)$ together with an element $g$ of base
type satisfying definitionally $\neg i \vdash F_1(f) = g$, we may glue
$f$ along $g$ to get an element of $\hom_i(x, y)$.

```agda
  hom-glue
    : ∀ i (x y : obl i)
    → (f : PartialP {a = ℓ} (~ i) λ { (i = i0) → C.Hom x y })
    → (g : D.Hom (unglue x) (unglue y)
        [ (~ i) ↦ (λ { (i = i0) → F .F₁ (f 1=1) }) ])
    → hom i x y
  hom-glue i x y f g = attach (∂ i)
    (λ { (i = i0) → f 1=1 ; (i = i1) → outS g })
    (inS (outS g))
```

To obtain these definitional extensions of a morphism in C, we use
homogeneous composition, together with the functor laws. For example,
below, we obtain a line which definitionally extends $\id_{\cC}$ on the
left and $\id_{\cD}$ by gluing $\id_{\cC}$ _against the proof that $F$
preserves identity_.

```agda
  idh : ∀ i x → hom i x x
  idh i x = attach (∂ i) (λ { (i = i0) → _ ; (i = i1) → _ }) (inS (hcomp (∂ i) λ where
    j (i = i0) → F .F-id (~ j)
    j (i = i1) → D.id
    j (j = i0) → D.id))

  circ : ∀ i x y z → hom i y z → hom i x y → hom i x z
  circ i x y z f g = attach (∂ i) (λ { (i = i0) → _ ; (i = i1) → _ })
    (inS (hcomp (∂ i) λ where
      j (i = i0) → F .F-∘ f g (~ j)
      j (i = i1) → f D.∘ g
      j (j = i0) → unglue f D.∘ unglue g))
```

The last trick is extending a proposition $P$ along the line
$\hom_i$, in a way that agrees with the original categories. We do
this by piecing together a square whose sides are the witness that $P$
is a proposition, and where the base is given by spreading
(`coe0→i`{.Agda}) the proposition from $\cC$ throughout the line. We
only include the case for `Hom-set`{.Agda} since it is instructive and
the other laws are not any more enlightening.

```agda
  hom-is-set : ∀ i a b → is-set (hom i a b)
  hom-is-set i a b = hcomp (∂ i) λ where
      k (k = i0) → extended
      k (i = i0) → is-hlevel-is-prop 2 extended (C.Hom-set a b) k
      k (i = i1) → is-hlevel-is-prop 2 extended (D.Hom-set a b) k
    where
      extended =
        coe0→i (λ i → (a b : obl i) → is-set (hom i a b)) i C.Hom-set a b

  open Precategory
  path : C ≡ D
  path i .Ob = obl i
  path i .Hom = hom i
  path i .Hom-set a b = hom-is-set i a b
  path i .id {x} = idh i x
  path i ._∘_ {x} {y} {z} f g = circ i x y z f g
```

<!--
```agda
  path i .idr {x} {y} f =
    hcomp (∂ i) λ where
      k (k = i0) → extended
      k (i = i0) → C.Hom-set x y (f C.∘ C.id) f extended (C.idr f) k
      k (i = i1) → D.Hom-set x y (f D.∘ D.id) f extended (D.idr f) k
    where
      extended = coe0→i
        (λ i → (x y : obl i) (f : hom i x y) → circ i x x y f (idh i x) ≡ f) i
        (λ x y f → C.idr f) x y f
  path i .idl {x} {y} f =
    hcomp (∂ i) λ where
      k (k = i0) → extended
      k (i = i0) → C.Hom-set x y (C.id C.∘ f) f extended (C.idl f) k
      k (i = i1) → D.Hom-set x y (D.id D.∘ f) f extended (D.idl f) k
    where
      extended = coe0→i
        (λ i → (x y : obl i) (f : hom i x y) → circ i x y y (idh i y) f ≡ f) i
        (λ x y f → C.idl f) x y f
  path i .assoc {w} {x} {y} {z} f g h =
    hcomp (∂ i) λ where
      k (k = i0) → extended
      k (i = i0) →
        C.Hom-set w z (f C.∘ g C.∘ h) ((f C.∘ g) C.∘ h) extended (C.assoc f g h) k
      k (i = i1) →
        D.Hom-set w z (f D.∘ g D.∘ h) ((f D.∘ g) D.∘ h) extended (D.assoc f g h) k
    where
      extended = coe0→i
        (λ i → (w x y z : obl i) (f : hom i y z) (g : hom i x y) (h : hom i w x)
             → circ i w y z f (circ i w x y g h) ≡ circ i w x z (circ i x y z f g) h)
        i
        (λ _ _ _ _ f g h → C.assoc f g h) w x y z f g h
```
-->

To conclude that isomorphisms of precategories are an identity system,
we must now prove that the operation `Precategory-path`{.Agda} above
trivialises the isomorphism we started with. This is mostly
straightforward, but the proof that the action on morphisms is preserved
requires a boring calculation:

```agda
Precategory-identity-system
  : ∀ {o ℓ}
  → is-identity-system {A = Precategory o ℓ}
    (λ C D → Σ (Functor C D) is-precat-iso)
    (λ a → Id , iso id-equiv id-equiv)
Precategory-identity-system .to-path (F , i) = Precategory-path F i
Precategory-identity-system .to-path-over {C} {D} (F , i) = Σ-prop-pathp! $
  Functor-pathp
    (λ p → path→ua-pathp _ (λ j → F .F₀ (p j)))
    (λ {x} {y} f i → attach (∂ i) (λ { (i = i0) → _ ; (i = i1) → _ }) (inS (F .F₁ (f i))))
```

Note that we did not need to concern ourselves with the actual witness
that the functor is an isomorphism, since being an isomorphism is a
proposition.

## For univalent categories

Now we want to characterise the space of paths between _univalent_
categories, as a refinement of the identity system constructed above.
There are two observations that will allow us to do this like magic:

1. Being univalent is a _property_ of a precategory: Univalence is
defined to mean that the relation $X \cong Y$ is an identity system for
the objects of $\cC$, and "being an identity system" is a _property_
of a relation^[Really, it's a property of a _pointed_ relation, but this
does not make a difference here.]

2. Between univalent categories, being an adjoint equivalence is a
property of a functor, and it is logically equivalent to being an
isomorphism of the underlying precategories.

Putting this together is a matter of piecing pre-existing lemmas
together. The first half of the construction is by observing that the
map (of types) which forgets univalence for a given category is an
embedding, so that we may compute an identity system on univalent
categories by pulling back that of precategories:

```agda
Category-identity-system-pre
  : ∀ {o ℓ} →
    is-identity-system {A = Σ (Precategory o ℓ) is-category}
      (λ C D → Σ (Functor (C .fst) (D .fst)) is-precat-iso)
      (λ a → Id , iso id-equiv id-equiv)
Category-identity-system-pre =
  pullback-identity-system
    Precategory-identity-system
    (fst , Subset-proj-embedding λ x → is-identity-system-is-prop)
```

Then, since the spaces of equivalences $\cC \cong \cD$ and
isomorphisms $\cC \to \cD$ are both defined as the total space of
a predicate on the same types, it suffices to show that the predicates
are equivalent pointwise, which follows by propositional extensionality
and a tiny result to adjust an equivalence into an isomorphism.

```agda
Category-identity-system
  : ∀ {o ℓ} → is-identity-system
    {A = Σ (Precategory o ℓ) is-category}
    (λ C D → Σ (Functor (C .fst) (D .fst)) is-equivalence)
    (λ a → Id , Id-is-equivalence)
Category-identity-system =
  transfer-identity-system Category-identity-system-pre
    (λ x y → Σ-ap-snd λ F → prop-ext (hlevel 1) (is-equivalence-is-prop (x .snd) F)
      is-precat-iso→is-equivalence
      (eqv→iso (x .snd) (y .snd) F))
```

To show that this equivalence sends "reflexivity" to "reflexivity", all
that matters is the functor (since being an equivalence is a
proposition), and the functor is definitionally preserved.

```agda
    (λ x → Σ-prop-path (is-equivalence-is-prop (x .snd)) refl)
```

<!--
```agda
  where
    module
      _ {C D : Precategory _ _} (ccat : is-category C) (dcat : is-category D)
      (F : Functor C D) (eqv : is-equivalence F)
      where
      open is-precat-iso
      open is-equivalence
```
-->

And now the aforementioned tiny result: All equivalences are [[fully
faithful]], and if both categories are univalent, the natural
isomorphisms $F\inv F \cong \Id$ and $FF\inv \cong \Id$ provide
the necessary paths for showing that $F_0$ is an equivalence of types.

```agda
      eqv→iso : is-precat-iso F
      eqv→iso .has-is-ff = is-equivalence→is-ff F eqv
      eqv→iso .has-is-iso = is-iso→is-equiv λ where
        .is-iso.from   → eqv .F⁻¹ .F₀
        .is-iso.rinv x → dcat .to-path       $ isoⁿ→iso (F∘F⁻¹≅Id eqv) _
        .is-iso.linv x → sym $ ccat .to-path $ isoⁿ→iso (Id≅F⁻¹∘F eqv) _
```

<!--
```agda
module
  _ {o ℓ} {C : Precategory o ℓ} {D : Precategory o ℓ}
    (ccat : is-category C) (dcat : is-category D)
    (F : Functor C D)
    (eqv : is-equivalence F)
  where

  eqv→path : C ≡ D
  eqv→path = ap fst (Category-identity-system .to-path {C , ccat} {D , dcat} (F , eqv))
```
-->
