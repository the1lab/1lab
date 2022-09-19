```agda
open import Cat.Functor.Adjoint.Unique
open import Cat.Functor.Equivalence
open import Cat.Instances.Functor
open import Cat.Functor.Base
open import Cat.Univalent
open import Cat.Prelude

import Cat.Functor.Reasoning as Fr
import Cat.Reasoning

open Functor

module Cat.Functor.Equivalence.Path where
```

# Paths between categories

We know that, _in_ a univalent category, paths between objects are the
same thing as isomorphisms. A natural question to follow up is: what are
the paths _between_ univalent categories? We prove that the space of
functors $F : \ca{C} \to \ca{D}$ whose mappings on objects and on
morphisms are both equivalences ("isomorphisms of precategories") is an
\r{identity system} on the space of precategories.

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
univalence it induces an equivalence $\ca{C}_0 \equiv \ca{D}_0$. The
path between `Hom`{.Agda}-sets is slightly more complicated. It is,
essentially, the dashed line in the diagram

~~~{.quiver}
\[\begin{tikzcd}
  {\mathbf{Hom}_\mathcal{C}(x,y)} && {\mathbf{Hom}_\mathcal{D}(F_0x,F_0y)} \\
  \\
  {\mathbf{Hom}_\mathcal{D}(F_0x,F_0y)} && {\mathbf{Hom}_\mathcal{D}(F_0x,F_0y)}
  \arrow["{\mathrm{id}}", from=1-3, to=3-3]
  \arrow["{F_1}"', from=1-1, to=3-1]
  \arrow["{\mathrm{Hom}_\mathcal{D}(x, y)}"', from=3-1, to=3-3]
  \arrow[dashed, from=1-1, to=1-3]
\end{tikzcd}\]
~~~

```agda
  obl : ∀ i → Type o
  obl i = ua (F₀ F , ob≃) i

  sys : ∀ i (x y : obl i) → Partial (i ∨ ~ i) _
  sys i x y (i = i0) = C.Hom x y , F₁ F , hom≃
  sys i x y (i = i1) = D.Hom x y , (λ x → x) , id-equiv

  hom : PathP (λ i → obl i → obl i → Type ℓ) C.Hom D.Hom
  hom i x y = Glue (D.Hom (unglue (i ∨ ~ i) x) (unglue (i ∨ ~ i) y)) (sys i x y)
```

Note that $\id{unglue}_{i \lor \neg i}(x)$ is a term in $\ca{D}_0$ which
evaluates to $F_0(x)$ when $i = i1$ or $i = i0$, so that the system
described above can indeed be built. The introduction rule for
`hom`{.Agda} is `hom-glue`{.Agda}: If we have a partial element $\neg i
\vdash f : \Hom_\mathca{C} x y$ together with an element $g$ of base
type satisfying definitionally $\neg i \vdash F_1(f) = g$, we may glue
$f$ along $g$ to get an element of $\id{hom}_i(x, y)$.

```agda
  hom-glue
    : ∀ i (x y : obl i)
    → (f : PartialP {a = ℓ} (~ i) λ { (i = i0) → C.Hom x y })
    → (g : D.Hom (unglue (i ∨ ~ i) x) (unglue (i ∨ ~ i) y)
        [ (~ i) ↦ (λ { (i = i0) → F₁ F (f 1=1) }) ])
    → hom i x y
  hom-glue i x y f g = glue-inc _ {Tf = sys i x y}
    (λ { (i = i0) → f 1=1 ; (i = i1) → outS g })
    (inS (outS g))
```

To obtain these definitional extensions of a morphism in C, we use
homogeneous composition, together with the functor laws. For example,
below, we obtain a line which definitionally extends $\id{id}_\ca{C}$ on
the left and $\id{id}_\ca{D}$ by gluing $\id{id}_\ca{C}$ _against the
proof that $F$ preserves identity_.

```agda
  idh : ∀ i x → hom i x x
  idh i x = hom-glue i x x (λ { (i = i0) → C.id }) (inS (hcomp (∂ i) λ where
    j (i = i0) → F .F-id (~ j)
    j (i = i1) → D.id
    j (j = i0) → D.id))

  circ : ∀ i x y z → hom i y z → hom i x y → hom i x z
  circ i x y z f g =
    hom-glue i x z (λ { (i = i0) → f C.∘ g }) (inS (hcomp (∂ i) λ where
      j (i = i0) → F .F-∘ f g (~ j)
      j (i = i1) → f D.∘ g
      j (j = i0) → unglue (i ∨ ~ i) f D.∘ unglue (i ∨ ~ i) g))
```

The last trick is extending a proposition $P$ along the line
$\id{hom}_i$, in a way that agrees with the original categories. We do
this by piecing together a square whose sides are the witness that $P$
is a proposition, and where the base is given by spreading
(`coe0→i`{.Agda}) the proposition from $\ca{C}$ throughout the line. We
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

private unquoteDecl eqv = declare-record-iso eqv (quote is-precat-iso)
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
Precategory-identity-system .to-path-over {C} {D} (F , i) =
  Σ-prop-pathp (λ _ _ → is-hlevel≃ 1 (Iso→Equiv eqv e⁻¹) (hlevel 1)) $
    Functor-pathp (λ p → path→ua-pathp _ (λ j → F.₀ (p j)))
                  (λ {x} {y} → homs x y)
  where
    module C = Cat.Reasoning C
    module D = Cat.Reasoning D
    module F = Functor F

    homs : ∀ x y (r : ∀ j → C.Hom (x j) (y j)) → PathP _ _ _
    homs x y f = to-pathp $
      transport (λ i₁ → D.Hom (F.₀ (x i₁)) (F.₀ (y i₁))) (F.₁ (f i0)) ≡⟨ Hom-transport {C = D} (λ i → F.₀ (x i)) (λ i → F.₀ (y i)) (F.₁ (f i0)) ⟩
      _ D.∘ F.₁ (f i0) D.∘ _                                          ≡⟨ ap D.to (ap-F₀-to-iso F (λ i → y i)) D.⟩∘⟨ (refl D.⟩∘⟨ ap D.from (ap-F₀-to-iso F (λ i → x i))) ⟩
      F.₁ _ D.∘ F.₁ (f i0) D.∘ F.₁ _                                  ≡˘⟨ D.refl⟩∘⟨ F.F-∘ _ _ ⟩
      (F.₁ _ D.∘ F.₁ (f i0 C.∘ _))                                    ≡˘⟨ F.F-∘ _ _ ⟩
      F.₁ (_ C.∘ f i0 C.∘ _)                                          ≡˘⟨ ap F.₁ (Hom-transport {C = C} (λ i → x i) (λ i → y i) (f i0)) ⟩
      F.₁ (coe0→1 (λ z → C.Hom (x z) (y z)) (f i0))                   ≡⟨ ap F.₁ (from-pathp (λ i → f i)) ⟩
      F.₁ (f i1)                                                      ∎
```

Note that we did not need to concern ourselves with the actual witness
that the functor is an isomorphism, since being an isomorphism is a
proposition.
