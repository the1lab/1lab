---
description: |
  The category of marked graphs.
---
<!--
```agda
open import 1Lab.Reflection.Induction

open import Cat.Functor.Adjoint.Reflective
open import Cat.Instances.StrictCat
open import Cat.Functor.Properties
open import Cat.Instances.Graphs
open import Cat.Functor.Adjoint
open import Cat.Instances.Free
open import Cat.Functor.Base
open import Cat.Prelude
open import Cat.Strict

import Cat.Functor.Reasoning
import Cat.Reasoning
```
-->
```agda
module Cat.Instances.MarkedGraphs where
```

# Marked graphs

Recall that every [[graph]] $G$ gives rise to a [[free category]]
$\rm{Path}(G)$. Though useful, this construction is rather limiting;
if we want to construct ([[strict|strict category]]) categories via combinatorial methods,
then we really do need a way to add non-trivial equalities. In other words,
we need to be able to construct categories freely from a set of generators
*and* relations! This leads us to the following series of definitions:

:::{.definition #marked-graph alias="marked-graph"}
A **marked graph** consists of a [[graph]] $G$ along with a set of
pairs of distinguished paths in $G$, which we will call **marked pairs**.
:::


```agda
record Marked-graph (o ℓ : Level) : Type (lsuc o ⊔ lsuc ℓ) where
  no-eta-equality
  field
    graph : Graph o ℓ

  open Graph graph public

  field
    Marked : ∀ {x y} → Path-in graph x y → Path-in graph x y → Ω
```

<!--
```agda
private variable
  o ℓ o' ℓ' : Level
  G H K : Marked-graph o ℓ

open Marked-graph
open hlevel-projection

instance
  Underlying-Marked-graph : Underlying (Marked-graph o ℓ)
  Underlying-Marked-graph = record { ⌞_⌟ = Node }
```
-->

:::{.definition #marked-graph-homomorphism}
A **marked graph homomorphism** $f : G \to H$ is a [[graph homomorphism]]
that takes a marked pair $p, q : G^*$ in $G$ to a marked pair
$f(p), g(p) : H^*$ in $H$.
:::


```agda
record Marked-graph-hom (G : Marked-graph o ℓ) (H : Marked-graph o' ℓ') : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ') where
  no-eta-equality
  field
    hom : Graph-hom (G .graph) (H .graph)
    pres-marked
      : ∀ {x y} {p q : Path-in (G .graph) x y}
      → ∣ G .Marked p q ∣
      → ∣ H .Marked (path-map hom p) (path-map hom q) ∣
  open Graph-hom hom public
```

<!--
```agda
open Marked-graph-hom

unquoteDecl H-Level-Marked-graph-hom = declare-record-hlevel 2 H-Level-Marked-graph-hom (quote Marked-graph-hom)

instance
  Funlike-Marked-graph-hom : Funlike (Marked-graph-hom G H) ⌞ G ⌟ λ _ → ⌞ H ⌟
  Funlike-Marked-graph-hom .Funlike._·_ = Marked-graph-hom.node

Marked-graph-hom-pathp
  : {G : I → Marked-graph o ℓ} {H : I → Marked-graph o' ℓ'}
  → {f : Marked-graph-hom (G i0) (H i0)} {g : Marked-graph-hom (G i1) (H i1)}
  → (p0 : ∀ (x : ∀ i → G i .Node)
          → PathP (λ i → H i .Node)
              (f .node (x i0)) (g .node (x i1)))
  → (p1 : ∀ {x y : ∀ i → G i .Node}
          → (e : ∀ i → G i .Edge (x i) (y i))
          → PathP (λ i → H i .Edge (p0 x i) (p0 y i))
              (f .edge (e i0)) (g .edge (e i1)))
  → PathP (λ i → Marked-graph-hom (G i) (H i)) f g
Marked-graph-hom-pathp {G = G} {H = H} {f = f} {g = g} p0 p1 = comm-path where
  hom-path : PathP (λ i → Graph-hom (G i .graph) (H i .graph)) (f .hom) (g .hom)
  hom-path =
    Graph-hom-pathp {G = λ i → G i .graph} {H = λ i → H i .graph}
      {f = f .hom} {g .hom}
      p0 p1

  comm-path : PathP (λ i → Marked-graph-hom (G i) (H i)) f g
  comm-path i .hom = hom-path i
  comm-path i .pres-marked {x} {y} {p} {q} =
    is-prop→pathp (λ i →
        Π-is-hlevel {A = G i .Node} 1 λ x →
        Π-is-hlevel {A = G i .Node} 1 λ y →
        Π-is-hlevel {A = Path-in (G i .graph) x y} 1 λ p →
        Π-is-hlevel {A = Path-in (G i .graph) x y} 1 λ q →
        Π-is-hlevel {A = ∣ G i .Marked p q ∣} 1 λ _ →
        H i .Marked (path-map (hom-path i) p) (path-map (hom-path i) q) .is-tr)
      (λ _ _ _ _ → f .pres-marked)
      (λ _ _ _ _ → g .pres-marked)
      i x y p q

Marked-graph-hom-path
  : {f g : Marked-graph-hom G H}
  → (p0 : ∀ x → f .node x ≡ g .node x)
  → (p1 : ∀ {x y} → (e : G .Edge x y) → PathP (λ i → H .Edge (p0 x i) (p0 y i)) (f .edge e) (g .edge e))
  → f ≡ g
Marked-graph-hom-path {G = G} {H = H} p0 p1 =
  Marked-graph-hom-pathp {G = λ _ → G} {H = λ _ → H}
    (λ x i → p0 (x i) i)
    (λ e i → p1 (e i) i)
```
-->

We can organize marked graphs and their homomorphisms into a category $\MarkedGraphs$.

```agda
Marked-graphs : ∀ o ℓ → Precategory (lsuc o ⊔ lsuc ℓ) (o ⊔ ℓ)
Marked-graphs o ℓ .Precategory.Ob = Marked-graph o ℓ
Marked-graphs o ℓ .Precategory.Hom = Marked-graph-hom
```

<details>
<summary>Composition, identities, and their corresponding equations are
a bit tedious, so we omit the details.
</summary>

```agda
Marked-graphs o ℓ .Precategory.Hom-set _ _ = hlevel 2
Marked-graphs o ℓ .Precategory.id {G} .hom = Graphs.id
Marked-graphs o ℓ .Precategory.id {G} .pres-marked p~q =
  subst₂ (λ p q → ∣ G .Marked p q ∣)
    (sym (path-map-id _))
    (sym (path-map-id _))
    p~q
Marked-graphs o ℓ .Precategory._∘_ f g .hom = (f .hom) Graphs.∘ (g .hom)
Marked-graphs o ℓ .Precategory._∘_ {G} {H} {K} f g .pres-marked p~q =
  subst₂ (λ p q → ∣ K .Marked p q ∣)
    (sym (path-map-∘ _))
    (sym (path-map-∘ _))
    (f .pres-marked (g .pres-marked p~q))
Marked-graphs o ℓ .Precategory.idr _ =
  Marked-graph-hom-path (λ _ → refl) (λ _ → refl)
Marked-graphs o ℓ .Precategory.idl _ =
  Marked-graph-hom-path (λ _ → refl) (λ _ → refl)
Marked-graphs o ℓ .Precategory.assoc _ _ _ =
  Marked-graph-hom-path (λ _ → refl) (λ _ → refl)
```
</details>

<!--
```agda
open Functor
```
-->

Moreover, there is a faithful functor from the [[category of strict categories]]
to the category of marked graphs.

```agda
Strict-cats↪Marked-graphs : Functor (Strict-cats o ℓ) (Marked-graphs o ℓ)
```

The action on objects takes a strict category $\cC$ to its underlying
graph, and adds a marked pair between $p, q : \cC^*$ whenever
$p$ and $q$ are equal as morphisms in $\cC$.

```agda
Strict-cats↪Marked-graphs .F₀ C .graph =
  Strict-cats↪Graphs .F₀ C
Strict-cats↪Marked-graphs .F₀ C .Marked p q =
  elΩ (path-reduce C p ≡ path-reduce C q)
```

Functoriality follows from the fact that functors take equal paths in $\cC$
to equal paths in $\cD$.

```agda
Strict-cats↪Marked-graphs .F₁ F .hom =
  Strict-cats↪Graphs .F₁ F
Strict-cats↪Marked-graphs .F₁ F .pres-marked {p = p} {q = q} =
  □-map λ p~q → path-reduce-natural F p ∙ ap (F .F₁) p~q ∙ sym (path-reduce-natural F q)
Strict-cats↪Marked-graphs .F-id =
  Marked-graph-hom-path (λ _ → refl) (λ _ → refl)
Strict-cats↪Marked-graphs .F-∘ F G =
  Marked-graph-hom-path (λ _ → refl) (λ _ → refl)
```

This functor is clearly [[faithful]]; the proof is essentially just
relabeling data.

```agda
Strict-cats↪Marked-graphs-faithful
  : is-faithful (Strict-cats↪Marked-graphs {o} {ℓ})
Strict-cats↪Marked-graphs-faithful p =
  Functor-path (λ x i → p i .node x) (λ f i → p i .edge f)
```

More surprisingly this functor is also [[full]]!


```agda
Strict-cats↪Marked-graphs-full
  : is-full (Strict-cats↪Marked-graphs {o} {ℓ})
```

To see why, suppose that $f : \cC \to \cD$ is a marked
graph homomorphism between strict categories. By definition, $f$
already contains the data of a functor; the tricky part is showing
that this data is functorial.

```agda
Strict-cats↪Marked-graphs-full {x = C} {y = D} f =
  pure (functor , Marked-graph-hom-path (λ _ → refl) (λ _ → refl))
  where
    module C = Precategory (C .fst)
    module D = Precategory (D .fst)

    functor : Functor (C .fst) (D .fst)
    functor .F₀ = f .node
    functor .F₁ = f .edge
```

The trick is that marked graph homomorphisms between categories cannot observe
the intensional structure of paths, as they must preserve all marked pairs.
In particular, $f$ will preserve the makred pair consisting of $[id]$ and
the empty path; so $f(\id) = \id$

```agda
    functor .F-id =
      f .edge C.id          ≡˘⟨ D.idl _ ⟩
      D.id D.∘ f .edge C.id ≡⟨ □-out! (f .pres-marked {p = cons C.id nil} {q = nil} (inc (C.idl _))) ⟩
      D.id                  ∎
```

Additionally, $f$ will preserve the marked pair consisting of the singleton
path $[g \circ h]$ and the path $[h, g]$, so $f(g \circ h) = f g \circ f h$.

```agda
    functor .F-∘ g h =
      f .edge (g C.∘ h)                  ≡˘⟨ D.idl _ ⟩
      D.id D.∘ f .edge (g C.∘ h)         ≡˘⟨ □-out! (f .pres-marked {p = cons h (cons g nil)} {q = cons (g C.∘ h) nil} (pure (sym (C.assoc _ _ _)))) ⟩
      (D.id D.∘ f .edge g) D.∘ f .edge h ≡⟨ ap₂ D._∘_ (D.idl _) refl ⟩
      f .edge g D.∘ f .edge h ∎
```


## Categories from generators and relations

<!--
```agda
module _ (G : Marked-graph o ℓ) where
  private module G = Marked-graph G
```
-->

In this section, we will detail how to freely construct a category
from a marked graph $G$. Intuitively, this works by freely generating
a category from $G$, and then identifying all marked pairs.
However, there is a slight subtlety here: the marked pairs of $G$
may not respect path concatenation, and may not even form an equivalence
relation!

Luckily, there is an easy (though tedious) solution to this problem:
we can instead quotient by the reflexive-transitive-congruent closure
instead, which we encode in Agda via the following higher-inductive type.

```agda
  data Marking
    : ∀ {x y} → Path-in G.graph x y → Path-in G.graph x y
    → Type (o ⊔ ℓ)
    where
    marked
      : ∀ {x y} {p q : Path-in G.graph x y}
      → ∣ G.Marked p q ∣
      → Marking p q
    reflexive
      : ∀ {x y} {p : Path-in G.graph x y}
      → Marking p p
    symmetric
      : ∀ {x y} {p q : Path-in G.graph x y}
      → Marking q p
      → Marking p q
    transitive
      : ∀ {x y} {p q r : Path-in G.graph x y}
      → Marking p q → Marking q r
      → Marking p r
    congruent
      : ∀ {x y z} {p q : Path-in G.graph x y} {r s : Path-in G.graph y z}
      → Marking p q → Marking r s
      → Marking (p ++ r) (q ++ s)
    trunc : ∀ {x y} {p q : Path-in G.graph x y} → is-prop (Marking p q)
  ```

<!--
```agda
  unquoteDecl Marking-elim-prop = make-elim-n 1 Marking-elim-prop (quote Marking)
```
-->

The resulting category is not too difficult to construct:
the objects are the nodes of $G$, and the morphisms are paths in
$G$ quotiented by the aforementioned closure.

```agda
  Marked-path-category : Precategory o (o ⊔ ℓ)
  Marked-path-category .Precategory.Ob = G.Node
  Marked-path-category .Precategory.Hom x y =
    Path-in G.graph x y / Marking
  Marked-path-category .Precategory.Hom-set _ _ = hlevel 2
  Marked-path-category .Precategory.id = inc nil
  Marked-path-category .Precategory._∘_ =
    Quot-op₂
      (λ _ → reflexive) (λ _ → reflexive)
      (flip _++_)
      (λ p q r s p~q r~s → congruent r~s p~q)
  Marked-path-category .Precategory.idr =
    elim! λ p → refl
  Marked-path-category .Precategory.idl =
    elim! λ p → ap inc (++-idr p)
  Marked-path-category .Precategory.assoc =
    elim! λ p q r → ap inc (++-assoc r q p)
```

Proving that this construction is free involves a bit more work.

We start with a useful lemma. Let $\cC$ be an arbitrary strict category,
$G$ a marked graph, and $f : G \to \cC$ a marked graph homomorphism.
If $p, q$ are related by the marked closure of $G$, then folding $f$
over $p$ and $q$ results in the same morphism.

```agda
module _ (C : Σ (Precategory o ℓ) is-strict) where
  private
    module C = Cat.Reasoning (C .fst)
    ∣C∣ : Marked-graph o ℓ
    ∣C∣ = Strict-cats↪Marked-graphs .F₀ C

  path-fold-marking
    : (f : Marked-graph-hom G ∣C∣)
    → ∀ {x y} (p q : Path-in (G .graph) x y)
    → Marking G p q
    → path-fold C (f .hom) p ≡ path-fold C (f .hom) q
```

The proof is an easy but tedious application of the elimination principle
of `Marking`{.Agda}.

```agda
  path-fold-marking {G = G} f p q =
    Marking-elim-prop G
      {P = λ {x} {y} {p} {q} _ →
        path-fold C (f .hom) p ≡ path-fold C (f .hom) q}
      (λ _ → hlevel 1)
      (λ {_} {_} {p} {q} p~q →
        sym (path-reduce-map p)
        ∙ □-out! (f .pres-marked p~q)
        ∙ path-reduce-map q)
      refl (λ _ → sym) (λ _ p=q _ q=r → p=q ∙ q=r)
      (λ {_} {_} {_} {p} {q} {r} {s} _ p=q _ r=s →
        path-fold-++ C p r
        ∙ ap₂ C._∘_ r=s p=q
        ∙ sym (path-fold-++ C q s))
```

This lemma lets us extend folds over paths to folds over quotiented
paths.

```agda
  comm-path-fold
    : (f : Marked-graph-hom G ∣C∣)
    → ∀ {x y} → Path-in (G .graph) x y / Marking G
    → C.Hom (f .node x) (f .node y)
  comm-path-fold f =
    Quot-elim (λ _ → hlevel 2)
      (path-fold C (f .hom))
      (path-fold-marking f)
```

Moreover, this extends to a functor from the free category over $G$
to $\cC$.

```agda
  MarkedF
    : Marked-graph-hom G ∣C∣
    → Functor (Marked-path-category G) (C .fst)
  MarkedF f .F₀ = f .node
  MarkedF f .F₁ = comm-path-fold f
  MarkedF f .F-id = refl
  MarkedF f .F-∘ = elim! λ p q → path-fold-++ C q p
```

Like path categories, functors out of marked path categories
are purely characterized by their behaviour on edges.

<!--
```agda
module _ {C : Precategory o ℓ} where
  private module C = Cat.Reasoning C
```
-->

```agda
  Marked-path-category-functor-path
    : {F F' : Functor (Marked-path-category G) C}
    → (p0 : ∀ x → F .F₀ x ≡ F' .F₀ x)
    → (p1 : ∀ {x y} (e : G .Edge x y)
            → PathP (λ i → C.Hom (p0 x i) (p0 y i))
                (F .F₁ (inc (cons e nil)))
                (F' .F₁ (inc (cons e nil))))
    → F ≡ F'
```
<details>
<summary>Like the analogous result for path categories, this proof involves
some cubical yoga which we will hide from the innocent reader.
</summary>

```agda
  Marked-path-category-functor-path {G = G} {F = F} {F' = F'} p0 p1 =
    Functor-path p0 (elim! p1-paths)
    where
      p1-paths
        : ∀ {x y}
        → (p : Path-in (G .graph) x y)
        → PathP (λ i → C.Hom (p0 x i) (p0 y i)) (F .F₁ (inc p)) (F' .F₁ (inc p))
      p1-paths {x = x} nil i =
        hcomp (∂ i) λ where
          j (i = i0) → F .F-id (~ j)
          j (i = i1) → F' .F-id (~ j)
          j (j = i0) → C.id
      p1-paths (cons e p) i =
        hcomp (∂ i) λ where
          j (i = i0) → F .F-∘ (inc p) (inc (cons e nil)) (~ j)
          j (i = i1) → F' .F-∘ (inc p) (inc (cons e nil)) (~ j)
          j (j = i0) → p1-paths p i C.∘ p1 e i
```
</details>

With these results in hand, we can return to our original goal of showing
that the marked path category on $G$ is a [[free object]] relative
to the underlying marked graph functor.

```agda
Marked-free-category
  : ∀ (G : Marked-graph ℓ ℓ)
  → Free-object Strict-cats↪Marked-graphs G
Marked-free-category G .Free-object.free = Marked-path-category G , hlevel 2
```

The unit of the free object takes nodes to themselves, and edges
to singleton paths. We need to do a bit of work to show that this construction
preserves markings but it's not too difficult.

```agda
Marked-free-category G .Free-object.unit = unit-comm where
  G* : Σ (Precategory _ _) is-strict
  G* = Marked-path-category G , hlevel 2

  ∣G*∣ : Graph _ _
  ∣G*∣ = Strict-cats↪Graphs .F₀ G*

  unit : Graph-hom (G .graph) ∣G*∣
  unit .Graph-hom.node x = x
  unit .Graph-hom.edge e = inc (cons e nil)

  unit-comm : Marked-graph-hom G (Strict-cats↪Marked-graphs .F₀ G*)
  unit-comm .hom = unit
  unit-comm .pres-marked {p = p} {q = q} p~q =
    pure $
      path-reduce G* (path-map unit p) ≡⟨ path-reduce-map p ⟩
      path-fold G* unit p              ≡˘⟨ path-fold-unique G* inc refl (λ _ _ → refl) p ⟩
      inc p                            ≡⟨ quot (marked p~q) ⟩
      inc q                            ≡⟨ path-fold-unique G* inc refl (λ _ _ → refl) q ⟩
      path-fold G* unit q              ≡˘⟨ path-reduce-map q ⟩
      path-reduce G* (path-map unit q) ∎
```

We've already put in the work for the universal
property: all that we need to do is assemble previous results!

```agda
Marked-free-category G .Free-object.fold {Y = C} f = MarkedF C f
Marked-free-category G .Free-object.commute {Y = C} =
  Marked-graph-hom-path (λ _ → refl) (λ _ → idl _)
  where open Precategory (C .fst)
Marked-free-category G .Free-object.unique {Y = C} F p =
  Marked-path-category-functor-path
    (λ x i → p i .node x)
    (λ e → to-pathp (from-pathp (λ i → p i .edge e) ∙ sym (idl _)))
  where open Precategory (C .fst)
```

<!--
```agda
Marked-free-categories : Functor (Marked-graphs ℓ ℓ) (Strict-cats ℓ ℓ)
Marked-free-categories =
  free-objects→functor Marked-free-category

Marked-free-categories⊣Underlying-marked-graph
  : Marked-free-categories {ℓ} ⊣ Strict-cats↪Marked-graphs
Marked-free-categories⊣Underlying-marked-graph =
  free-objects→left-adjoint Marked-free-category
```
-->

This means that the category of strict categories is a [[reflective subcategory]]
of the category of marked graphs. In more intuitive terms,
that we can think about strict categories as algebraic structure placed
atop a marked graph, as inclusions from reflective subcategories
are [[monadic]]!

```agda
Marked-free-categories⊣Underlying-marked-graph-reflective
  : is-reflective (Marked-free-categories⊣Underlying-marked-graph {ℓ})
Marked-free-categories⊣Underlying-marked-graph-reflective =
  full+faithful→ff Strict-cats↪Marked-graphs
    Strict-cats↪Marked-graphs-full
    Strict-cats↪Marked-graphs-faithful
```
