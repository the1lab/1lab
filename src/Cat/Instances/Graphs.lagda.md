---
description: |
  The category of graphs.
---
<!--
```agda
open import 1Lab.Path.Cartesian
open import 1Lab.Reflection

open import Cat.Functor.Equivalence.Path
open import Cat.Instances.Shape.Parallel
open import Cat.Functor.Equivalence
open import Cat.Instances.StrictCat
open import Cat.Functor.Properties
open import Cat.Functor.Base
open import Cat.Univalent
open import Cat.Prelude
open import Cat.Strict

import Cat.Reasoning
```
-->
```agda
module Cat.Instances.Graphs where
```

<!--
```agda
private variable
  o o' ℓ ℓ' : Level
```
-->

# The category of graphs

:::{.definition #graph}
A **graph** (really, an $(o, \ell)$-graph^[and, even more pedantically,
a directed multi-$(o, ℓ)$-graph]) is given by a set $V : \Sets_o$ of
**vertices** and, for each pair of elements $x, y : V$, a set of
**edges** $E(x, y) : \Sets_\ell$ from $x$ to $y$. That's it: a set $V$
and a family of sets over $V \times V$.
:::


```agda
record Graph (o ℓ : Level) : Type (lsuc o ⊔ lsuc ℓ) where
  no-eta-equality
  field
    Vertex : Type o
    Edge : Vertex → Vertex → Type ℓ
    Vertex-is-set : is-set Vertex
    Edge-is-set : ∀ {x y} → is-set (Edge x y)
```

<!--
```agda
open Graph
open hlevel-projection

instance
  Underlying-Graph : Underlying (Graph o ℓ)
  Underlying-Graph = record { ⌞_⌟ = Graph.Vertex }

  hlevel-proj-vertex : hlevel-projection (quote Graph.Vertex)
  hlevel-proj-vertex .has-level = quote Graph.Vertex-is-set
  hlevel-proj-vertex .get-level _ = pure (quoteTerm (suc (suc zero)))
  hlevel-proj-vertex .get-argument (_ ∷ _ ∷ c v∷ _) = pure c
  {-# CATCHALL #-}
  hlevel-proj-vertex .get-argument _ = typeError []

  hlevel-proj-edge : hlevel-projection (quote Graph.Edge)
  hlevel-proj-edge .has-level = quote Graph.Edge-is-set
  hlevel-proj-edge .get-level _ = pure (quoteTerm (suc (suc zero)))
  hlevel-proj-edge .get-argument (_ ∷ _ ∷ c v∷ _) = pure c
  {-# CATCHALL #-}
  hlevel-proj-edge .get-argument _ = typeError []
```
-->

:::{.definition #graph-homomorphism}
A **graph homomorphism** $G \to H$ consists of a mapping of vertices
$f_v : G \to H$, along with a mapping of edges $f_e : G(x, y) \to H(f_v(x), f_v(y))$.
:::


```agda
record Graph-hom (G : Graph o ℓ) (H : Graph o' ℓ') : Type (o ⊔ o' ⊔ ℓ ⊔ ℓ') where
  no-eta-equality
  field
    vertex : ⌞ G ⌟ → ⌞ H ⌟
    edge : ∀ {x y} → G .Edge x y → H .Edge (vertex x) (vertex y)
```

<!--
```agda
private variable
  G H K : Graph o ℓ

open Graph-hom

unquoteDecl H-Level-Graph-hom = declare-record-hlevel 2 H-Level-Graph-hom (quote Graph-hom)

Graph-hom-pathp
  : {G : I → Graph o ℓ} {H : I → Graph o' ℓ'}
  → {f : Graph-hom (G i0) (H i0)} {g : Graph-hom (G i1) (H i1)}
  → (p0 : ∀ (x : ∀ i → G i .Vertex)
          → PathP (λ i → H i .Vertex)
              (f .vertex (x i0)) (g .vertex (x i1)))
  → (p1 : ∀ {x y : ∀ i → G i .Vertex}
          → (e : ∀ i → G i .Edge (x i) (y i))
          → PathP (λ i → H i .Edge (p0 x i) (p0 y i))
              (f .edge (e i0)) (g .edge (e i1)))
  → PathP (λ i → Graph-hom (G i) (H i)) f g
Graph-hom-pathp {G = G} {H = H} {f = f} {g = g} p0 p1 = pathp where
  vertex* : I → Type _
  vertex* i = (G i) .Vertex

  edge* : (i : I) → vertex* i → vertex* i → Type _
  edge* i x y = (G i) .Edge x y

  pathp : PathP (λ i → Graph-hom (G i) (H i)) f g
  pathp i .vertex x = p0 (λ j → coe vertex* i j x) i
  pathp i .edge {x} {y} e =
    p1 {x = λ j → coe vertex* i j x} {y = λ j → coe vertex* i j y}
      (λ j → coe (λ j → edge* j (coe vertex* i j x) (coe vertex* i j y)) i j (e* j)) i
    where

      x* y* : (j : I) → vertex* i
      x* j = coei→i vertex* i x (~ j ∨ i)
      y* j = coei→i vertex* i y (~ j ∨ i)

      e* : (j : I) → edge* i (coe vertex* i i x) (coe vertex* i i y)
      e* j =
        comp (λ j → edge* i (x* j) (y* j)) ((~ i ∧ ~ j) ∨ (i ∧ j)) λ where
          k (k = i0) → e
          k (i = i0) (j = i0) → e
          k (i = i1) (j = i1) → e

Graph-hom-path
  : {f g : Graph-hom G H}
  → (p0 : ∀ x → f .vertex x ≡ g .vertex x)
  → (p1 : ∀ {x y} → (e : Graph.Edge G x y) → PathP (λ i → Graph.Edge H (p0 x i) (p0 y i)) (f .edge e) (g .edge e))
  → f ≡ g
Graph-hom-path {G = G} {H = H} p0 p1 =
  Graph-hom-pathp {G = λ _ → G} {H = λ _ → H}
    (λ x i → p0 (x i) i)
    (λ e i → p1 (e i) i)

instance
  Funlike-Graph-hom : Funlike (Graph-hom G H) ⌞ G ⌟ λ _ → ⌞ H ⌟
  Funlike-Graph-hom .Funlike._#_ = vertex

Graph-hom-id : {G : Graph o ℓ} → Graph-hom G G
Graph-hom-id .vertex v = v
Graph-hom-id .edge e = e

```
-->

Graphs and graph homomorphisms can be organized into a category $\Graphs$.

```agda
Graphs : ∀ o ℓ → Precategory (lsuc (o ⊔ ℓ)) (o ⊔ ℓ)
Graphs o ℓ .Precategory.Ob = Graph o ℓ
Graphs o ℓ .Precategory.Hom = Graph-hom
Graphs o ℓ .Precategory.Hom-set _ _ = hlevel 2
Graphs o ℓ .Precategory.id = Graph-hom-id
Graphs o ℓ .Precategory._∘_ f g .vertex v = f .vertex (g .vertex v)
Graphs o ℓ .Precategory._∘_ f g .edge e = f .edge (g .edge e)
Graphs o ℓ .Precategory.idr _ = Graph-hom-path (λ _ → refl) (λ _ → refl)
Graphs o ℓ .Precategory.idl _ = Graph-hom-path (λ _ → refl) (λ _ → refl)
Graphs o ℓ .Precategory.assoc _ _ _ = Graph-hom-path (λ _ → refl) (λ _ → refl)
```
<!--
```agda
open Functor
open _=>_
module _ {o ℓ : Level} where
  module Graphs = Cat.Reasoning (Graphs o ℓ)

  graph-iso-is-ff : {x y : Graph o ℓ} (h : Graphs.Hom x y) → Graphs.is-invertible h → ∀ {x y} → is-equiv (h .edge {x} {y})
  graph-iso-is-ff {x} {y} h inv {s} {t} = is-iso→is-equiv (iso from ir il) where
    module h = Graphs.is-invertible inv

    from : ∀ {s t} → y .Edge (h # s) (h # t) → x .Edge s t
    from e = subst₂ (x .Edge) (ap vertex h.invr # _) (ap vertex h.invr # _) (h.inv .edge e)

    ir : is-right-inverse from (h .edge)
    ir e =
      let
        lemma = J₂
          (λ s'' t'' p q → ∀ e
            → h .edge (subst₂ (x .Edge) p q e)
            ≡ subst₂ (y .Edge) (ap# h p) (ap# h q) (h .edge e))
          (λ e → ap (h .edge) (transport-refl _) ∙ sym (transport-refl _))
      in lemma _ _ (h.inv .edge e)
      ·· ap₂ (λ p q → subst₂ (y .Edge) {b' = h .vertex t} p q (h .edge (h.inv .edge e))) prop! prop!
      ·· from-pathp (λ i → h.invl i .edge e)

    il : is-left-inverse from (h .edge)
    il e = from-pathp λ i → h.invr i .edge e

  Graph-path
    : ∀ {x y : Graph o ℓ}
    → (p : x .Vertex ≡ y .Vertex)
    → (PathP (λ i → p i → p i → Type ℓ) (x .Edge) (y .Edge))
    → x ≡ y
  Graph-path {x = x} {y} p q i .Vertex = p i
  Graph-path {x = x} {y} p q i .Edge = q i
  Graph-path {x = x} {y} p q i .Vertex-is-set = is-prop→pathp
    (λ i → is-hlevel-is-prop {A = p i} 2) (x .Vertex-is-set) (y .Vertex-is-set) i
  Graph-path {x = x} {y} p q i .Edge-is-set {s} {t} =
    is-prop→pathp
      (λ i → Π-is-hlevel 1 λ x → Π-is-hlevel 1 λ y → is-hlevel-is-prop {A = q i x y} 2)
      (λ a b → x .Edge-is-set {a} {b}) (λ a b → y .Edge-is-set {a} {b}) i s t

  graph-path : ∀ {x y : Graph o ℓ} (h : x Graphs.≅ y) → x ≡ y
  graph-path {x = x} {y = y} h = Graph-path (ua v) (λ i → E i ) module graph-path where
    module h = Graphs._≅_ h
    v : ⌞ x ⌟ ≃ ⌞ y ⌟
    v = record
      { fst = h.to .vertex
      ; snd = is-iso→is-equiv (iso (h.from .vertex) (happly (ap vertex h.invl)) (happly (ap vertex h.invr)))
      }

    E : (i : I) → ua v i → ua v i → Type ℓ
    E i s t = Glue (y .Edge (unglue s) (unglue t)) (λ where
      (i = i0) → x .Edge s t , _ , graph-iso-is-ff h.to (Graphs.iso→invertible h)
      (i = i1) → y .Edge s t , _ , id-equiv)
```
-->

In particular, $\Graphs$ is a [[univalent category]].

```agda
  Graphs-is-category : is-category (Graphs o ℓ)
  Graphs-is-category .to-path = graph-path
  Graphs-is-category .to-path-over {a} {b} p = Graphs.≅-pathp _ _ $ Graph-hom-pathp pv pe where
    open graph-path p

    pv : (h : I → a .Vertex) → PathP (λ i → ua v i) (h i0) (h.to .vertex (h i1))
    pv h i = ua-glue v i (λ { (i = i0) → h i }) (inS (h.to .vertex (h i)))

    pe : {x y : I → a .Vertex} (e : ∀ i → a .Edge (x i) (y i))
       → PathP (λ i → graph-path p i .Edge (pv x i) (pv y i)) (e i0) (h.to .edge (e i1))
    pe {x} {y} e i = attach (∂ i) (λ { (i = i0) → _ ; (i = i1) → _ }) (inS (h.to .edge (e i)))
```

## Graphs as presheaves

A graph $(V, E)$ may equivalently be seen as a diagram

~~~{.quiver}
\begin{tikzcd}
	V & E & V
	\arrow["{\mathrm{src}}"', from=1-2, to=1-1]
	\arrow["{\mathrm{dst}}", from=1-2, to=1-3]
\end{tikzcd}
~~~

of sets.

That is, a graph $G$^[whose edges and vertices live in the same
universe] is the same as functor from the [[walking parallel arrows]]
category to $\Sets$. Furthermore, presheaves and functors to $\Sets$ are
equivalent as this category is self-dual.

<!--
```agda
  graph→presheaf : Functor (Graphs o ℓ) (PSh (o ⊔ ℓ) ·⇇·)
  graph→presheaf .F₀ G =
    Fork {a = el! $ Σ[ s ∈ G .Vertex ] Σ[ t ∈ G .Vertex ] G .Edge s t }
         {el! $ Lift ℓ ⌞ G ⌟}
         (lift ⊙ fst)
         (lift ⊙ fst ⊙ snd)
  graph→presheaf .F₁ f =
    Fork-nt {u = λ (s , t , e) → f .vertex s , f .vertex t , f .edge e }
            {v = λ { (lift v) → lift (f # v) } } refl refl
  graph→presheaf .F-id = Nat-path λ { true → refl ; false → refl }
  graph→presheaf .F-∘ G H = Nat-path λ { true → refl ; false → refl }

  g→p-is-ff : is-fully-faithful graph→presheaf
  g→p-is-ff {x = x} {y = y} = is-iso→is-equiv (iso from ir il) where
    from : graph→presheaf # x => graph→presheaf # y → Graph-hom x y
    from h .vertex v = h .η true (lift v) .lower
    from h .edge e =
      let
        (s' , t' , e') = h .η false (_ , _ , e)
        ps = ap lower (sym (h .is-natural false true false $ₚ (_ , _ , e)))
        pt = ap lower (sym (h .is-natural false true true $ₚ (_ , _ , e)))
      in subst₂ (y .Edge) ps pt e'

    ir : is-right-inverse from (graph→presheaf .F₁)
    ir h = ext λ where
      true x          → refl
      false (s , t , e) →
        let
          ps = ap lower (h .is-natural false true false $ₚ (s , t , e))
          pt = ap lower (h .is-natural false true true $ₚ (s , t , e))
          s' , t' , e' = h .η false (_ , _ , e)
        in Σ-pathp ps (Σ-pathp pt λ i → coe1→i (λ j → y .Edge (ps j) (pt j)) i e')

    il : is-left-inverse from (graph→presheaf .F₁)
    il h = Graph-hom-path (λ _ → refl) (λ e → transport-refl _)

private module _ {ℓ : Level} where

  presheaf→graph : ⌞ PSh ℓ ·⇇· ⌟ → Graph ℓ ℓ
  presheaf→graph F = g
    where module F = Functor F
          g : Graph ℓ ℓ
          g .Vertex = ⌞ F # true ⌟
          g .Edge s d = Σ[ e ∈ ∣ F.₀ false ∣ ]  F.₁ false e ≡ s × F.₁ true e ≡ d
          g .Vertex-is-set = hlevel 2
          g .Edge-is-set = hlevel 2

  open is-precat-iso
  open is-iso
  g→p-is-iso : is-precat-iso (graph→presheaf {ℓ} {ℓ})
  g→p-is-iso .has-is-ff = g→p-is-ff
  g→p-is-iso .has-is-iso = is-iso→is-equiv F₀-iso where
    F₀-iso : is-iso (graph→presheaf .F₀)
    F₀-iso .inv = presheaf→graph
    F₀-iso .rinv F = Functor-path
      (λ { false  → n-ua (Iso→Equiv (
            (λ (_ , _ , x , _ , _) → x) , iso
            (λ s → _ , _ , s , refl , refl)
            (λ _ → refl)
            (λ (_ , _ , s , p , q) i → p i , q i , s
                                     , (λ j → p (i ∧ j)) , (λ j → q (i ∧ j)))))
          ; true → n-ua (lower
                        , (is-iso→is-equiv (iso lift (λ _ → refl) (λ _ → refl))))
          })
      λ { {false} {false} e → ua→ λ _ → path→ua-pathp _ (sym (F .F-id {false} # _))
        ; {false} {true} false → ua→ λ (_ , _ , s , p , q) → path→ua-pathp _ (sym p)
        ; {false} {true} true → ua→ λ (_ , _ , s , p , q) → path→ua-pathp _ (sym q)
        ; {true} {true} e → ua→ λ _ → path→ua-pathp _ (sym (F .F-id {true} # _)) }
    F₀-iso .linv G = let
      eqv : Lift ℓ ⌞ G ⌟ ≃ ⌞ G ⌟
      eqv = Lift-≃

      ΣE = Σ[ s ∈ G ] Σ[ t ∈ G ] G .Edge s t

      E' : Lift ℓ ⌞ G ⌟ → Lift ℓ ⌞ G ⌟ → Type _
      E' x y = Σ[ (s , t , e) ∈ ΣE ] (lift s ≡ x × lift t ≡ y)

      from : (u v : ⌞ G ⌟) → E' (lift u) (lift v) → G .Edge u v
      from u v ((u' , v' , e) , p , q) = subst₂ (G .Edge) (ap lower p) (ap lower q) e

      frome : (u v : ⌞ G ⌟) → is-iso (from u v)
      frome u v = iso (λ e → ((_ , _ , e) , refl , refl)) (λ x → transport-refl _)
        (λ ((u' , v' , e) , p , q) i →
          ( p (~ i) .lower , q (~ i) .lower
          , coe0→i (λ i → G .Edge (p i .lower) (q i .lower)) (~ i) e )
          , (λ j → p (~ i ∨ j))
          , (λ j → q (~ i ∨ j)))
      in Graph-path (ua eqv) λ i x y → Glue (G .Edge (ua-unglue eqv i x)
                                                     (ua-unglue eqv i y)) λ where
        (i = i0) → E' x y , from (x .lower) (y .lower) , is-iso→is-equiv (frome _ _)
        (i = i1) → G .Edge x y , _ , id-equiv
```
-->

Thus, $\Graphs$ are presheaves and are thereby a [[topos]].

```agda
  graphs-are-presheaves : Equivalence (Graphs ℓ ℓ) (PSh ℓ ·⇇·)
  graphs-are-presheaves = eqv where
    open Equivalence
    eqv : Equivalence (Graphs ℓ ℓ) (PSh ℓ ·⇇·)
    eqv .To = graph→presheaf
    eqv .To-equiv = is-precat-iso→is-equivalence g→p-is-iso
```

## The underlying graph of a strict category {defines="underlying-graph underlying-graph-functor"}

Note that every [[strict category]] has an underlying graph, where
the vertices are given by objects, and edges by morphisms. Moreover,
functors between strict categories give rise to graph homomorphisms
between underlying graphs. This gives rise to a functor from the
[[category of strict categories]] to the category of graphs.

```agda
Strict-cats↪Graphs : Functor (Strict-cats o ℓ) (Graphs o ℓ)
Strict-cats↪Graphs .F₀ (C , C-strict) .Vertex = Precategory.Ob C
Strict-cats↪Graphs .F₀ (C , C-strict) .Edge = Precategory.Hom C
Strict-cats↪Graphs .F₀ (C , C-strict) .Vertex-is-set = C-strict
Strict-cats↪Graphs .F₀ (C , C-strict) .Edge-is-set = Precategory.Hom-set C _ _
Strict-cats↪Graphs .F₁ F .vertex = F .F₀
Strict-cats↪Graphs .F₁ F .edge = F .F₁
Strict-cats↪Graphs .F-id = Graph-hom-path (λ _ → refl) (λ _ → refl)
Strict-cats↪Graphs .F-∘ F G = Graph-hom-path (λ _ → refl) (λ _ → refl)
```

The underlying graph functor is faithful, as functors are graph homomorphisms
with extra properties.

```agda
Strict-cats↪Graphs-faithful : is-faithful (Strict-cats↪Graphs {o} {ℓ})
Strict-cats↪Graphs-faithful p =
  Functor-path
    (λ x i → p i .vertex x)
    (λ e i → p i .edge e)
```
