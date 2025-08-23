<!--
```agda
open import Cat.Instances.Graphs.Representable
open import Cat.Instances.Graphs.Limits
open import Cat.Instances.Graphs
open import Cat.Diagram.Omega
open import Cat.Prelude

import Cat.Displayed.Instances.Subobjects.Reasoning as Sub

open Graph-hom
open Graph
```
-->

```agda
module Cat.Instances.Graphs.Omega where
```

# The subgraph classifier

<!--
```agda
private
  module _ {o ℓ} where open Sub (Graphs-pullbacks {o} {ℓ}) public

  variable
    o ℓ o' ℓ' : Level
    X Y Z : Graph o ℓ
```
-->

Since the category of [[graphs]] is a presheaf category, we know for a
fact that it has a [[subobject classifier]], and we could simply
transport this result over the equivalence to obtain the 'subgraph
classifier'. However, since the shape category for graphs is very
simple, we can directly compute what this classifier is in terms of nodes
and edges.

:::{.definition #subgraph-classifier}
The **subgraph classifier** is the [[graph]] with nodes the set $\Omega$
of [[propositions]], and such that the edges from $P$ to $Q$ are the
*spans* $P \ot V \to Q$ from $P$ to $Q$.
:::

Intuitively, a map into the subgraph classifier assigns to each node the
proposition of whether it belongs to the subgraph; and, to each edge, a
proposition indicating belonging of the edge, which additionally
remembers that an edge can only be included if its endpoints are.

```agda
Ωᴳ : Graph o ℓ
Ωᴳ .Node     = Lift _ Ω
Ωᴳ .Edge P Q = Σ[ e ∈ Lift _ Ω ] (⌞ e ⌟ → ⌞ P ⌟) × (⌞ e ⌟ → ⌞ Q ⌟)
Ωᴳ .Node-set = hlevel 2
Ωᴳ .Edge-set = hlevel 2
```

The "true" arrow into the subgraph classifier simply picks out the true
proposition `⊤Ω`{.Agda}, and the true span over that. We now turn to
showing the universal property of $\Omega$ as a graph.

```agda
trueᴳ : Graph-hom (⊤ᴳ {o} {ℓ}) (Ωᴳ {o'} {ℓ'})
trueᴳ .node _ = lift ⊤Ω
trueᴳ .edge _ = lift ⊤Ω , _ , _
```

<!--
```agda
private
  tru' : Subobject (Ωᴳ {o'} {ℓ'})
  tru' = point→subobject Graphs-finitely-complete Graphs-is-category trueᴳ
```
-->

For this, suppose that we have a subgraph $m : M \mono X$. We want to
compute a "name" $\name{m} : X \to \Omega$. First, the fibres $m^*(x)$
over the nodes $x : X$ are propositions, so we can directly take this as
the node part of $\name{m}$.

```agda
private module work (m : Subobject X) where
  Nodes : X .Node → Type _
  Nodes x = fibre (m .map .node) x
```

However, we can only ask about the fibres $m^*(e)$ for edges between
$m(x)$ and $m(y)$ in $X$, i.e. those for which the endpoints literally
come from $M$. We can extend this to work for arbitrary $e : x \to y$ by
quantifying fibres $(x', p) : m^*(x)$ and $(y', q) : m^*(y)$ over the
endpoints, and then asking for a fibre of $m$ over the transport of $e$
to an edge $e' : m(x') \to m(y')$ along $p$ and $q$.

```agda
  Edges : ∀ {x y} → X .Edge x y → Type _
  Edges {x} {y} e =
    Σ[ (mx , p) ∈ Nodes x ]
    Σ[ (my , q) ∈ Nodes y ]
    fibre (m .map .edge) (subst₂ (X .Edge) (sym p) (sym q) e)
```

Since both the node and edge part of a monomorphism of graphs are
[[set]] [[embeddings]], these types are propositions; and, by
construction, our predicate on edges implies that both endpoints are
also included. We thus have a map into the subgraph classifier.

<!--
```agda
  open Subobject m renaming (map to mm) using ()

  node-emb : is-embedding (mm .node)
  node-emb = is-monic→node-is-embedding (m .monic)

  edge-emb : ∀ {x y} → is-embedding (mm .edge {x} {y})
  edge-emb = is-monic→edge-is-embedding (m .monic)

  nodes : X .Node → Ω
  nodes x = elΩ (Nodes x)

  Edges-is-prop : ∀ {x y} {e : X .Edge x y} → is-prop (Edges e)
  Edges-is-prop = Σ-is-hlevel 1 (node-emb _) λ _ → Σ-is-hlevel 1 (node-emb _) λ _ → edge-emb _

  edges : ∀ {x y} → X .Edge x y → Ω
  edges e = elΩ (Edges e)
```
-->

```agda
  name : Graph-hom X (Ωᴳ {o} {ℓ})
  name .node x = lift (nodes x)
  name .edge {x} {y} e = record
    { fst = lift (edges e)
    ; snd = rec! (λ mx p _ _ _ _ → inc (mx , p))
          , rec! (λ _ _ my q _ _ → inc (my , q))
    }
```

Let us show that this construction is an equivalence between subgraphs
and their names. We define a helper function for recovering a fibre over
a node from the information that our proposition about nodes is true.

```agda
  from-node : ∀ {x} → lift {ℓ = ℓ} (nodes x) ≡ lift ⊤Ω → fibre (mm .node) x
  from-node p = □-out (node-emb _) (from-is-true (ap lower p))
```

To recover an edge, we have to work a bit harder. First, we presuppose
that we already have fibres $p, q$ over the source and target nodes.
Projecting the information from our `Edges`{.Agda} proposition at some
$e$ then gives a *new* pair of fibres $p', q'$, an edge $e'$ between
these fibres, and a proof that $m(e')$ is the transport of $e$ along
$p'$, $q'$.

```agda
  from-edge
    : {x y : ⌞ X ⌟} {e : X .Edge x y}
    → ((mx , p) : Nodes x) ((my , q) : Nodes y)
    → e ∈ edges
    → fibre (mm .edge) (subst₂ (X .Edge) (sym p) (sym q) e)
  from-edge {x} {y} {e} (mx , p) (my , q) w
    using ((mx' , p') , (my' , q') , e⁻¹' , γ) ← □-out {A = Edges e} Edges-is-prop w =
    record { fst = subst₂ (m .dom .Edge) x⁻¹p y⁻¹p e⁻¹'
           ; snd = rem₁
           }
    where abstract
```

This is almost what we want, except the transport is in the wrong place
and talks about the wrong paths. We can fix this up by showing that the
fibres (hence the nodes) must be identical, since $m$ is an embedding on
nodes, and some algebra regarding transports.

```agda
    x⁻¹p : mx' ≡ mx
    x⁻¹p = ap fst (node-emb _ (mx' , p') (mx , p))

    y⁻¹p : my' ≡ my
    y⁻¹p = ap fst (node-emb _ (my' , q') (my , q))

    rem₁ : mm .edge (subst₂ (m .dom .Edge) x⁻¹p y⁻¹p e⁻¹')
         ≡ subst₂ (X .Edge) (sym p) (sym q) e
    rem₁ =
      mm .edge (subst₂ (m .dom .Edge) x⁻¹p y⁻¹p e⁻¹')
        ≡⟨ sym (subst₂-fibrewise (λ x y → mm .edge {x} {y}) x⁻¹p y⁻¹p e⁻¹') ⟩
      subst₂ (X .Edge) (ap· mm x⁻¹p) (ap· mm y⁻¹p)
        (mm .edge e⁻¹')
        ≡⟨ ap (subst₂ (X .Edge) (ap· mm x⁻¹p) (ap· mm y⁻¹p)) γ ⟩
      subst₂ (X .Edge) (ap· mm x⁻¹p) (ap· mm y⁻¹p)
        (subst₂ (X .Edge) (sym p') (sym q') e)
        ≡⟨ sym (subst₂-∙ (X .Edge) _ _ _ _ e) ⟩
      subst₂ (X .Edge) _ _ e
        ≡⟨ ap₂ (λ a b → subst₂ (X .Edge) {b' = m .map .node my} a b e) prop! prop! ⟩
      subst₂ (X .Edge) (sym p) (sym q) e
        ∎
```

This provides all we need to show that $m$ is the pullback of the true
arrow along its name. We show that the subobjects are mutually embedded:
in one direction, we can trivially show that the propositions are true
by constructing the fibres. In the converse direction, we can use the
helper functions defined above.

```agda
  named-name : m ≅ₘ name ^* tru'
  named-name = Sub-antisym
    record
      { map = record where
        node x = m .map · x , lift tt , ap lift (to-is-true (inc (x , refl)))
        edge {x} {y} e = m .map .edge e , lift tt , Σ-pathp
          (ap lift (to-is-true
            (inc ((x , refl) , (y , refl) , e , sym (transport-refl _)))))
          (to-pathp refl)
      ; com = Graph-hom-path (λ x → refl) (λ x → refl)
      }
    record
      { map = record where
        node (x , lift tt , e) = from-node e .fst
        edge {x , lift tt , p} {y , lift tt , q} (e , lift tt , pe) = from-edge
          (from-node p) (from-node q)
          (from-is-true (ap lower (apd (λ i → fst) pe))) .fst
      ; com = ext λ where
        .node x _ e → sym (from-node e .snd)
        .edge {x , _ , p} {y , _ , q} (e , _ , pe) → to-pathp $ sym $
          from-edge (from-node p) (from-node q)
            (from-is-true (ap lower (apd (λ i → fst) pe))) .snd }
```

<details>
<summary>Showing that you get back $h : X \to \Omega$ after into a
subgraph by pulling back the true arrow and computing its name is a
similar calculation.</summary>

```agda
private module mk = make-subobject-classifier

name-named : (h : Graphs.Hom X Ωᴳ) → work.name (h ^* tru') ≡ h
name-named {X = X} h = Graph-hom-path nodep λ e → Σ-prop-pathp rem (edgep e) where
  open work (h ^* tru')

  nodep : ∀ x → lift (elΩ (Nodes x)) ≡ h .node x
  nodep x = ap lift $ Ω-ua
    (λ e →
      let (x , lift tt , p) , α = (□-out (node-emb _) e)
       in subst (λ e → ⌞ h .node e ⌟) α (from-is-true (ap lower p)))
    (λ hx → inc ((x , _ , ap lift (to-is-true hx)) , refl))

  edgep : ∀ {x y} (e : X .Edge x y) → lift (elΩ (Edges e)) ≡ h .edge e .fst
  edgep {x} {y} e = ap lift $ Ω-ua
    (λ fb →
      let
        (((x⁻¹ , _) , α) , ((y⁻¹ , _) , β) , (e⁻¹ , lift tt , p) , γ) =
          □-out Edges-is-prop fb
      in subst₂ {A = X .Node × X .Node} {B = uncurry (X .Edge)}
          (λ (x , y) e → e ∈ h .edge {x} {y})
          (Σ-pathp α β) (to-pathp⁻ γ)
          (from-is-true (ap lower (apd (λ i → fst) p))))

    (λ he → inc (
        ((x , _ , ap lift (to-is-true (h .edge e .snd .fst he))) , refl)
      , ((y , _ , ap lift (to-is-true (h .edge e .snd .snd he))) , refl)
      , (e , _ , Σ-pathp (ap lift (to-is-true he)) (to-pathp refl))
      , sym (transport-refl _)))

  rem : ∀ {x y} (i : I) (A : Lift ℓ Ω)
      → is-prop ((⌞ A ⌟ → ⌞ nodep x i ⌟) × (⌞ A ⌟ → ⌞ nodep y i ⌟))
  rem {x = x} {y} i _ = ×-is-hlevel 1
    (fun-is-hlevel 1 (nodep x i .lower .is-tr))
    (fun-is-hlevel 1 (nodep y i .lower .is-tr))
```

</details>

Since the category of graphs is [[univalent|univalent category]], these
constructs suffice to show it has a subobject classifier.

```agda
Graph-omega : Subobject-classifier (Graphs o ℓ)
Graph-omega = to-subobject-classifier Graphs-finitely-complete Graphs-is-category
  λ where
    .mk.Ω          → Ωᴳ
    .mk.true       → trueᴳ
    .mk.name       m → work.name m
    .mk.name-named m → name-named m
    .mk.named-name m → work.named-name m
```
