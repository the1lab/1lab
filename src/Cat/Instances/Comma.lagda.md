<!--
```agda
open import Cat.Instances.Shape.Terminal
open import Cat.Prelude
```
-->

```agda
module Cat.Instances.Comma where
```

<!--
```agda
private variable
  o h ao ah bo bh : Level
  A B C : Precategory o h
open Precategory
open Functor
```
-->

# Comma categories {defines="comma-category"}

The **comma category** of two functors $F : \cA \to \cC$ and $G : \cB
\to \cC$ with common codomain, written $F \downarrow G$, is the
directed, bicategorical analogue of a [[pullback]] square. It consists
of maps in $\cC$ which all have their domain in the image of $F$, and
codomain in the image of $G$.

The comma category is the universal way of completing a [cospan] of
functors $A \to C \ot B$ to a square, like the one below, which commutes
_up to a natural transformation_ $\theta$. Note the similarity with a
[[pullback]] square.

[cospan]: Cat.Instances.Shape.Cospan.html

~~~{.quiver}
\[\begin{tikzcd}
  {F\downarrow G} && \mathcal{A} \\
  \\
  \mathcal{B}     && \mathcal{C}
  \arrow["F", from=1-3, to=3-3]
  \arrow["G"', from=3-1, to=3-3]
  \arrow["{\rm{dom}}", from=1-1, to=1-3]
  \arrow["{\rm{cod}}"', from=1-1, to=3-1]
  \arrow["\theta"{description}, Rightarrow, from=1-1, to=3-3]
\end{tikzcd}\]
~~~

<!--
```agda
module
  _ {A : Precategory ao ah}
    {B : Precategory bo bh}
    {C : Precategory o h}
    (F : Functor A C) (G : Functor B C) where

  private
    module A = Precategory A
    module B = Precategory B
    import Cat.Reasoning C as C

  open A.HLevel-instance
  open B.HLevel-instance
  open C.HLevel-instance
```
-->

The objects in $F \downarrow G$ are given by triples $(x, y, f)$ where
$x : \cA$, $y : \cB$, and $f : F(x) \to G(y)$.

```agda
  record ↓Obj : Type (h ⊔ ao ⊔ bo) where
    no-eta-equality
    constructor ↓obj
    field
      {x} : Ob A
      {y} : Ob B
      map : Hom C (F₀ F x) (F₀ G y)
```

A morphism from $(x_a, y_a, f_a) \to (x_b, y_b, f_b)$ is given by a pair
of maps $\alpha : x_a \to x_b$ and $\beta : y_a \to y_b$, such that the
square below commutes. Note that this is exactly the data of one
component of a [naturality square].

[naturality square]: Cat.Base.html#natural-transformations

~~~{.quiver}
\[\begin{tikzcd}
  {F(x_a)} && {G(y_a)} \\
  \\
  {F(x_b)} && {G(y_b)}
  \arrow["{f_b}"', from=3-1, to=3-3]
  \arrow["{f_a}", from=1-1, to=1-3]
  \arrow["{F(\alpha)}"', from=1-1, to=3-1]
  \arrow["{G(\beta)}", from=1-3, to=3-3]
\end{tikzcd}\]
~~~

```agda
  record ↓Hom (a b : ↓Obj) : Type (h ⊔ bh ⊔ ah) where
    no-eta-equality
    constructor ↓hom
    private
      module a = ↓Obj a
      module b = ↓Obj b

    field
      {α} : Hom A a.x b.x
      {β} : Hom B a.y b.y
      sq : b.map C.∘ F₁ F α ≡ F₁ G β C.∘ a.map
```

We omit routine characterisations of equality in `↓Hom`{.Agda} from the
page: `↓Hom-path`{.Agda} and `↓Hom-set`{.Agda}.

<!--
```agda
  ↓Hom-pathp : ∀ {x x' y y'} {p : x ≡ x'} {q : y ≡ y'}
             → {f : ↓Hom x y} {g : ↓Hom x' y'}
             → (PathP _ (f .↓Hom.α) (g .↓Hom.α))
             → (PathP _ (f .↓Hom.β) (g .↓Hom.β))
             → PathP (λ i → ↓Hom (p i) (q i)) f g
  ↓Hom-pathp p q i .↓Hom.α = p i
  ↓Hom-pathp p q i .↓Hom.β = q i
  ↓Hom-pathp {p = p} {q} {f} {g} r s i .↓Hom.sq =
    is-prop→pathp (λ i → C.Hom-set _ _ (↓Obj.map (q i) C.∘ F₁ F (r i))
                                       (F₁ G (s i) C.∘ ↓Obj.map (p i)))
      (f .↓Hom.sq) (g .↓Hom.sq) i

  ↓Hom-path : ∀ {x y} {f g : ↓Hom x y}
            → (f .↓Hom.α ≡ g .↓Hom.α)
            → (f .↓Hom.β ≡ g .↓Hom.β)
            → f ≡ g
  ↓Hom-path = ↓Hom-pathp

  ↓Obj-path : {a b : ↓Obj}
            → (p : a .↓Obj.x ≡ b .↓Obj.x) (q : a .↓Obj.y ≡ b .↓Obj.y)
            → PathP (λ i → Hom C (F₀ F (p i)) (F₀ G (q i))) (a .↓Obj.map) (b .↓Obj.map)
            → a ≡ b
  ↓Obj-path p q r i .↓Obj.x = p i
  ↓Obj-path p q r i .↓Obj.y = q i
  ↓Obj-path p q r i .↓Obj.map = r i

  private unquoteDecl eqv = declare-record-iso eqv (quote ↓Hom)

  ↓Hom-set : ∀ x y → is-set (↓Hom x y)
  ↓Hom-set a b = hl' where abstract
    hl' : is-set (↓Hom a b)
    hl' = Iso→is-hlevel 2 eqv (hlevel 2)
```
-->

Identities and compositions are given componentwise:

```agda
  ↓id : ∀ {a} → ↓Hom a a
  ↓id .↓Hom.α = A.id
  ↓id .↓Hom.β = B.id
  ↓id .↓Hom.sq = ap (_ C.∘_) (F-id F) ·· C.id-comm ·· ap (C._∘ _) (sym (F-id G))

  ↓∘ : ∀ {a b c} → ↓Hom b c → ↓Hom a b → ↓Hom a c
  ↓∘ {a} {b} {c} g f = composite where
    open ↓Hom

    module a = ↓Obj a
    module b = ↓Obj b
    module c = ↓Obj c
    module f = ↓Hom f
    module g = ↓Hom g

    composite : ↓Hom a c
    composite .α = g.α A.∘ f.α
    composite .β = g.β B.∘ f.β
    composite .sq =
      c.map C.∘ F₁ F (g.α A.∘ f.α)    ≡⟨ ap (_ C.∘_) (F-∘ F _ _) ⟩
      c.map C.∘ F₁ F g.α C.∘ F₁ F f.α ≡⟨ C.extendl g.sq ⟩
      F₁ G g.β C.∘ b.map C.∘ F₁ F f.α ≡⟨ ap (_ C.∘_) f.sq ⟩
      F₁ G g.β C.∘ F₁ G f.β C.∘ a.map ≡⟨ C.pulll (sym (F-∘ G _ _)) ⟩
      F₁ G (g.β B.∘ f.β) C.∘ a.map    ∎
```

This assembles into a precategory.

```agda
  _↓_ : Precategory _ _
  _↓_ .Ob = ↓Obj
  _↓_ .Hom = ↓Hom
  _↓_ .Hom-set = ↓Hom-set
  _↓_ .id = ↓id
  _↓_ ._∘_ = ↓∘
  _↓_ .idr f = ↓Hom-path (A.idr _) (B.idr _)
  _↓_ .idl f = ↓Hom-path (A.idl _) (B.idl _)
  _↓_ .assoc f g h = ↓Hom-path (A.assoc _ _ _) (B.assoc _ _ _)
```

We also have the projection functors onto the factors, and the natural
transformation $\theta$ witnessing "directed commutativity" of the
square.

```agda
  Dom : Functor _↓_ A
  Dom .F₀ = ↓Obj.x
  Dom .F₁ = ↓Hom.α
  Dom .F-id = refl
  Dom .F-∘ _ _ = refl

  Cod : Functor _↓_ B
  Cod .F₀ = ↓Obj.y
  Cod .F₁ = ↓Hom.β
  Cod .F-id = refl
  Cod .F-∘ _ _ = refl

  θ : (F F∘ Dom) => (G F∘ Cod)
  θ = NT (λ x → x .↓Obj.map) λ x y f → f .↓Hom.sq
```

<!--
```agda
module _ {A : Precategory ao ah} {B : Precategory bo bh} where
  private module A = Precategory A

  infix 5 _↙_ _↘_
  _↙_ : A.Ob → Functor B A → Precategory _ _
  X ↙ T = const! X ↓ T

  _↘_ : Functor B A → A.Ob → Precategory _ _
  S ↘ X = S ↓ const! X
```
-->
