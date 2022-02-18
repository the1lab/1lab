```agda
open import Cat.Instances.Terminal
open import Cat.Instances.Functor
open import Cat.Prelude

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

# Comma categories

The **comma category** of two functors $F : \ca{A} \to \ca{C}$ and $G :
\ca{B} \to \ca{C}$ with common domain, written $F \downarrow G$, is the
directed, bicategorical analogue of a [pullback] square. It consists of
maps in $\ca{C}$ which all have their domain in the image of $F$, and
codomain in the image of $G$.

[pullback]: Cat.Diagram.Pullback.html

The comma category is the universal way of completing a cospan of
functors $A \to C \ot B$ to a homotopy commutative square like the one
below. Note the similarity with a pullback square; However, since this
is a bicategorical limit, rather than having an _equality_ witnessing
the square commutes, we have a natural transformation $\theta$.

~~~{.quiver}
\[\begin{tikzcd}
  {F\downarrow G} && \mathcal{A} \\
  \\
  \mathcal{B}     && \mathcal{C}
  \arrow["F", from=1-3, to=3-3]
  \arrow["G"', from=3-1, to=3-3]
  \arrow["{\mathrm{dom}}", from=1-1, to=1-3]
  \arrow["{\mathrm{cod}}"', from=1-1, to=3-1]
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
```
-->

The objects in $F \downarrow G$ are given by triples $(x, y, f)$ where
$x : \ca{A}$, $y : \ca{B}$, and $f : F(x) \to G(y)$.

```agda
  record ↓Obj : Type (h ⊔ ao ⊔ bo) where
    no-eta-equality
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
  ↓Hom-path : ∀ {x y} {f g : ↓Hom x y}
            → (f .↓Hom.α ≡ g .↓Hom.α)
            → (f .↓Hom.β ≡ g .↓Hom.β)
            → f ≡ g
  ↓Hom-path p q i .↓Hom.α = p i
  ↓Hom-path p q i .↓Hom.β = q i
  ↓Hom-path {x} {y} {f} {g} p q i .↓Hom.sq = 
    isProp→PathP (λ i → C.Hom-set _ _ (↓Obj.map y C.∘ F₁ F (p i)) 
                                      (F₁ G (q i) C.∘ ↓Obj.map x))
      (f .↓Hom.sq) (g .↓Hom.sq) i

  ↓Hom-set : ∀ x y → isSet (↓Hom x y)
  ↓Hom-set a b = hl' where abstract
    module a = ↓Obj a
    module b = ↓Obj b

    T : Type (h ⊔ bh ⊔ ah)
    T = 
      Σ[ α ∈ Hom A a.x b.x ] 
      Σ[ β ∈ Hom B a.y b.y ] 
      (b.map C.∘ F₁ F α ≡ F₁ G β C.∘ a.map)

    encode : T → ↓Hom a b
    encode (α , β , sq) .↓Hom.α = α
    encode (α , β , sq) .↓Hom.β = β
    encode (α , β , sq) .↓Hom.sq = sq

    decode : ↓Hom a b → T
    decode r = r .↓Hom.α , r .↓Hom.β , r .↓Hom.sq

    hl : isSet T
    hl = isHLevelΣ 2 (A.Hom-set _ _) λ _ → 
         isHLevelΣ 2 (B.Hom-set _ _) λ _ →
         isProp→isSet (C.Hom-set _ _ _ _)

    encode∘decode : isLeftInverse encode decode
    encode∘decode x i .↓Hom.α  = x .↓Hom.α
    encode∘decode x i .↓Hom.β  = x .↓Hom.β
    encode∘decode x i .↓Hom.sq = x .↓Hom.sq

    hl' : isSet (↓Hom a b)
    hl' = isHLevel-retract 2 encode decode encode∘decode hl
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

  infix 4 _↙_ _↘_
  _↙_ : A.Ob → Functor B A → Precategory _ _
  X ↙ T = const! X ↓ T

  _↘_ : Functor B A → A.Ob → Precategory _ _
  S ↘ X = S ↓ const! X
```
-->
