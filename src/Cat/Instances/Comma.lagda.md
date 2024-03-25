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

-- Outside the main module to make instance search work.
module _ where
  open ↓Hom
  open ↓Obj
  open Precategory
  open Functor


  Extensional-↓Hom
    : ∀ {ℓr}
    → {F : Functor A C} {G : Functor B C}
    → {f g : ↓Obj F G}
    → ⦃ sab : Extensional (A .Hom (f .x) (g .x) × B .Hom (f .y) (g .y)) ℓr ⦄
    → Extensional (↓Hom F G f g) ℓr
  Extensional-↓Hom {A = A} {B = B} {F = F} {G = G} {f = f} {g = g} ⦃ sab ⦄ =
    injection→extensional! (λ p → ↓Hom-path F G (ap fst p) (ap snd p)) sab
    where
      open Precategory.HLevel-instance A
      open Precategory.HLevel-instance B

  -- Overlapping instances for ↙ and ↘; these resolve issues where
  -- Agda cannot determine the source category A for 'Const'. We can
  -- also optimize the instance a bit to avoid a silly obligation that
  -- 'tt ≡ tt'.
  Extensional-↙Hom
    : ∀ {ℓr}
    → {X : A .Ob} {T : Functor B A}
    → {f g : ↓Obj (const! X) T}
    → ⦃ sb : Extensional (B .Hom (f .y) (g .y)) ℓr ⦄
    → Extensional (↓Hom (const! X) T f g) ℓr
  Extensional-↙Hom {B = B} {X = X} {T = T} {f = f} {g = g} ⦃ sb ⦄ =
    injection→extensional! {f = λ sq → sq .β} (λ p → ↓Hom-path (const! X) T refl p) sb
    where
      open Precategory.HLevel-instance B

  Extensional-↘Hom
    : ∀ {ℓr}
    → {T : Functor A B} {X : B .Ob}
    → {f g : ↓Obj T (const! X)}
    → ⦃ sa : Extensional (A .Hom (f .x) (g .x)) ℓr ⦄
    → Extensional (↓Hom T (const! X) f g) ℓr
  Extensional-↘Hom {A = A} {T = T} {X = X} {f = f} {g = g} ⦃ sa ⦄ =
    injection→extensional! {f = λ sq → sq .α} (λ p → ↓Hom-path T (const! X) p refl) sa
    where
      open Precategory.HLevel-instance A

  instance
    Extensionality-↓Hom
      : ∀ {F : Functor A C} {G : Functor B C}
      → {f g : ↓Obj F G}
      → Extensionality (↓Hom F G f g)
    Extensionality-↓Hom = record { lemma = quote Extensional-↓Hom }

    Extensionality-↙Hom
      : ∀ {X : A .Ob} {T : Functor B A}
      → {f g : ↓Obj (const! X) T}
      → Extensionality (↓Hom (const! X) T f g)
    Extensionality-↙Hom = record { lemma = quote Extensional-↙Hom }

    Extensionality-↘Hom
      : ∀ {T : Functor A B} {X : B .Ob}
      → {f g : ↓Obj T (const! X)}
      → Extensionality (↓Hom T (const! X) f g)
    Extensionality-↘Hom = record { lemma = quote Extensional-↘Hom }

  -- Extensionality cannot handle PathP, but we /can/ make a bit of progress
  -- by deleting 'tt ≡ tt' obligations when using ↙ and ↘.
  Extensional-↙Obj
    : ∀ {ℓr}
    → {X : A .Ob} {T : Functor B A}
    → ⦃ sb : Extensional (Σ[ Y ∈ B .Ob ] (A .Hom X (T .F₀ Y))) ℓr ⦄
    → Extensional (↓Obj (const! X) T) ℓr
  Extensional-↙Obj {A = A} {B = B} {X = X} {T = T} ⦃ sb ⦄ =
    iso→extensional isom sb
      where
        -- Easier to just do this by hand.
        isom : Iso (↓Obj (const! X) T) (Σ[ Y ∈ B .Ob ] (A .Hom X (T .F₀ Y)))
        isom .fst α = ↓Obj.y α , ↓Obj.map α
        isom .snd .is-iso.inv (Y , f) = ↓obj f
        isom .snd .is-iso.rinv _ = refl
        isom .snd .is-iso.linv _ = ↓Obj-path (const! X) T refl refl refl

  Extensional-↘Obj
    : ∀ {ℓr}
    → {T : Functor A B} {Y : B .Ob}
    → ⦃ sb : Extensional (Σ[ X ∈ A .Ob ] (B .Hom (T .F₀ X) Y)) ℓr ⦄
    → Extensional (↓Obj T (const! Y)) ℓr
  Extensional-↘Obj {A = A} {B = B} {T = T} {Y = Y} ⦃ sb ⦄ =
    iso→extensional isom sb
      where
        -- Easier to just do this by hand.
        isom : Iso (↓Obj T (const! Y)) (Σ[ X ∈ A .Ob ] (B .Hom (T .F₀ X) Y))
        isom .fst α = ↓Obj.x α , ↓Obj.map α
        isom .snd .is-iso.inv (Y , f) = ↓obj f
        isom .snd .is-iso.rinv _ = refl
        isom .snd .is-iso.linv _ = ↓Obj-path T (const! Y) refl refl refl

  instance
    Extensionality-↙Obj
      : ∀ {X : A .Ob} {T : Functor B A}
      → Extensionality (↓Obj (const! X) T)
    Extensionality-↙Obj = record { lemma = quote Extensional-↙Obj }

    Extensionality-↘Obj
      : ∀ {T : Functor A B} {Y : B .Ob}
      → Extensionality (↓Obj T (const! Y))
    Extensionality-↘Obj = record { lemma = quote Extensional-↘Obj }
      
```
-->
