<!--
```agda
open import Cat.Instances.Shape.Terminal
open import Cat.Functor.Constant
open import Cat.Functor.Compose
open import Cat.Functor.Base
open import Cat.Groupoid
open import Cat.Morphism
open import Cat.Prelude

import Cat.Functor.Reasoning
import Cat.Reasoning
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
    module C = Cat.Reasoning C
    module F = Cat.Functor.Reasoning F
    module G = Cat.Functor.Reasoning G
```
-->

The objects in $F \downarrow G$ are given by triples $(x, y, f)$ where
$x : \cA$, $y : \cB$, and $f : F(x) \to G(y)$.

```agda
  record ↓Obj : Type (h ⊔ ao ⊔ bo) where
    no-eta-equality
    constructor ↓obj
    field
      {dom} : Ob A
      {cod} : Ob B
      map   : Hom C (F .F₀ dom) (G .F₀ cod)
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
      {top} : Hom A a.dom b.dom
      {bot} : Hom B a.cod b.cod
      com   : b.map C.∘ F .F₁ top ≡ G .F₁ bot C.∘ a.map
```

We omit routine characterisations of equality in `↓Hom`{.Agda} from the
page: `↓Hom-path`{.Agda} and `↓Hom-set`{.Agda}.

<!--
```agda
  {-# INLINE ↓obj #-}
  {-# INLINE ↓hom #-}

  ↓Hom-pathp : ∀ {x x' y y'} {p : x ≡ x'} {q : y ≡ y'}
             → {f : ↓Hom x y} {g : ↓Hom x' y'}
             → (PathP _ (f .↓Hom.top) (g .↓Hom.top))
             → (PathP _ (f .↓Hom.bot) (g .↓Hom.bot))
             → PathP (λ i → ↓Hom (p i) (q i)) f g
  ↓Hom-pathp p q i .↓Hom.top = p i
  ↓Hom-pathp p q i .↓Hom.bot = q i
  ↓Hom-pathp {p = p} {q} {f} {g} r s i .↓Hom.com =
    is-prop→pathp (λ i → C.Hom-set _ _ (↓Obj.map (q i) C.∘ F .F₁ (r i))
                                       (G .F₁ (s i) C.∘ ↓Obj.map (p i)))
      (f .↓Hom.com) (g .↓Hom.com) i

  ↓Hom-path : ∀ {x y} {f g : ↓Hom x y}
            → (f .↓Hom.top ≡ g .↓Hom.top)
            → (f .↓Hom.bot ≡ g .↓Hom.bot)
            → f ≡ g
  ↓Hom-path = ↓Hom-pathp

  ↓Obj-path : {a b : ↓Obj}
            → (p : a .↓Obj.dom ≡ b .↓Obj.dom) (q : a .↓Obj.cod ≡ b .↓Obj.cod)
            → PathP (λ i → Hom C (F .F₀ (p i)) (G .F₀ (q i))) (a .↓Obj.map) (b .↓Obj.map)
            → a ≡ b
  ↓Obj-path p q r i .↓Obj.dom = p i
  ↓Obj-path p q r i .↓Obj.cod = q i
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
  ↓id .↓Hom.top = A.id
  ↓id .↓Hom.bot = B.id
  ↓id .↓Hom.com = ap (_ C.∘_) (F .F-id) ∙∙ C.id-comm ∙∙ ap (C._∘ _) (sym (G .F-id))

  ↓∘ : ∀ {a b c} → ↓Hom b c → ↓Hom a b → ↓Hom a c
  ↓∘ {a} {b} {c} g f = composite where
    open ↓Hom

    module a = ↓Obj a
    module b = ↓Obj b
    module c = ↓Obj c
    module f = ↓Hom f
    module g = ↓Hom g

    composite : ↓Hom a c
    composite .top = g.top A.∘ f.top
    composite .bot = g.bot B.∘ f.bot
    composite .com =
      c.map C.∘ F .F₁ (g.top A.∘ f.top)      ≡⟨ ap (_ C.∘_) (F .F-∘ _ _) ⟩
      c.map C.∘ F .F₁ g.top C.∘ F .F₁ f.top  ≡⟨ C.extendl g.com ⟩
      G .F₁ g.bot C.∘ b.map C.∘ F .F₁ f.top  ≡⟨ ap (_ C.∘_) f.com ⟩
      G .F₁ g.bot C.∘ G .F₁ f.bot C.∘ a.map  ≡⟨ C.pulll (sym (G .F-∘ _ _)) ⟩
      G .F₁ (g.bot B.∘ f.bot) C.∘ a.map      ∎
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
  Dom .F₀ = ↓Obj.dom
  Dom .F₁ = ↓Hom.top
  Dom .F-id = refl
  Dom .F-∘ _ _ = refl

  Cod : Functor _↓_ B
  Cod .F₀ = ↓Obj.cod
  Cod .F₁ = ↓Hom.bot
  Cod .F-id = refl
  Cod .F-∘ _ _ = refl

  θ : (F F∘ Dom) => (G F∘ Cod)
  θ = NT (λ x → x .↓Obj.map) λ x y f → f .↓Hom.com
```

<!--
```agda
  module _ (A-grpd : is-pregroupoid A) (B-grpd : is-pregroupoid B) where
    open ↓Hom
    open is-invertible
    open Inverses

    ↓-is-pregroupoid : is-pregroupoid _↓_
    ↓-is-pregroupoid f .inv .top = A-grpd (f .top) .inv
    ↓-is-pregroupoid f .inv .bot = B-grpd (f .bot) .inv
    ↓-is-pregroupoid f .inv .com = C.rswizzle
      (sym (C.lswizzle (f .com) (G.annihilate (B-grpd (f .bot) .invr))) ∙ C.assoc _ _ _)
      (F.annihilate (A-grpd (f .top) .invl))
    ↓-is-pregroupoid f .inverses .invl = ↓Hom-path (A-grpd (f .top) .invl) (B-grpd (f .bot) .invl)
    ↓-is-pregroupoid f .inverses .invr = ↓Hom-path (A-grpd (f .top) .invr) (B-grpd (f .bot) .invr)

module _ {A : Precategory ao ah} {B : Precategory bo bh} where
  private
    module A = Precategory A
    module B = Precategory B
    variable
      F : Functor A B
  open ↓Obj
  open ↓Hom

  infix 8 _↙_ _↘_
  _↙_ : A.Ob → Functor B A → Precategory _ _
  X ↙ T = !Const X ↓ T

  _↘_ : Functor B A → A.Ob → Precategory _ _
  S ↘ X = S ↓ !Const X

  θ↘ : ∀ {X} → F F∘ Dom F (!Const X) => Const X
  θ↘ ._=>_.η f = f .map
  θ↘ ._=>_.is-natural _ _ γ = γ .com

  θ↙ : ∀ {X} → Const X => F F∘ Cod (!Const X) F
  θ↙ ._=>_.η f = f .map
  θ↙ ._=>_.is-natural _ _ γ = γ .com


module ↙-compose
    {oc ℓc od ℓd oe ℓe}
    {𝒞 : Precategory oc ℓc} {𝒟 : Precategory od ℓd} {ℰ : Precategory oe ℓe}
    (F : Functor 𝒞 𝒟) (G : Functor 𝒟 ℰ)
  where
  private
    module 𝒟 = Precategory 𝒟
    module ℰ = Precategory ℰ
    module F = Functor F
    module G = Cat.Functor.Reasoning G
  open ↓Obj
  open ↓Hom

  _↙>_ : ∀ {d} (g : Ob (d ↙ G)) → Ob (g .cod ↙ F) → Ob (d ↙ G F∘ F)
  g ↙> f = ↓obj (G.₁ (f .map) ℰ.∘ g .map)

  ↙-compose : ∀ {d} (g : Ob (d ↙ G)) → Functor (g .cod ↙ F) (d ↙ G F∘ F)
  ↙-compose g .F₀ f = g ↙> f
  ↙-compose g .F₁ {f} {f'} h = ↓hom {bot = h .bot} $
    (G.₁ (f' .map) ℰ.∘ g .map) ℰ.∘ ℰ.id          ≡⟨ ℰ.idr _ ⟩
    G.₁ (f' .map) ℰ.∘ g .map                     ≡⟨ G.pushl (sym (𝒟.idr _) ∙ h .com) ⟩
    G.₁ (F.₁ (h .bot)) ℰ.∘ G.₁ (f .map) ℰ.∘ g .map ∎
  ↙-compose g .F-id = ↓Hom-path _ _ refl refl
  ↙-compose g .F-∘ _ _ = ↓Hom-path _ _ refl refl

  ↙>-id : ∀ {c} {f : Ob (c ↙ G F∘ F)} → ↓obj (f .map) ↙> ↓obj 𝒟.id ≡ f
  ↙>-id = ↓Obj-path _ _ refl refl (G.eliml refl)


-- Outside the main module to make instance search work.
module _ where
  open ↓Hom
  open ↓Obj
  open Precategory
  open Functor


  instance
    Extensional-↓Hom
      : ∀ {ℓr}
      → {F : Functor A C} {G : Functor B C}
      → {f g : ↓Obj F G}
      → ⦃ sab : Extensional (A .Hom (f .dom) (g .dom) × B .Hom (f .cod) (g .cod)) ℓr ⦄
      → Extensional (↓Hom F G f g) ℓr
    Extensional-↓Hom {A = A} {B = B} {F = F} {G = G} {f = f} {g = g} ⦃ sab ⦄ =
      injection→extensional! (λ p → ↓Hom-path F G (ap fst p) (ap snd p)) sab

    -- Overlapping instances for ↙ and ↘; these resolve issues where
    -- Mikan cannot determine the source category A for 'Const'. We can
    -- also optimize the instance a bit to avoid a silly obligation that
    -- 'tt ≡ tt'.
    Extensional-↙Hom
      : ∀ {ℓr}
      → {X : A .Ob} {T : Functor B A}
      → {f g : ↓Obj (!Const X) T}
      → ⦃ sb : Extensional (B .Hom (f .cod) (g .cod)) ℓr ⦄
      → Extensional (↓Hom (!Const X) T f g) ℓr
    Extensional-↙Hom {B = B} {X = X} {T = T} {f = f} {g = g} ⦃ sb ⦄ =
      injection→extensional! {f = λ sq → sq .bot} (λ p → ↓Hom-path (!Const X) T refl p) sb
    {-# OVERLAPS Extensional-↙Hom #-}

    Extensional-↘Hom
      : ∀ {ℓr}
      → {T : Functor A B} {X : B .Ob}
      → {f g : ↓Obj T (!Const X)}
      → ⦃ sa : Extensional (A .Hom (f .dom) (g .dom)) ℓr ⦄
      → Extensional (↓Hom T (!Const X) f g) ℓr
    Extensional-↘Hom {A = A} {T = T} {X = X} {f = f} {g = g} ⦃ sa ⦄ =
      injection→extensional! {f = λ sq → sq .top} (λ p → ↓Hom-path T (!Const X) p refl) sa
    {-# OVERLAPS Extensional-↘Hom #-}


    -- Extensionality cannot handle PathP, but we /can/ make a bit of progress
    -- by deleting 'tt ≡ tt' obligations when using ↙ and ↘.
    Extensional-↙Obj
      : ∀ {ℓr}
      → {X : A .Ob} {T : Functor B A}
      → ⦃ sb : Extensional (Σ[ Y ∈ B .Ob ] (A .Hom X (T .F₀ Y))) ℓr ⦄
      → Extensional (↓Obj (!Const X) T) ℓr
    Extensional-↙Obj {A = A} {B = B} {X = X} {T = T} ⦃ sb ⦄ =
      iso→extensional isom sb
        where
          -- Easier to just do this by hand.
          isom : Iso (↓Obj (!Const X) T) (Σ[ Y ∈ B .Ob ] (A .Hom X (T .F₀ Y)))
          isom .fst α = ↓Obj.cod α , ↓Obj.map α
          isom .snd .is-iso.from (Y , f) = ↓obj f
          isom .snd .is-iso.rinv _ = refl
          isom .snd .is-iso.linv _ = ↓Obj-path (!Const X) T refl refl refl

    Extensional-↘Obj
      : ∀ {ℓr}
      → {T : Functor A B} {Y : B .Ob}
      → ⦃ sb : Extensional (Σ[ X ∈ A .Ob ] (B .Hom (T .F₀ X) Y)) ℓr ⦄
      → Extensional (↓Obj T (!Const Y)) ℓr
    Extensional-↘Obj {A = A} {B = B} {T = T} {Y = Y} ⦃ sb ⦄ =
      iso→extensional isom sb
        where
          -- Easier to just do this by hand.
          isom : Iso (↓Obj T (!Const Y)) (Σ[ X ∈ A .Ob ] (B .Hom (T .F₀ X) Y))
          isom .fst α = ↓Obj.dom α , ↓Obj.map α
          isom .snd .is-iso.from (Y , f) = ↓obj f
          isom .snd .is-iso.rinv _ = refl
          isom .snd .is-iso.linv _ = ↓Obj-path T (!Const Y) refl refl refl
```
-->
