```agda
open import Cat.Diagram.Colimit.Base
open import Cat.Instances.Discrete
open import Cat.Diagram.Pullback
open import Cat.Diagram.Initial
open import Cat.Prelude

module Cat.Diagram.Coproduct.Indexed {o ℓ} (C : Precategory o ℓ) where
```

# Indexed coproducts

Indexed coproducts are the [dual] notion to [indexed products], so see
there for motivation and exposition.

[indexed products]: Cat.Diagram.Product.Indexed.html
[dual]: Cat.Base.html#opposites

<!--
```agda
import Cat.Reasoning C as C
private variable
  o' ℓ' : Level
  Idx : Type ℓ'
  A B S : C.Ob
```
-->

```
record is-indexed-coproduct (F : Idx → C.Ob) (ι : ∀ i → C.Hom (F i) S)
  : Type (o ⊔ ℓ ⊔ level-of Idx) where
  no-eta-equality
  field
    match   : ∀ {Y} → (∀ i → C.Hom (F i) Y) → C.Hom S Y
    commute : ∀ {i} {Y} {f : ∀ i → C.Hom (F i) Y} → match f C.∘ ι i ≡ f i
    unique  : ∀ {Y} {h : C.Hom S Y} (f : ∀ i → C.Hom (F i) Y)
            → (∀ i → h C.∘ ι i ≡ f i)
            → h ≡ match f

  eta : ∀ {Y} (h : C.Hom S Y) → h ≡ match (λ i → h C.∘ ι i)
  eta h = unique _ λ _ → refl
```

A category $\ca{C}$ **admits indexed coproducts** (of level $\ell$) if,
for any type $I : \ty\ \ell$ and family $F : I \to \ca{C}$, there is an
indexed coproduct of $F$.

```agda
record Indexed-coproduct (F : Idx → C.Ob) : Type (o ⊔ ℓ ⊔ level-of Idx) where
  no-eta-equality
  field
    {ΣF}      : C.Ob
    ι         : ∀ i → C.Hom (F i) ΣF
    has-is-ic : is-indexed-coproduct F ι
  open is-indexed-coproduct has-is-ic public

has-indexed-coproducts : ∀ ℓ → Type _
has-indexed-coproducts ℓ = ∀ {I : Type ℓ} (F : I → C.Ob) → Indexed-coproduct F
```

## As colimits

Similarly to the product case, when $I$ is a groupoid, indexed
coproducts correspond to discrete diagrams of shape $I$.

```agda
module _ {I : Type ℓ'} (i-is-grpd : is-groupoid I) (F : I → C.Ob) where
  open Cocone-hom
  open Initial
  open Cocone

  IC→Limit : Indexed-coproduct F → Colimit {C = C} (Disc-adjunct {iss = i-is-grpd} F)
  IC→Limit IC = colim where
    module IC = Indexed-coproduct IC

    thecolim : Cocone _
    thecolim .coapex = IC.ΣF
    thecolim .ψ = IC.ι
    thecolim .commutes {x} =
      J (λ y p → IC.ι y C.∘ subst (C.Hom (F x) ⊙ F) p C.id ≡ IC.ι x)
        (C.elimr (transport-refl _))

    colim : Colimit _
    colim .bot = thecolim
    colim .has⊥ x .centre .hom = IC.match (x .ψ)
    colim .has⊥ x .centre .commutes o = IC.commute
    colim .has⊥ x .paths h = Cocone-hom-path _ (sym (IC.unique _ λ i → h .commutes _))

module _ {I : Type ℓ'} (isg : is-groupoid I) (F : Functor (Disc I isg) C) where
  private module F = Functor F
  open is-indexed-coproduct
  open Indexed-coproduct
  open Cocone-hom
  open Initial
  open Cocone

  Inj→Cocone : ∀ {Y} → (∀ i → C.Hom (F.₀ i) Y) → Cocone F
  Inj→Cocone f .coapex = _
  Inj→Cocone f .ψ = f
  Inj→Cocone f .commutes {x} = J (λ y p → f y C.∘ F.₁ p ≡ f x) (C.elimr F.F-id)

  Colimit→IC : Colimit {C = C} F → Indexed-coproduct F.₀
  Colimit→IC colim = the-ic where
    module colim = Cocone (colim .bot)

    the-ic : Indexed-coproduct _
    the-ic .ΣF = colim.coapex
    the-ic .ι  = colim.ψ
    the-ic .has-is-ic .match f = colim .has⊥ (Inj→Cocone f) .centre .hom
    the-ic .has-is-ic .commute = colim .has⊥ _ .centre .commutes _
    the-ic .has-is-ic .unique {h = h} f p i =
      colim .has⊥ (Inj→Cocone f) .paths h′ (~ i) .hom
      where
        h′ : Cocone-hom _ _ _
        h′ .hom = h
        h′ .commutes o = p _
```

# Disjoint coproducts

An indexed coproduct $\sum F$ is said to be **disjoint** if every one of
its inclusions $F_i \to \sum F$ is [monic], and, for unequal $i \ne j$,
the square below is a pullback with initial apex. Since the maps $F_i
\to \sum F \ot F_j$ are monic, the pullback below computes the
_intersection_ of $F_i$ and $F_j$ as subobjects of $\sum F$, hence the
name _disjoint coproduct_: If $\bot$ is an initial object, then $F_i
\cap F_j = \emptyset$.

[monic]: Cat.Morphism.html#monos

~~~{.quiver}
\[\begin{tikzcd}
  \bot && {F_i} \\
  \\
  {F_j} && {\sum F}
  \arrow[from=1-1, to=1-3]
  \arrow[from=1-3, to=3-3]
  \arrow[from=3-1, to=3-3]
  \arrow[from=1-1, to=3-1]
\end{tikzcd}\]
~~~

```agda
record is-disjoint-coproduct (F : Idx → C.Ob) (ι : ∀ i → C.Hom (F i) S)
  : Type (o ⊔ ℓ ⊔ level-of Idx) where
  field
    is-coproduct         : is-indexed-coproduct F ι
    injections-are-monic : ∀ i → C.is-monic (ι i)
    summands-intersect   : ∀ i j → Pullback C (ι i) (ι j)
    different-images-are-disjoint
      : ∀ i j → (i ≡ j → ⊥) → is-initial C (summands-intersect i j .Pullback.apex)
```

## Initial objects are disjoint

We prove that if $\bot$ is an initial object, then it is also an indexed
coproduct --- for any family $\bot \to \ca{C}$ --- and furthermore, it
is a disjoint coproduct.

```agda
is-initial→is-disjoint-coproduct
  : ∀ {∅} {F : ⊥ → C.Ob} {i : ∀ i → C.Hom (F i) ∅}
  → is-initial C ∅
  → is-disjoint-coproduct F i
is-initial→is-disjoint-coproduct {F = F} {i = i} init = is-disjoint where
  open is-indexed-coproduct
  is-coprod : is-indexed-coproduct F i
  is-coprod .match _ = init _ .centre
  is-coprod .commute {i = i} = absurd i
  is-coprod .unique {h = h} f p i = init _ .paths h (~ i)

  open is-disjoint-coproduct
  is-disjoint : is-disjoint-coproduct F i
  is-disjoint .is-coproduct = is-coprod
  is-disjoint .injections-are-monic i = absurd i
  is-disjoint .summands-intersect i j = absurd i
  is-disjoint .different-images-are-disjoint i j p = absurd i
```
