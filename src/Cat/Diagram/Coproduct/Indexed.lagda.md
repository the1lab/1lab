```agda
open import Cat.Instances.Shape.Terminal
open import Cat.Diagram.Colimit.Base
open import Cat.Instances.Discrete
open import Cat.Diagram.Pullback
open import Cat.Functor.Kan.Base
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

  hom-iso : ∀ {Y} → C.Hom S Y ≃ (∀ i → C.Hom (F i) Y)
  hom-iso = (λ z i → z C.∘ ι i) , is-iso→is-equiv λ where
    .is-iso.inv → match
    .is-iso.rinv x → funext λ i → commute
    .is-iso.linv x → sym (unique _ λ _ → refl)
```

A category $\cC$ **admits indexed coproducts** (of level $\ell$) if,
for any type $I : \ty\ \ell$ and family $F : I \to \cC$, there is an
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
  open _=>_

  Inj→Cocone : ∀ {x} → (∀ i → C.Hom (F i) x)
             → Disc-adjunct {C = C} {iss = i-is-grpd} F => Const x
  Inj→Cocone inj .η i = inj i
  Inj→Cocone inj .is-natural i j p =
    J (λ j p → inj j C.∘ subst (C.Hom (F i) ⊙ F) p C.id ≡ C.id C.∘ inj i)
      (C.elimr (transport-refl C.id) ∙ sym (C.idl _)) p

  is-indexed-coproduct→is-colimit
    : ∀ {x} {inj : ∀ i → C.Hom (F i) x}
    → is-indexed-coproduct F inj
    → is-colimit (Disc-adjunct F) x (Inj→Cocone inj)
  is-indexed-coproduct→is-colimit {x = x} {inj} ic =
    to-is-colimitp mc refl
    where
      module ic = is-indexed-coproduct ic
      open make-is-colimit

      mc : make-is-colimit (Disc-adjunct F) x
      mc .ψ i = inj i
      mc .commutes {i} {j} p =
        J (λ j p → inj j C.∘ subst (C.Hom (F i) ⊙ F) p C.id ≡ inj i)
          (C.elimr (transport-refl C.id))
          p
      mc .universal eta p = ic.match eta
      mc .factors eta p = ic.commute
      mc .unique eta p other q = ic.unique eta q

  is-colimit→is-indexed-coprduct
    : ∀ {K : Functor ⊤Cat C}
    → {eps : Disc-adjunct {iss = i-is-grpd} F => K F∘ !F}
    → is-lan !F (Disc-adjunct F) K eps
    → is-indexed-coproduct F (eps .η)
  is-colimit→is-indexed-coprduct {K = K} {eps} colim = ic where
    module colim = is-colimit colim
    open is-indexed-coproduct

    ic : is-indexed-coproduct F (eps .η)
    ic .match k =
      colim.universal k
        (J (λ j p → k j C.∘ subst (C.Hom (F _) ⊙ F) p C.id ≡ k _)
           (C.elimr (transport-refl _)))
    ic .commute =
      colim.factors _ _
    ic .unique k comm =
      colim.unique _ _ _ comm

  IC→Colimit
    : Indexed-coproduct F
    → Colimit {C = C} (Disc-adjunct {iss = i-is-grpd} F)
  IC→Colimit ic =
    to-colimit (is-indexed-coproduct→is-colimit has-is-ic)
    where open Indexed-coproduct ic

  Colimit→IC
    : Colimit {C = C} (Disc-adjunct {iss = i-is-grpd} F)
    → Indexed-coproduct F
  Colimit→IC colim .Indexed-coproduct.ΣF = _
  Colimit→IC colim .Indexed-coproduct.ι = _
  Colimit→IC colim .Indexed-coproduct.has-is-ic =
    is-colimit→is-indexed-coprduct (Colimit.has-colimit colim)
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
      : ∀ i j → ¬ i ≡ j → is-initial C (summands-intersect i j .Pullback.apex)
```

## Initial objects are disjoint

We prove that if $\bot$ is an initial object, then it is also an indexed
coproduct --- for any family $\bot \to \cC$ --- and furthermore, it
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
