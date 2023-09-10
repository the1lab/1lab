<!--
```agda
open import Cat.Instances.Shape.Terminal
open import Cat.Diagram.Pullback
open import Cat.Diagram.Initial
open import Cat.Univalent
open import Cat.Prelude
```
-->

```agda
module Cat.Diagram.Coproduct.Indexed {o ℓ} (C : Precategory o ℓ) where
```

# Indexed coproducts {defines="indexed-coproduct"}

Indexed coproducts are the [dual] notion to [[indexed products]], so see
there for motivation and exposition.

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

```agda
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

  unique₂ : ∀ {Y} {g h : C.Hom S Y} → (∀ i → g C.∘ ι i ≡ h C.∘ ι i) → g ≡ h
  unique₂ {g = g} {h} eq = eta g ∙ ap match (funext eq) ∙ sym (eta h)

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

has-coproducts-indexed-by : ∀ {ℓ} (I : Type ℓ) → Type _
has-coproducts-indexed-by I = ∀ (F : I → C.Ob) → Indexed-coproduct F

has-indexed-coproducts : ∀ ℓ → Type _
has-indexed-coproducts ℓ = ∀ {I : Type ℓ} → has-coproducts-indexed-by I
```

<!--
```agda
Indexed-coproduct-≃
  : ∀ {ℓ ℓ'} {I : Type ℓ} {J : Type ℓ'} → (e : I ≃ J)
  → {F : I → C.Ob} → Indexed-coproduct (F ⊙ Equiv.from e) → Indexed-coproduct F
Indexed-coproduct-≃ e {F} p = λ where
  .ΣF → p .ΣF
  .ι j → p .ι (e.to j) C.∘ C.from (path→iso (ap F (e.η _)))
  .has-is-ic .match f → p .match (f ⊙ e.from)
  .has-is-ic .commute {f = f} →
    C.pulll (p .commute) ∙ from-pathp-to (C ^op) _ (ap f (e.η _))
  .has-is-ic .unique f comm → p .unique _ λ j →
      ap (_ C.∘_) (sym (from-pathp-to (C ^op) _ (ap (p .ι) (e.ε j)))
                  ∙ ap (λ z → p .ι _ C.∘ C.from (path→iso (ap F z))) (e.zag j))
    ∙ comm (e.from j)
    where
      open Indexed-coproduct
      open is-indexed-coproduct
      module e = Equiv e

Lift-Indexed-coproduct
  : ∀ {ℓ} ℓ' → {I : Type ℓ} → {F : I → C.Ob}
  → Indexed-coproduct {Idx = Lift ℓ' I} (F ⊙ Lift.lower)
  → Indexed-coproduct F
Lift-Indexed-coproduct _ = Indexed-coproduct-≃ (Lift-≃ e⁻¹)
```
-->

# Disjoint coproducts

An indexed coproduct $\sum F$ is said to be **disjoint** if every one of
its inclusions $F_i \to \sum F$ is [[monic]], and, for unequal $i \ne j$,
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
    has-is-ic            : is-indexed-coproduct F ι
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
  is-disjoint .has-is-ic = is-coprod
  is-disjoint .injections-are-monic i = absurd i
  is-disjoint .summands-intersect i j = absurd i
  is-disjoint .different-images-are-disjoint i j p = absurd i
```
