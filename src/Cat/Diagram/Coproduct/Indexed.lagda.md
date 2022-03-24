```agda
open import Cat.Diagram.Colimit.Base
open import Cat.Instances.Discrete
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
    colim .has⊥ x .centre .commutes = IC.commute
    colim .has⊥ x .paths h = Cocone-hom-path _ (sym (IC.unique _ λ i → h .commutes))

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

  Coimit→IC : Colimit {C = C} F → Indexed-coproduct F.₀
  Coimit→IC colim = the-ic where
    module colim = Cocone (colim .bot)

    the-ic : Indexed-coproduct _
    the-ic .ΣF = colim.coapex
    the-ic .ι  = colim.ψ
    the-ic .has-is-ic .match f = colim .has⊥ (Inj→Cocone f) .centre .hom
    the-ic .has-is-ic .commute = colim .has⊥ _ .centre .commutes
    the-ic .has-is-ic .unique {h = h} f p i =
      colim .has⊥ (Inj→Cocone f) .paths h′ (~ i) .hom
      where
        h′ : Cocone-hom _ _ _
        h′ .hom = h
        h′ .commutes = p _
```
