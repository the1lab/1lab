```agda
open import Cat.Diagram.Limit.Base
open import Cat.Instances.Discrete
open import Cat.Diagram.Terminal
open import Cat.Prelude

module Cat.Diagram.Product.Indexed {o ℓ} (C : Precategory o ℓ) where
```

<!--
```agda
import Cat.Reasoning C as C
private variable
  o' ℓ' : Level
  Idx : Type ℓ'
  A B P : C.Ob
```
-->

# Indexed products

If a category admits a [terminal object] and [binary products], then it
admits products of any finite cardinality: iterate the binary product,
and use the terminal object when there aren't any objects. However,
these two classes of limit do not let us speak of products of arbitrary
cardinality, or, in the univalent context, indexed by types which are
not sets.

[terminal object]: Cat.Diagram.Terminal.html
[binary products]: Cat.Diagram.Product.html

That's where $I$-indexed products come in: Rather than having a
_functor_ giving the objects to take the limit over, we have an
arbitrary map $F$ from $I$ to the space of objects of $\cC$. An
_indexed product_ for this "diagram" is then an object admitting an
universal family of maps $\pi_i : (\prod F) \to F_i$.

```
record is-indexed-product (F : Idx → C.Ob) (π : ∀ i → C.Hom P (F i))
  : Type (o ⊔ ℓ ⊔ level-of Idx) where
  no-eta-equality
  field
    tuple   : ∀ {Y} → (∀ i → C.Hom Y (F i)) → C.Hom Y P
    commute : ∀ {i} {Y} {f : ∀ i → C.Hom Y (F i)} → π i C.∘ tuple f ≡ f i
    unique  : ∀ {Y} {h : C.Hom Y P} (f : ∀ i → C.Hom Y (F i))
            → (∀ i → π i C.∘ h ≡ f i)
            → h ≡ tuple f

  eta : ∀ {Y} (h : C.Hom Y P) → h ≡ tuple λ i → π i C.∘ h
  eta h = unique _ λ _ → refl

  hom-iso : ∀ {Y} → C.Hom Y P ≃ (∀ i → C.Hom Y (F i))
  hom-iso = (λ f i → π i C.∘ f) , is-iso→is-equiv λ where
    .is-iso.inv → tuple
    .is-iso.rinv x → funext λ i → commute
    .is-iso.linv x → sym (unique _ λ _ → refl)
```

A category $\cC$ **admits indexed products** (of level $\ell$) if,
for any type $I : \ty\ \ell$ and family $F : I \to \cC$, there is an
indexed product of $F$.

```agda
record Indexed-product (F : Idx → C.Ob) : Type (o ⊔ ℓ ⊔ level-of Idx) where
  no-eta-equality
  field
    {ΠF}      : C.Ob
    π         : ∀ i → C.Hom ΠF (F i)
    has-is-ip : is-indexed-product F π
  open is-indexed-product has-is-ip public

has-indexed-products : ∀ ℓ → Type _
has-indexed-products ℓ = ∀ {I : Type ℓ} (F : I → C.Ob) → Indexed-product F
```

<!--
```agda
module _ {ℓ′} {I : Type ℓ′} (F : I → C .Precategory.Ob) (ip : Indexed-product F) where
  private module ip = Indexed-product ip

  tuple∘ : ∀ {A B} (f : ∀ i → C.Hom B (F i))
          {g : C.Hom A B}
        → ip.tuple f C.∘ g ≡ ip.tuple λ i → f i C.∘ g
  tuple∘ f = ip.unique _ λ i → C.pulll ip.commute
```
-->

## As limits

In the particular case where $I$ is a groupoid, e.g. because it arises
as the space of objects of a univalent category, an indexed product for
$F : I \to \cC$ is the same thing as a limit over $F$, considered as
a functor $\disc{I} \to \cC$. We can not lift this restriction: If
$I$ is not a groupoid, then its path spaces $x = y$ are not necessarily
sets, and so the `Disc`{.Agda} construction does not apply to it.

```agda
module _ {I : Type ℓ'} (i-is-grpd : is-groupoid I) (F : I → C.Ob) where
  open Cone-hom
  open Terminal
  open Cone

  IP→Limit : Indexed-product F → Limit {C = C} (Disc-adjunct {iss = i-is-grpd} F)
  IP→Limit IP = lim where
    module IP = Indexed-product IP

    thelim : Cone _
    thelim .apex = IP.ΠF
    thelim .ψ = IP.π
    thelim .commutes {x} =
      J (λ y p → subst (C.Hom (F x) ⊙ F) p C.id C.∘ (IP.π x) ≡ IP.π y)
        (C.eliml (transport-refl _))

    lim : Limit _
    lim .top = thelim
    lim .has⊤ x .centre .hom = IP.tuple (x .ψ)
    lim .has⊤ x .centre .commutes o = IP.commute
    lim .has⊤ x .paths h = Cone-hom-path _ (sym (IP.unique _ λ i → h .commutes _))

module _ {I : Type ℓ'} (isg : is-groupoid I) (F : Functor (Disc I isg) C) where
  private module F = Functor F
  open is-indexed-product
  open Indexed-product
  open Cone-hom
  open Terminal
  open Cone

  Proj→Cone : ∀ {Y} → (∀ i → C.Hom Y (F.₀ i)) → Cone F
  Proj→Cone f .apex = _
  Proj→Cone f .ψ = f
  Proj→Cone f .commutes {x} =
    J (λ y p → F.₁ p C.∘ f x ≡ f y) (C.eliml F.F-id)

  Limit→IP : Limit {C = C} F → Indexed-product F.₀
  Limit→IP lim = the-ip where
    module lim = Cone (lim .top)

    the-ip : Indexed-product _
    the-ip .ΠF = lim.apex
    the-ip .π = lim.ψ
    the-ip .has-is-ip .tuple f = lim .has⊤ (Proj→Cone f) .centre .hom
    the-ip .has-is-ip .commute = lim .has⊤ (Proj→Cone _) .centre .commutes _
    the-ip .has-is-ip .unique {h = h} f p i =
      lim .has⊤ (Proj→Cone f) .paths other (~ i) .hom
      where
        other : Cone-hom _ _ _
        other .hom = h
        other .commutes i = p i
```

## Uniqueness

As is traditional with universal constructions, "having an indexed
product for a diagram" is _property_ of a category, not structure: Put
another way, for any particular diagram, in a univalent category, there
is (at most) a contractible space of indexed products of that diagram.
And again as is traditional with universal constructions, the proof is
surprisingly straightforward!

```agda
Indexed-product-unique
  : ∀ {ℓ′} {I : Type ℓ′} (F : I → C.Ob)
  → is-category C → is-prop (Indexed-product F)
Indexed-product-unique {I = I} F c-cat x y = p where
  module x = Indexed-product x
  module y = Indexed-product y
```

All we have to do --- "all" --- is exhibit an isomorphism between the
apices which commutes with the projection function in one direction, and
with the product with morphisms in the other. That's it! The isomorphism
is induced by the universal properties, and is readily seen to commute
with both projections:

```agda
  apices : x.ΠF C.≅ y.ΠF
  apices = C.make-iso (y.tuple x.π) (x.tuple y.π)
    ( y.unique y.π (λ i → C.pulll y.commute ∙ x.commute)
    ∙ sym (y.unique y.π λ i → C.idr _) )
    ( x.unique x.π (λ i → C.pulll x.commute ∙ y.commute)
    ∙ sym (x.unique x.π λ i → C.idr _))
```

By the characterisation of paths-over in Hom-sets, we get paths-over
between the projection maps and the product maps:

```agda
  module apices = C._≅_ apices
  abstract
    pres : ∀ j → PathP (λ i → C.Hom (c-cat .to-path apices i) (F j)) (x.π j) (y.π j)
    pres j = Univalent.Hom-pathp-refll-iso c-cat x.commute

    pres′ : ∀ {Y} (f : ∀ j → C.Hom Y (F j))
      → PathP (λ i → C.Hom Y (c-cat .to-path apices i)) (x.tuple f) (y.tuple f)
    pres′ f =
      Univalent.Hom-pathp-reflr-iso c-cat (y.unique f λ j → C.pulll y.commute ∙ x.commute)
```

And after some munging (dealing with the axioms), that's exactly what we
need to prove that indexed products are unique.

```agda
  open Indexed-product
  open is-indexed-product
  p : x ≡ y
  p i .ΠF = c-cat .to-path apices i
  p i .π j = pres j i
  p i .has-is-ip .tuple f = pres′ f i
  p i .has-is-ip .commute {i = j} {f = f} =
    is-prop→pathp (λ i → C.Hom-set _ (F j) (pres j i C.∘ pres′ f i) _)
     (x .has-is-ip .commute) (y .has-is-ip .commute) i
  p i .has-is-ip .unique {h = h} f =
    is-prop→pathp
      (λ i → Π-is-hlevel {A = C.Hom _ (c-cat .to-path apices i)} 1
       λ h → Π-is-hlevel {A = ∀ j → pres j i C.∘ h ≡ f j} 1
       λ p → C.Hom-set _ (c-cat .to-path apices i) h (pres′ f i))
      (λ h → x.unique {h = h} f) (λ h → y.unique {h = h} f) i h
```
