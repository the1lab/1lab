<!--
```agda
open import Cat.Instances.Shape.Terminal
open import Cat.Diagram.Limit.Base
open import Cat.Instances.Discrete
open import Cat.Functor.Kan.Base
open import Cat.Prelude
```
-->

```agda
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

```agda
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
a functor $\rm{Disc}{I} \to \cC$. We can not lift this restriction: If
$I$ is not a groupoid, then its path spaces $x = y$ are not necessarily
sets, and so the `Disc`{.Agda} construction does not apply to it.

```agda
module _ {I : Type ℓ'} (i-is-grpd : is-groupoid I) (F : I → C.Ob) where
  open _=>_

  Proj→Cone : ∀ {x} → (∀ i → C.Hom x (F i))
            → Const x => Disc-adjunct {C = C} {iss = i-is-grpd} F
  Proj→Cone π .η i = π i
  Proj→Cone π .is-natural i j p =
    J (λ j p →  π j C.∘ C.id ≡ subst (C.Hom (F i) ⊙ F) p C.id C.∘ π i)
      (C.idr _ ∙ C.introl (transport-refl C.id))
      p

  is-indexed-product→is-limit
    : ∀ {x} {π : ∀ i → C.Hom x (F i)}
    → is-indexed-product F π
    → is-limit (Disc-adjunct F) x (Proj→Cone π)
  is-indexed-product→is-limit {x = x} {π} ip =
    to-is-limitp ml refl
    where
      module ip = is-indexed-product ip
      open make-is-limit

      ml : make-is-limit (Disc-adjunct F) x
      ml .ψ j = π j
      ml .commutes {i} {j} p =
        J (λ j p → subst (C.Hom (F i) ⊙ F) p C.id C.∘ π i ≡ π j)
          (C.eliml (transport-refl _))
          p
      ml .universal eta p = ip.tuple eta
      ml .factors eta p = ip.commute
      ml .unique eta p other q = ip.unique eta q

  is-limit→is-indexed-product
    : ∀ {K : Functor ⊤Cat C}
    → {eta : K F∘ !F => Disc-adjunct {iss = i-is-grpd} F}
    → is-ran !F (Disc-adjunct F) K eta
    → is-indexed-product F (eta .η)
  is-limit→is-indexed-product {K = K} {eta} lim = ip where
    module lim = is-limit lim
    open is-indexed-product hiding (eta)

    ip : is-indexed-product F (eta .η)
    ip .tuple k =
      lim.universal k
        (J (λ j p → subst (C.Hom (F _) ⊙ F) p C.id C.∘ k _ ≡ k j)
           (C.eliml (transport-refl _)))
    ip .commute =
      lim.factors _ _
    ip .unique k comm =
      lim.unique _ _ _ comm

  IP→Limit : Indexed-product F → Limit {C = C} (Disc-adjunct {iss = i-is-grpd} F)
  IP→Limit ip =
    to-limit (is-indexed-product→is-limit has-is-ip)
    where open Indexed-product ip

  Limit→IP : Limit {C = C} (Disc-adjunct {iss = i-is-grpd} F) → Indexed-product F
  Limit→IP lim .Indexed-product.ΠF = _
  Limit→IP lim .Indexed-product.π = _
  Limit→IP lim .Indexed-product.has-is-ip =
    is-limit→is-indexed-product (Limit.has-limit lim)
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
