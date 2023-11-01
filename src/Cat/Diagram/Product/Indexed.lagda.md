<!--
```agda
open import Cat.Instances.Shape.Terminal
open import Cat.Univalent
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

# Indexed products {defines="indexed-product"}

If a category admits a [[terminal object]] and [[binary
products|product]], then it admits products of any finite cardinality:
iterate the binary product, and use the terminal object when there
aren't any objects. However, these two classes of limit do not let us
speak of products of arbitrary cardinality, or, in the univalent
context, indexed by types which are not sets.

That's where $I$-indexed products come in: Rather than having a
_functor_ giving the objects to take the limit over, we have an
arbitrary map $F$ from $I$ to the space of objects of $\cC$. An _indexed
product_ for this "diagram" is then an object admitting an universal
family of maps $\pi_i : (\prod F) \to F_i$.

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

  unique₂ : ∀ {Y} {g h : C.Hom Y P} → (∀ i → π i C.∘ g ≡ π i C.∘ h) → g ≡ h
  unique₂ {g = g} {h} eq = eta g ∙ ap tuple (funext eq) ∙ sym (eta h)

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

has-products-indexed-by : ∀ {ℓ} (I : Type ℓ) → Type _
has-products-indexed-by I = ∀ (F : I → C.Ob) → Indexed-product F

has-indexed-products : ∀ ℓ → Type _
has-indexed-products ℓ = ∀ {I : Type ℓ} → has-products-indexed-by I
```

<!--
```agda
module _ {ℓ'} {I : Type ℓ'} (F : I → C .Precategory.Ob) (ip : Indexed-product F) where
  private module ip = Indexed-product ip

  tuple∘ : ∀ {A B} (f : ∀ i → C.Hom B (F i))
          {g : C.Hom A B}
        → ip.tuple f C.∘ g ≡ ip.tuple λ i → f i C.∘ g
  tuple∘ f = ip.unique _ λ i → C.pulll ip.commute

Indexed-product-≃
  : ∀ {ℓ ℓ'} {I : Type ℓ} {J : Type ℓ'} → (e : I ≃ J)
  → {F : I → C.Ob} → Indexed-product (F ⊙ Equiv.from e) → Indexed-product F
Indexed-product-≃ e {F} p = λ where
  .ΠF → p .ΠF
  .π j → C.to (path→iso (ap F (e.η _))) C.∘ p .π (e.to j)
  .has-is-ip .tuple f → p .tuple (f ⊙ e.from)
  .has-is-ip .commute {f = f} →
    C.pullr (p .commute) ∙ from-pathp-to C _ (ap f (e.η _))
  .has-is-ip .unique f comm → p .unique _ λ j →
      ap (C._∘ _) (sym (from-pathp-to C _ (ap (p .π) (e.ε j)))
                  ∙ ap (λ z → C.to (path→iso (ap F z)) C.∘ p .π _) (e.zag j))
    ∙ comm (e.from j)
    where
      open Indexed-product
      open is-indexed-product
      module e = Equiv e

Lift-Indexed-product
  : ∀ {ℓ} ℓ' → {I : Type ℓ} → {F : I → C.Ob}
  → Indexed-product {Idx = Lift ℓ' I} (F ⊙ Lift.lower)
  → Indexed-product F
Lift-Indexed-product _ = Indexed-product-≃ (Lift-≃ e⁻¹)
```
-->

## Uniqueness

As is traditional with universal constructions, "having an indexed
product for a diagram" is _property_ of a category, not structure: Put
another way, for any particular diagram, in a univalent category, there
is (at most) a contractible space of indexed products of that diagram.
And again as is traditional with universal constructions, the proof is
surprisingly straightforward!

```agda
Indexed-product-unique
  : ∀ {ℓ'} {I : Type ℓ'} (F : I → C.Ob)
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

    pres' : ∀ {Y} (f : ∀ j → C.Hom Y (F j))
      → PathP (λ i → C.Hom Y (c-cat .to-path apices i)) (x.tuple f) (y.tuple f)
    pres' f =
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
  p i .has-is-ip .tuple f = pres' f i
  p i .has-is-ip .commute {i = j} {f = f} =
    is-prop→pathp (λ i → C.Hom-set _ (F j) (pres j i C.∘ pres' f i) _)
     (x .has-is-ip .commute) (y .has-is-ip .commute) i
  p i .has-is-ip .unique {h = h} f =
    is-prop→pathp
      (λ i → Π-is-hlevel {A = C.Hom _ (c-cat .to-path apices i)} 1
       λ h → Π-is-hlevel {A = ∀ j → pres j i C.∘ h ≡ f j} 1
       λ p → C.Hom-set _ (c-cat .to-path apices i) h (pres' f i))
      (λ h → x.unique {h = h} f) (λ h → y.unique {h = h} f) i h
```

We can also prove the converse direction: if indexed products in $\cC$ are unique,
then $\cC$ is univalent. In fact, we only need limits of one-object diagrams to be
unique.

```agda
unique-products→is-category
  : ({x : C.Ob} → is-prop (Indexed-product {Idx = ⊤} (λ _ → x)))
  → is-category C
unique-products→is-category prop = cat where
```

Given an isomorphism $a \cong b$, we build two products for the one-object diagram $a$:
one with apex $a$ itself and identity as projection, and one with apex $b$ and the
given isomorphism as projection.

```agda
  module _ {a b : C.Ob} (is : a C.≅ b) where
    open Indexed-product
    open is-indexed-product

    Pa : Indexed-product {Idx = ⊤} (λ _ → a)
    Pa .ΠF = a
    Pa .π _ = C.id
    Pa .has-is-ip .tuple f = f _
    Pa .has-is-ip .commute = C.idl _
    Pa .has-is-ip .unique f p = sym (C.idl _) ∙ p _

    Pb : Indexed-product {Idx = ⊤} (λ _ → a)
    Pb .ΠF = b
    Pb .π _ = is .C.from
    Pb .has-is-ip .tuple f = is .C.to C.∘ f _
    Pb .has-is-ip .commute = C.cancell (is .C.invr)
    Pb .has-is-ip .unique f p = sym (C.lswizzle (sym (p _)) (is .C.invl))
```

By uniqueness, the two products are equal, which gives us an equality $a \equiv b$
lying over our isomorphism.

```agda
    path : a ≡ b
    path = ap ΠF (prop Pa Pb)

    path-over : PathP (λ i → a C.≅ path i) C.id-iso is
    path-over = C.≅-pathp-from _ _ (ap (λ p → p .π _) (prop Pa Pb))

  cat : is-category C
  cat .to-path = path
  cat .to-path-over = path-over
```
