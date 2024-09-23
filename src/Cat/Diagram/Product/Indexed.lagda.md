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
  → Indexed-product {Idx = Lift ℓ' I} (F ⊙ lower)
  → Indexed-product F
Lift-Indexed-product _ = Indexed-product-≃ (Lift-≃ e⁻¹)

is-indexed-product-is-prop
  : ∀ {ℓ'} {Idx : Type ℓ'}
  → {F : Idx → C.Ob} {ΠF : C.Ob} {π : ∀ idx → C.Hom ΠF (F idx)}
  → is-prop (is-indexed-product F π)
is-indexed-product-is-prop {Idx = Idx} {F = F} {ΠF = ΠF} {π = π} P Q = path where
  open is-indexed-product

  p : ∀ {X} → (f : (i : Idx) → C.Hom X (F i)) → P .tuple f ≡ Q .tuple f
  p f = Q .unique f (λ idx → P .commute)

  path : P ≡ Q
  path i .tuple f = p f i
  path i .commute {i = idx} {f = f} =
    is-prop→pathp (λ i → C.Hom-set _ _ (π idx C.∘ p f i) (f idx))
      (P .commute)
      (Q .commute) i
  path i .unique {h = h} f q =
      is-prop→pathp (λ i → C.Hom-set _ _ h (p f i))
        (P .unique f q)
        (Q .unique f q) i

module _ {ℓ'} {Idx : Type ℓ'} {F : Idx → C.Ob} {P P' : Indexed-product F} where
  private
    module P = Indexed-product P
    module P' = Indexed-product P'

  Indexed-product-path
    : (p : P.ΠF ≡ P'.ΠF)
    → (∀ idx → PathP (λ i → C.Hom (p i) (F idx)) (P.π idx) (P'.π idx))
    → P ≡ P'
  Indexed-product-path p q i .Indexed-product.ΠF = p i
  Indexed-product-path p q i .Indexed-product.π idx = q idx i
  Indexed-product-path p q i .Indexed-product.has-is-ip =
    is-prop→pathp (λ i → is-indexed-product-is-prop {ΠF = p i} {π = λ idx → q idx i})
      P.has-is-ip
      P'.has-is-ip i
```
-->

## Uniqueness

As is traditional with universal constructions, "having an indexed
product for a diagram" is _property_ of a category, not structure: Put
another way, for any particular diagram, in a univalent category, there
is (at most) a contractible space of indexed products of that diagram.
And again as is traditional with universal constructions, the proof is
surprisingly straightforward!

First, a general result: if two objects are both indexed products over the
same family of objects, then those objects are isomorphic. This isomorphism
is induced by the universal properties, and is readily seen to commute
with both projections:

```agda
is-indexed-product→iso
  : ∀ {ℓ'} {Idx : Type ℓ'} {F : Idx → C.Ob}
  → {ΠF ΠF' : C.Ob}
  → {π : ∀ i → C.Hom ΠF (F i)} {π' : ∀ i → C.Hom ΠF' (F i)}
  → is-indexed-product F π
  → is-indexed-product F π'
  → ΠF C.≅ ΠF'
is-indexed-product→iso {π = π} {π' = π'} ΠF-prod ΠF'-prod =
  C.make-iso (ΠF'.tuple π) (ΠF.tuple π')
    (ΠF'.unique₂ (λ i → C.pulll ΠF'.commute ∙ ΠF.commute ∙ sym (C.idr _)))
    (ΠF.unique₂ λ i → C.pulll ΠF.commute ∙ ΠF'.commute ∙ sym (C.idr _))
  where
    module ΠF = is-indexed-product ΠF-prod
    module ΠF' = is-indexed-product ΠF'-prod

```

<!--
```agda
Indexed-product→iso
  : ∀ {ℓ'} {Idx : Type ℓ'} {F : Idx → C.Ob}
  → (P P' : Indexed-product F)
  → Indexed-product.ΠF P C.≅ Indexed-product.ΠF P'
Indexed-product→iso P P' =
  is-indexed-product→iso
    (Indexed-product.has-is-ip P)
    (Indexed-product.has-is-ip P')
```
-->

With that out of the way, we can proceed to show our original result!
First, note that paths between indexed products are determined by a
path between apices, and a corresponding path-over between projections.
We can upgrade the iso from our previous lemma into a path, so all that
remains is to construct the path-over.

```agda
Indexed-product-unique
  : ∀ {ℓ'} {I : Type ℓ'} (F : I → C.Ob)
  → is-category C → is-prop (Indexed-product F)
Indexed-product-unique {I = I} F c-cat x y =
  Indexed-product-path
    (c-cat .to-path apices)
    pres
  where
    module x = Indexed-product x
    module y = Indexed-product y

    apices : x.ΠF C.≅ y.ΠF
    apices = Indexed-product→iso x y
```

By the characterisation of paths-over in Hom-sets, we get paths-over
between the projection maps and the product maps:

```agda
    module apices = C._≅_ apices
    abstract
      pres : ∀ j → PathP (λ i → C.Hom (c-cat .to-path apices i) (F j)) (x.π j) (y.π j)
      pres j = Univalent.Hom-pathp-refll-iso c-cat x.commute
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

## Properties

Let $X : \Sigma A B \to \cC$ be a family of objects in $\cC$. If the
the indexed products $\Pi_{a, b : \Sigma A B} X_{a,b}$ and
$\Pi_{a : A} \Pi_{b : B(a)} X_{a, b}$ exists, then they are isomorphic.

```agda
is-indexed-product-assoc
  : ∀ {κ κ'} {A : Type κ} {B : A → Type κ'}
  → {X : Σ A B → C.Ob}
  → {ΠᵃᵇX : C.Ob} {ΠᵃΠᵇX : C.Ob} {ΠᵇX : A → C.Ob}
  → {πᵃᵇ : (ab : Σ A B) → C.Hom ΠᵃᵇX (X ab)}
  → {πᵃ : ∀ a → C.Hom ΠᵃΠᵇX (ΠᵇX a)}
  → {πᵇ : ∀ a → (b : B a) → C.Hom (ΠᵇX a) (X (a , b))}
  → is-indexed-product X πᵃᵇ
  → is-indexed-product ΠᵇX πᵃ
  → (∀ a → is-indexed-product (λ b → X (a , b)) (πᵇ a))
  → ΠᵃᵇX C.≅ ΠᵃΠᵇX
```

The proof is surprisingly straightforward: as indexed products are
unique up to iso, it suffices to show that $\Pi_{a : A} \Pi_{b : B(a)} X_{a, b}$
is an indexed product over $X$.

```agda
is-indexed-product-assoc {A = A} {B} {X} {ΠᵃΠᵇX = ΠᵃΠᵇX} {πᵃ = πᵃ} {πᵇ} Πᵃᵇ ΠᵃΠᵇ Πᵇ =
  is-indexed-product→iso Πᵃᵇ Πᵃᵇ'
  where
    open is-indexed-product
```

We can construct projections by composing the projections out of each
successive product.

```agda
    πᵃᵇ' : ∀ (ab : Σ A B) → C.Hom ΠᵃΠᵇX (X ab)
    πᵃᵇ' (a , b) = πᵇ a b C.∘ πᵃ a
```

The rest of the structure follows a similar pattern.

```agda
    Πᵃᵇ' : is-indexed-product X πᵃᵇ'
    Πᵃᵇ' .tuple f = ΠᵃΠᵇ .tuple λ a → Πᵇ a .tuple λ b → f (a , b)
    Πᵃᵇ' .commute = C.pullr (ΠᵃΠᵇ .commute) ∙ Πᵇ _ .commute
    Πᵃᵇ' .unique {h = h} f p =
      ΠᵃΠᵇ .unique _ λ a →
      Πᵇ _ .unique _ λ b →
      C.assoc _ _ _ ∙ p (a , b)
```

# Categories with all indexed products

```agda
has-products-indexed-by : ∀ {ℓ} (I : Type ℓ) → Type _
has-products-indexed-by I = ∀ (F : I → C.Ob) → Indexed-product F

has-indexed-products : ∀ ℓ → Type _
has-indexed-products ℓ = ∀ {I : Type ℓ} → has-products-indexed-by I

module Indexed-products
  {κ : Level}
  (has-ip : has-indexed-products κ)
  where
  module ∏ {Idx : Type κ} (F : Idx → C.Ob) = Indexed-product (has-ip F)

  open ∏ renaming (commute to π-commute; unique to tuple-unique) public
```
