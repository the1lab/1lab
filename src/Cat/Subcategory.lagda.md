```agda
module Cat.Subcategory where

open import Cat.Displayed.Base
open import Cat.Displayed.Total
open import Cat.Displayed.Univalence
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Reasoning
```

# Subcategories

Naïvely, a subcategory of a category $\ca{B}$ consists of a subset
of objects, and a subset of morphisms between those objects that is
closed under identity and composition. However, this definition is naïve
for a reason: it's not invariant under equivalence of categories!
The traditional approach repairing the definition is to try and
generalize the situation with subobjects, and to work with the
embeddings of subcategories instead of the foundational goop that
underlies them, but this is not the route we shall take.

Instead, we can take a step back and think of subcategories as
_structure imposed upon a category_. This immediately leads us to the
theory of [displayed categories], which provides the perfect setting to
study stuctures over categories in type theory. Concretely, we shall
say some displayed category $\ca{E}$ is a subcategory of $\ca{B}$ if
both the object and hom spaces of $\ca{E}$ are propositions.
Intuitively, the to think about this is that the structure we
are imposing over $\ca{B}$ is "is this object/hom in the subcategory",
instead of some more proof-relevant notion of structure.

[displayed categories]: Cat.Displayed.Base.html

```agda
record is-subcategory {o ℓ o′ ℓ′} {B : Precategory o ℓ} (E : Displayed B o′ ℓ′) :
  Type (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) where

  open Displayed E

  field
    Ob[_]-prop : ∀ X → is-prop Ob[ X ]
    Hom[_]-prop : ∀ {X Y} f (X′ : Ob[ X ]) (Y′ : Ob[ Y ]) → is-prop (Hom[ f ] X′ Y′)
```

As per usual, we define a bundled notion of subcategory as well as the
predicate.

```agda
record Subcategory {o ℓ} (B : Precategory o ℓ) (o′ ℓ′ : Level) :
  Type (o ⊔ ℓ ⊔ lsuc o′ ⊔ lsuc ℓ′) where
  field
    Subcat : Displayed B o′ ℓ′
    has-is-subcategory : is-subcategory Subcat

  open is-subcategory has-is-subcategory public
```

## Subcategories are Univalent

One interesting fact is that subcategories $\ca{E}$ of $\ca{B}$
are _always_ univalent displayed categories, _regardless of whether or
not the base category is univalent_. To see this, recall that a displayed
category is univalent iff the for all `A : Ob[ X ]`, the space of
displayed isomorphisms `Σ[ B ∈ Ob[ Y ] ] (A ≅[ f ] B)` is contractible.
However, because all of the objects and homs in $\ca{E}$ are props,
this follows directly from the fact that we can only ever have a single
isomorphism between objects, due to the uniqueness of homs.

```agda
module _ {o ℓ o′ ℓ′} {B : Precategory o ℓ} {E : Displayed B o′ ℓ′}
         (is-subcat : is-subcategory E) where

  open Cat.Reasoning B
  open Displayed E
  open is-subcategory is-subcat

  subcategory-is-category : is-category-displayed E
  subcategory-is-category x≅y X′ =
    Σ-is-hlevel 1
      Ob[ _ ]-prop 
      (λ _ _ _ →
        ≅[]-path E
          ((Hom[ _ ]-prop _ _) _ _)
          ((Hom[ _ ]-prop _ _) _ _))
```

## Faithfulness of the Projection Functor

Given a subcategory $E$ of $B$, the projection functor `πᶠ`{.Agda} from the total
category is faithful. This follows rather directly from the characterization of
path spaces in the total category: these consist of paths between the base homs,
along with a `PathP`{.Agda} over the displayed homs. We have the first path by
our hypotheses, and the `PathP` is trivial, as the space of homs is a proposition.

```agda
module _ {o ℓ o′ ℓ′} {B : Precategory o ℓ} {E : Displayed B o′ ℓ′}
  (is-subcat : is-subcategory E) where
    
  open Cat.Reasoning B
  open is-subcategory is-subcat
  open Total-hom

  πᶠ-subcategory-faithful : is-faithful (πᶠ E)
  πᶠ-subcategory-faithful p =
    total-hom-path E p (is-prop→pathp (λ _ → Hom[ _ ]-prop _ _) _ _)
```


## Constructing Subcategories

Our definition of a subcategory has many things going for it.
It's concise, uses existing theory, is easily extensible, and generally
follows the principle of the rising sea. However, there is one glaring
drawback: constructing one involves a lot of busywork! To work around
this, we define an API for constructing subcategories from the datum
that is normally used to define them.

```agda
record make-subcategory {o ℓ} (B : Precategory o ℓ) (o′ ℓ′ : Level) :
  Type (o ⊔ ℓ ⊔ lsuc o′ ⊔ lsuc ℓ′) where
  open Precategory B
  field
    Ob? : Ob → Prop o′
    Hom? : ∀ {X Y} → Hom X Y → ∣ Ob? X ∣ → ∣ Ob? Y ∣ → Prop ℓ′
    hom?-id : ∀ {X} → (PX : ∣ Ob? X ∣) → ∣ Hom? id PX PX ∣
    hom?-∘  : ∀ {X Y Z f g}
              → (PX : ∣ Ob? X ∣) → (PY : ∣ Ob? Y ∣) → (PZ : ∣ Ob? Z ∣)
              → ∣ Hom? f PY PZ ∣ → ∣ Hom? g PX PY ∣ → ∣ Hom? (f ∘ g) PX PZ ∣ 

to-subcategory : ∀ {o ℓ o′ ℓ′} {B : Precategory o ℓ}
                 → make-subcategory B o′ ℓ′ → Subcategory B o′ ℓ′
to-subcategory mk-subcat = subcat
  where
    open make-subcategory mk-subcat
    open Subcategory
    open Displayed

    subcat : Subcategory _ _ _
    subcat .Subcat .Ob[_] X = ∣ Ob? X ∣
    subcat .Subcat .Hom[_] f PX PY = ∣ Hom? f PX PY ∣
    subcat .Subcat .Hom[_]-set f PX PY = is-prop→is-set (is-tr (Hom? f PX PY))
    subcat .Subcat .id′ = hom?-id _
    subcat .Subcat ._∘′_ f g = hom?-∘ _ _ _ f g
    subcat .Subcat .idr′ f = is-prop→pathp (λ _ → is-tr (Hom? _ _ _)) _ _
    subcat .Subcat .idl′ f = is-prop→pathp (λ _ → is-tr (Hom? _ _ _)) _ _
    subcat .Subcat .assoc′ f g h = is-prop→pathp (λ _ → is-tr (Hom? _ _ _)) _ _
    subcat .has-is-subcategory .is-subcategory.Ob[_]-prop _ = is-tr (Ob? _)
    subcat .has-is-subcategory .is-subcategory.Hom[_]-prop _ _ _ = is-tr (Hom? _ _ _)
```

# Wide Subcategories

We say a subcategory is wide if it contains "all of the objects,
but some of the morphisms". This can be elegantly expressed by refining the definition
of subcategory to require _contractible_ spaces of objects instead of propositional
spaces.

```agda
record is-wide-subcategory {o ℓ o′ ℓ′} {B : Precategory o ℓ} (E : Displayed B o′ ℓ′) :
  Type (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) where
  open Displayed E
  field
    Ob[_]-contr : ∀ X → is-contr Ob[ X ]
    Hom[_]-prop : ∀ {X Y} f (X′ : Ob[ X ]) (Y′ : Ob[ Y ]) → is-prop (Hom[ f ] X′ Y′)

  has-is-subcategory : is-subcategory E
  has-is-subcategory .is-subcategory.Ob[_]-prop X = is-contr→is-prop (Ob[_]-contr X)
  has-is-subcategory .is-subcategory.Hom[_]-prop = Hom[_]-prop
```

As in the case of subcategories, we bundle up the definition to make it less
annoying to work with in some cases.

```agda
record Wide-subcategory {o ℓ} (B : Precategory o ℓ) (o′ ℓ′ : Level) :
  Type (o ⊔ ℓ ⊔ lsuc o′ ⊔ lsuc ℓ′) where
  field
    Subcat : Displayed B o′ ℓ′
    has-is-wide-subcategory : is-wide-subcategory Subcat

  open is-wide-subcategory has-is-wide-subcategory public
```

## Essential Surjectivity of the Projection Functor.

If $E$ is a wide subcategory of $B$, then the projection functor `πᶠ`{.Agda}
from the total category of $E$ is _split_ essentially surjective.
The space of objects in $E$ is contractible, so we can always lift
$X : \ca{B}$ to the pair of $X$ and the unique $X' : Ob_{X}$  in the total category, which projects down to $X$
by `πᶠ`{.Agda}.

```agda
module _ {o ℓ o′ ℓ′} {B : Precategory o ℓ} {E : Displayed B o′ ℓ′}
  (is-wide-subcat : is-wide-subcategory E) where
    
  open Cat.Reasoning B
  open is-wide-subcategory is-wide-subcat
  open Total-hom

  πᶠ-wide-subcategory-split-eso : is-split-eso (πᶠ E)
  πᶠ-wide-subcategory-split-eso Y = ((Y , Ob[ Y ]-contr .centre) , id-iso)
```


## Constructing Wide Subcategories

We also provide an API for constructing wide subcategories from the normal
datum used to define them.

```agda
record make-wide-subcategory {o ℓ} (B : Precategory o ℓ) (ℓ′ : Level) :
  Type (o ⊔ ℓ ⊔ lsuc ℓ′) where
  open Precategory B
  field
    Hom? : ∀ {X Y} → Hom X Y → Prop ℓ′
    hom?-id : ∀ {X} → ∣ Hom? (id {X}) ∣
    hom?-∘  : ∀ {X Y Z} {f : Hom Y Z} {g : Hom X Y} → ∣ Hom? f ∣ → ∣ Hom? g ∣ → ∣ Hom? (f ∘ g) ∣ 

to-wide-subcategory : ∀ {o ℓ ℓ′} {B : Precategory o ℓ}
                      → make-wide-subcategory B ℓ′ → Wide-subcategory B lzero ℓ′
to-wide-subcategory mk-subcat = subcat
  where
    open make-wide-subcategory mk-subcat
    open Wide-subcategory
    open is-wide-subcategory
    open Displayed

    subcat : Wide-subcategory _ _ _
    Ob[ subcat .Subcat ] X = ⊤
    subcat .Subcat .Hom[_] f _ _ = ∣ Hom? f ∣
    subcat .Subcat .Hom[_]-set f _ _ = is-prop→is-set (is-tr (Hom? f))
    subcat .Subcat .id′ = hom?-id
    subcat .Subcat ._∘′_ = hom?-∘
    subcat .Subcat .idr′ _ = is-prop→pathp (λ _ → is-tr (Hom? _)) _ _
    subcat .Subcat .idl′ _ = is-prop→pathp (λ _ → is-tr (Hom? _)) _ _
    subcat .Subcat .assoc′ _ _ _ = is-prop→pathp (λ _ → is-tr (Hom? _)) _ _
    subcat .has-is-wide-subcategory .Ob[_]-contr _ = hlevel 0
    subcat .has-is-wide-subcategory .Hom[_]-prop _ _ _ = is-tr (Hom? _)
```

# Full Subcategories

Full subcategories are the cousins of wide subcategories: instead of
"all of the objects, some of the morphisms", we have "some of the objects, all of the
morphisms". We can encode this by requiring that the hom spaces be contractible.

```agda
record is-full-subcategory {o ℓ o′ ℓ′} {B : Precategory o ℓ} (E : Displayed B o′ ℓ′) :
  Type (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) where
  open Displayed E
  field
    Ob[_]-prop : ∀ X → is-prop Ob[ X ]
    Hom[_]-contr : ∀ {X Y} f (X′ : Ob[ X ]) (Y′ : Ob[ Y ]) → is-contr (Hom[ f ] X′ Y′)

  has-is-subcategory : is-subcategory E
  has-is-subcategory .is-subcategory.Ob[_]-prop = Ob[_]-prop
  has-is-subcategory .is-subcategory.Hom[_]-prop f PX PY = is-contr→is-prop (Hom[_]-contr f PX PY)
```

In our usual style, we provide both an unbunbled and bundled definition.

```agda
record Full-subcategory {o ℓ} (B : Precategory o ℓ) (o′ ℓ′ : Level) :
  Type (o ⊔ ℓ ⊔ lsuc o′ ⊔ lsuc ℓ′) where
  field
    Subcat : Displayed B o′ ℓ′
    has-is-full-subcategory : is-full-subcategory Subcat

  open is-full-subcategory has-is-full-subcategory public
```

## Constructing Full Subcategories

The datum used to construct a full category is exceptionally simple, as we don't
need to worry about closure conditions at all.

```agda
to-full-subcategory : ∀ {o ℓ o′} {B : Precategory o ℓ}
                      → (Precategory.Ob B → Prop o′)
                      → Full-subcategory B o′ lzero
to-full-subcategory Ob? = subcat
  where
    open Full-subcategory
    open is-full-subcategory
    open Displayed

    subcat : Full-subcategory _ _ _
    subcat .Subcat .Ob[_] X = ∣ Ob? X ∣
    subcat .Subcat .Hom[_] f PX PY = ⊤
    subcat .Subcat .Hom[_]-set _ _ _ = hlevel 2
    subcat .Subcat .id′ = tt
    subcat .Subcat ._∘′_ _ _ = tt
    subcat .Subcat .idr′ _ = refl
    subcat .Subcat .idl′ _ = refl
    subcat .Subcat .assoc′ _ _ _ = refl
    subcat .has-is-full-subcategory .Ob[_]-prop X = is-tr (Ob? X)
    subcat .has-is-full-subcategory .Hom[_]-contr _ _ _ = hlevel 0
```

## Full Inclusions, and Full Faithfulness of the Projection Functor

If $\ca{E}$ is a full subcategory of $\ca{B}$, then the projection functor
`πᶠ`{.Agda} from the total category of $\ca{E}$ to $\ca{B}$ is fully faithful.
To see this, consider some morphism $f$ in $\ca{B}$. We need to show that the space
of fibres of `πᶠ`{.Agda} at $f$ is contractible. To construct the centre of this
contraction, we can use contractibility of hom spaces in $\ca{E}$ to obtain a
morphism $f'$ in $\ca{E}$ that lives above $f$. This then gets us an element
$(f, f')$ of the total category, which obviously lives in the fibre of `πᶠ`{.Agda}
over $f$.

To show contractibility, we can ignore any homotopical content of the equivalence,
as all of the hom spaces are sets. This means that we need to show that $(f , f')$
is the only element of the fibre of `πᶠ` at `f`, which follows directly from
contractibility of hom spaces in $\ca{E}$.

```agda
module _ {o ℓ o′ ℓ′} {B : Precategory o ℓ} {E : Displayed B o′ ℓ′}
  (is-full-subcat : is-full-subcategory E) where

  open Precategory B
  open is-full-subcategory is-full-subcat
  open Total-hom

  πᶠ-full-subcategory-ff : is-ff (πᶠ E)
  πᶠ-full-subcategory-ff .is-eqv f .centre =
    total-hom f (Hom[ f ]-contr _ _ .centre) , refl
  πᶠ-full-subcategory-ff .is-eqv f .paths (pf , eq) =
    Σ-prop-path
      (λ _ → Hom-set _ _ _ _)
      (total-hom-path E
        (sym eq)
        (is-prop→pathp (λ _ → is-contr→is-prop (Hom[ _ ]-contr _ _)) _ _))
```

We can also go the other direction: given a fully faithful functor
$F : \ca{D} \to \ca{C}$, we can construct a full subcategory on $\ca{C}$
that consists of only those objects that are _essentially_ in the
image of $F$.

```agda
module _ {o ℓ o′ ℓ′} {C : Precategory o ℓ} {D : Precategory o′ ℓ′}
         {F : Functor D C} (ff : is-ff F) where

  private
    module D = Cat.Reasoning D
    module C = Cat.Reasoning C

    open Full-subcategory
    open is-full-subcategory
    open Functor F
    open Total-hom

  Essential-image : Full-subcategory C (ℓ ⊔ o′) lzero
  Essential-image =
    to-full-subcategory λ X → el! (∃[ Y ∈ D.Ob ] (F₀ Y C.≅ X))
```

Notably, the total category of this full subcategory is equivalent to
$\ca{D}$! To start, we first construct a functor from $\ca{D}$ to the
total category of the constructed full subcategory that takes objects in
$\ca{D}$ to their image in $\ca{C}$, and equips them with the identity
isomorphism.

```agda
  Embed-essential-image : Functor D (∫ (Essential-image .Subcat))
  Embed-essential-image .Functor.F₀ X = (F₀ X) , inc (X , C.id-iso)
  Embed-essential-image .Functor.F₁ f = total-hom (F₁ f) tt
  Embed-essential-image .Functor.F-id = total-hom-path _ F-id refl
  Embed-essential-image .Functor.F-∘ f g = total-hom-path _ (F-∘ f g) refl
```

To see that this functor is fully faithful, recall that if both
$F \circ G$  and $F$ are fully faithful, then so is $G$.
The action of morphisms of `πᶠ F∘ Embed-essential-image` is `F.F₁`{.Agda},
which is fully faithful by our hypotheses. `πᶠ`{.Agda} is fully faithful
when the displayed category is a full subcategory, which `Essential-image`{.Agda}
is, so we can conclude that `Embed-essential-image`{.Agda} is also fully faithful.

```agda
  Embed-essential-image-ff : is-ff Embed-essential-image
  Embed-essential-image-ff =
    ff-cancel-l (πᶠ _) Embed-essential-image
      ff
      (πᶠ-full-subcategory-ff (Essential-image .has-is-full-subcategory))
```

Furthermore, `Embed-essential-image`{.Agda} is essential surjective, as
`πᶠ`{.Agda} is fully faithful, and fully faithful functors are essential injective,
which allows us to lift the isomorphism in question.

```agda
  Embed-essential-image-eso : is-eso Embed-essential-image
  Embed-essential-image-eso yo = do
    (preimg , isom) ← yo .snd
    pure $ preimg , is-ff→essentially-injective (πᶠ _) πᶠ-ff isom
    where
      open C._≅_
      πᶠ-ff = πᶠ-full-subcategory-ff (Essential-image .has-is-full-subcategory)
```
