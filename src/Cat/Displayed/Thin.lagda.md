<!--
```agda
open import 1Lab.Function.Embedding

open import Cat.Displayed.Univalence
open import Cat.Functor.Properties
open import Cat.Displayed.Total
open import Cat.Displayed.Base
open import Cat.Instances.Sets
open import Cat.Prelude

import Cat.Displayed.Reasoning as Dr
import Cat.Displayed.Morphism as Dm
import Cat.Morphism as Cm
```
-->

```agda
module Cat.Displayed.Thin where
```

# Thinly displayed categories {defines="thinly-displayed-category"}

<!--
```agda
private variable
  o o' h h' : Level

module _ {B : Precategory o h} (E : Displayed B o' h') where

  private module B = Precategory B
  open Dr E
```
-->

We say a displayed category $\cE$ over $\cB$ is **thinly displayed** if
the type of morphisms lying over any $f : A \to B$ in $\cB$ is a mere
[[proposition]].

```agda
  is-thinly-displayed : Type (o ⊔ h ⊔ o' ⊔ h')
  is-thinly-displayed = ∀ {a b} {f : B.Hom a b} {x y} → is-prop (Hom[ f ] x y)
```

A displayed category $\cE$ over $\cB$ is a repackaging of the data of a
functor $\cE' \to \cB$, more precisely, the projection functor $\pi :
\int \cE \to \cB$ from the [[total category]] of $\cE$ into $\cB$.
Taking this view, we can characterise the thinly displayed categories as
those with a [[faithful]] projection functor.

```agda
  πᶠ-faithful→thin : is-faithful (πᶠ E) → is-thinly-displayed
  πᶠ-faithful→thin πᶠ-faithful f g = cast[] $ ap ∫Hom.snd (πᶠ-faithful refl)

  thin→πᶠ-faithful : is-thinly-displayed → is-faithful (πᶠ E)
  thin→πᶠ-faithful thin p = ∫Hom-path E p (to-pathp (thin _ _))

  πᶠ-faithful≃thin : is-faithful (πᶠ E) ≃ is-thinly-displayed
  πᶠ-faithful≃thin = prop-ext! πᶠ-faithful→thin thin→πᶠ-faithful
```

Intuitively, objects in a thinly displayed category over $\cB$ lying
over $b : \cB$ correspond to some kind of structure on $b$, and
morphisms between such structures are given by a subset of the morphisms
between the underlying objects, which we can think of as
structure-preserving.

For a thinly displayed category, the identity and associativity axioms
trivialise, so to construct one it suffices to prove that the morphism
predicate includes identities and is closed under composition.

```agda
  _ : Thinly-displayed B o' h' → Displayed B o' h'
  _ = with-thin-display
```

## Thinly displayed structures {defines="thin-structure"}

A particularly important example is categories thinly displayed over the
category of sets.  Equivalently, these are categories equipped with a
faithful functor into $\Sets$, known in the literature as concrete
categories.  These encompass most categories of standard mathematical
structures, like the [[category of monoids]], the [[category of
groups]], the category of [[posets]], and a plethora of other examples.
When working with specific examples of concrete categories it is often
useful to take the displayed point of view, as it lets one directly
define the class of relevant structures on a given set.

We define a type specifying a notion of **thinly displayed structure**
(or thin structure for short) for working with this presentation.  In
fact, this is the same as the HoTT Book's *notion of structure* over
$\Sets$, which can be seen as a very early example of displayed category
theory.

```agda
record
  Thin-structure {ℓ o'} ℓ' (S : Type ℓ → Type o')
    : Type (lsuc ℓ ⊔ o' ⊔ lsuc ℓ') where
  no-eta-equality
  field
    is-hom    : ∀ {x y} → (x → y) → S x → S y → Prop ℓ'
    id-is-hom : ∀ {x} {s : S x} → ∣ is-hom (λ x → x) s s ∣

    ∘-is-hom  :
      ∀ {x y z} {s t u} (f : y → z) (g : x → y)
      → (α : ∣ is-hom f t u ∣) (β : ∣ is-hom g s t ∣)
      → ∣ is-hom (λ x → f (g x)) s u ∣

open Thin-structure
```

Here, the type former `S`{.Agda} specifies a type of structures on a
given set `X` (for instance, monoids on `X`, or groups on `X`), while
`is-hom`{.Agda} is a predicate determining the structure-preserving
functions, required to include identities and compose.

A notion of thin structure is just a repackaging of a thinly displayed
category over sets, which we can show as follows.

```agda
module _ {S : Type o → Type o'} (spec : Thin-structure h' S) where
  Thin-structure→displayed : Displayed (Sets o) o' h'
  Thin-structure→displayed = with-thin-display record where
    Ob[_]      x = S ∣ x ∣
    Hom[_] f x y = ∣ spec .is-hom f x y ∣

    id'      = spec .id-is-hom
    _∘'_ f g = spec .∘-is-hom _ _ f g

  private
    Thin-structure-is-thin : is-thinly-displayed Thin-structure→displayed
    Thin-structure-is-thin = hlevel 1

module _ (E : Displayed (Sets o) o' h') (E-thin : is-thinly-displayed E) where
  open Displayed E
  Thinly-displayed→structure
    : Thin-structure h' (λ X → Σ[ Xset ∈ is-set X ] Ob[ el X Xset ])
  Thinly-displayed→structure .is-hom f (_ , A) (_ , B) = el (Hom[_] f A B) E-thin
  Thinly-displayed→structure .id-is-hom                = id'
  Thinly-displayed→structure .∘-is-hom _ _ Hf Hg       = Hf ∘' Hg
```

Putting our previous observations together, we can assemble a concrete
category from any notion of thin structure.  In other words, we have a
category of structured objects equipped with a faithful functor into
$\Sets$.

```agda
module _ {S : Type o → Type o'} (spec : Thin-structure h' S) where
  Structured-objects : Precategory _ _
  Structured-objects = ∫ (Thin-structure→displayed spec)

  Forget-structure : Functor Structured-objects (Sets o)
  Forget-structure = πᶠ (Thin-structure→displayed spec)

  Structured-hom-path : is-faithful Forget-structure
  Structured-hom-path = thin→πᶠ-faithful _ (hlevel 1)
```

<!--
```agda
module _ {S : Type o → Type o'} {spec : Thin-structure h' S} where
  private
    module So = Precategory (Structured-objects spec)
    module Som = Cm (Structured-objects spec)

  instance
    Extensional-Hom
      : ∀ {a b ℓr} ⦃ sa : Extensional (⌞ a ⌟ → ⌞ b ⌟) ℓr ⦄
      → Extensional (So.Hom a b) ℓr
    Extensional-Hom ⦃ sa ⦄ = injection→extensional!
      (Structured-hom-path spec) sa

  Homomorphism-monic
    : ∀ {x y} (f : So.Hom x y)
    → (∀ {x y} (p : f · x ≡ f · y) → x ≡ y)
    → Som.is-monic f
  Homomorphism-monic f wit g h p = ext λ x → wit (ap ∫Hom.fst p $ₚ x)
```
-->

## Univalent thin structures {defines="univalent-thin-structure"}

If `S`{.Agda} is a notion of thin structure and `X` is a set, we can
form a preorder on structures `S X` as follows.

```agda
module _ {S : Type o → Type o'} where
  private
    _≲[_]_ : ∀ {X} → S X → Thin-structure h' S → S X → Type _
    α ≲[ spec ] β = ∣ spec .is-hom (λ x → x) α β ∣
```

The HoTT Book's version of the structure identity principle defines a
*standard notion of structure* as a notion of thin structure where this
preorder is in fact a partial order for all `X`.  This corresponds to
the induced displayed category being [[univalent|displayed univalent
category]], so we refer to this as a **univalent** notion of thin
structure.

```agda
  record is-univalent-structure
    (spec : Thin-structure h' S) : Type (lsuc o ⊔ o' ⊔ h') where
    field
      id-hom-unique : ∀ {x} {s t : S x} → s ≲[ spec ] t → t ≲[ spec ] s → s ≡ t

    open Dm (Thin-structure→displayed spec)

    Structured-objects-is-category : is-category (Structured-objects spec)
    Structured-objects-is-category =
      is-category-total (Thin-structure→displayed spec) Sets-is-category $
        is-category-fibrewise _ Sets-is-category λ A x y →
        Σ-prop-path
          (λ _ _ _ → ≅[]-path (spec .is-hom _ _ _ .is-tr _ _))
          ( id-hom-unique (x .snd .from') (x .snd .to')
          ∙ id-hom-unique (y .snd .to') (y .snd .from'))

  open is-univalent-structure ⦃ ... ⦄ public hiding (id-hom-unique)
```

If the preorder on structures is instead symmetric, we refer to it as an
**equational** notion of thin structure.

```agda
  record is-equational-structure
    (spec : Thin-structure h' S) : Type (lsuc o ⊔ o' ⊔ h') where
    field
      invert-id-hom : ∀ {x} {s t : S x} → s ≲[ spec ] t → t ≲[ spec ] s
```

<!--
```agda
    private
      module So = Precategory (Structured-objects spec)
      module Som = Cm (Structured-objects spec)
```
-->

The upshot is that for equational structures, equivalences of underlying
sets which are also homomorphisms can be lifted to isomorphisms in the
category of structured objects.  We can show this using equivalence
induction, reducing the argument to the case where the given equivalence
is just an identity function.

```agda
    abstract
      equiv-hom→inverse-hom
        : ∀ {a b : So.Ob}
        → (f : ⌞ a ⌟ ≃ ⌞ b ⌟)
        → ∣ spec .is-hom (Equiv.to f) (a .snd) (b .snd) ∣
        → ∣ spec .is-hom (Equiv.from f) (b .snd) (a .snd) ∣
      equiv-hom→inverse-hom {a = a} {b = b} f e =
        EquivJ
          (λ B e → ∀ st
            → ∣ spec .is-hom (e .fst) (a .snd) st ∣
            → ∣ spec .is-hom (Equiv.from e) st (a .snd) ∣)
          (λ _ → invert-id-hom) f (b .snd) e

    total-iso
      : ∀ {a b : So.Ob}
      → (f : ⌞ a ⌟ ≃ ⌞ b ⌟)
      → ∣ spec .is-hom (Equiv.to f) (a .snd) (b .snd) ∣
      → a Som.≅ b
    total-iso {a} {b} f e = Som.make-iso
      (∫hom (Equiv.to f) e)
      (∫hom (Equiv.from f) (equiv-hom→inverse-hom {a} {b} f e))
      (ext (Equiv.ε f))
      (ext (Equiv.η f))

  open is-equational-structure ⦃ ... ⦄ public hiding (invert-id-hom)
```

It follows that if a notion of structure is both univalent and
equational, equivalences on underlying sets can be lifted to paths on
structured objects.

```agda
  module _
    {spec : Thin-structure h' S}
    ⦃ _ : is-univalent-structure spec ⦄ ⦃ _ : is-equational-structure spec ⦄ where
    private module So = Precategory (Structured-objects spec)
    ∫-Path
      : ∀ {a b : So.Ob}
      → (f : So.Hom a b)
      → is-equiv (f ·_)
      → a ≡ b
    ∫-Path {a = a} {b = b} f eqv = Univalent.iso→path
      Structured-objects-is-category
      (total-iso ((f ·_) , eqv) (f .∫Hom.snd))
```

<!--
```agda
Full-substructure
  : ∀ (R S : Type o → Type o') → (∀ X → R X ↪ S X)
  → Thin-structure h' S → Thin-structure h' R
Full-substructure R S embed Sst .is-hom f x y =
  Sst .is-hom f (embed _ .fst x) (embed _ .fst y)
Full-substructure R S embed Sst .id-is-hom = Sst .id-is-hom
Full-substructure R S embed Sst .∘-is-hom  = Sst .∘-is-hom

module _
  {R S : Type o → Type o'} {embed : ∀ X → R X ↪ S X} {spec : Thin-structure h' S}
  where
  open is-univalent-structure
  Full-substructure-univalent
    : is-univalent-structure spec
    → is-univalent-structure (Full-substructure R S embed spec)
  Full-substructure-univalent spec-univalent .id-hom-unique α β =
    has-prop-fibres→injective (embed _ .fst) (embed _ .snd)
      (spec-univalent .id-hom-unique α β)
```
-->
