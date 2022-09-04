```agda
open import Cat.Displayed.Univalence
open import Cat.Displayed.Total
open import Cat.Instances.Sets
open import Cat.Displayed.Base
open import Cat.Functor.Base
open import Cat.Univalent
open import Cat.Prelude

import Cat.Morphism

module Cat.Displayed.Univalence.Thin where

```

<!--
```agda
open Cat.Displayed.Total public
open Cat.Displayed.Base public
open Total-hom public
open Precategory
open Displayed
open _≅[_]_
```
-->

# Thinly displayed structures

The HoTT Book's version of the structure identity principle can be seen
as a very early example of displayed category theory. Their notion of
_standard notion of structure_ corresponds exactly to a displayed
category, all of whose fibres are posets. Note that this is not a
category _fibred in_ posets, since the displayed category will not
necessarily be a Cartesian fibration.

Here, we restrict our attention to an important special case: Categories
of structures over the category of sets (for a given universe level).
Since these all have thin fibres (by assumption), we refer to them as
_thinly displayed structures_, or _thin structures_ for short. These are
of note not only because they intersect the categorical SIP defined
above with the [typal SIP] established in the prelude modules, but also
because we can work with them very directly.

```agda
record
  Thin-structure {ℓ o′} ℓ′ (S : Type ℓ → Type o′)
    : Type (lsuc ℓ ⊔ o′ ⊔ lsuc ℓ′) where
  no-eta-equality
  field
    is-hom    : ∀ {x y} → (x → y) → S x → S y → Prop ℓ′

    id-is-hom : ∀ {x} {s : S x} → ∣ is-hom (λ x → x) s s ∣
    ∘-is-hom  :
      ∀ {x y z} {s t u} (f : y → z) (g : x → y)
      → ∣ is-hom f t u ∣ → ∣ is-hom g s t ∣ → ∣ is-hom (λ x → f (g x)) s u ∣

open Thin-structure public

module _
  {ℓ o′ ℓ′} {S : Type ℓ → Type o′}
  (spec : Thin-structure ℓ′ S) where
```

The data above conspires to make a category displayed over $\ca{B}$. The
laws are trivial since $H$ is valued in propositions.

```agda
  Thin-structure-over : Displayed (Sets ℓ) o′ ℓ′
  Thin-structure-over .Ob[_] x = S ∣ x ∣
  Thin-structure-over .Hom[_] f x y = ∣ spec .is-hom f x y ∣
  Thin-structure-over .Hom[_]-set f a b = is-prop→is-set hlevel!
  Thin-structure-over .id′ = spec .id-is-hom
  Thin-structure-over ._∘′_ f g = spec .∘-is-hom _ _ f g
  Thin-structure-over .idr′ f′ = is-prop→pathp (λ _ → hlevel!) _ _
  Thin-structure-over .idl′ f′ = is-prop→pathp (λ _ → hlevel!) _ _
  Thin-structure-over .assoc′ f′ g′ h′ = is-prop→pathp (λ _ → hlevel!) _ _

  Structured-objects : Precategory _ _
  Structured-objects = ∫ Thin-structure-over
```

We recall that the $S$-structures can be made into a preorder by setting
$\alpha \le \beta$ iff. the identity morphism is an $H$-homomorphism
from $\alpha$ to $\beta$. And, if this preorder is in fact a partial
order, then the total category of structures is univalent --- the type
of identities between $S$-structured $\ca{B}$-objects is equivalent to
the type of $H$-homomorphic $\ca{B}$-isomorphisms.

```agda
  thin-SIP
    : ( ∀ {x} (α β : S x)
      → ∣ spec .is-hom (λ x → x) α β ∣
      → ∣ spec .is-hom (λ x → x) β α ∣
      → α ≡ β )
    → is-category Structured-objects
  thin-SIP H-antisym =
    is-category-total Thin-structure-over Sets-is-category $
      is-category-fibrewise _ Sets-is-category λ A x y →
      Σ-prop-path
        (λ _ _ _ → ≅[]-path _ (spec .is-hom _ _ _ .is-tr _ _)
                              (spec .is-hom _ _ _ .is-tr _ _))
        (H-antisym _ _
          (spec .∘-is-hom _ _ (y .snd .to′) (x .snd .from′))
          (spec .∘-is-hom _ _ (x .snd .to′) (y .snd .from′)))
```

Connecting this to the typal SIP, if the thin structure $S$ induces a
univalent structure (in the standard sense of the word), then it
satisfies the premises of the thin SIP defined above. This means that we
can re-use the automated SIP machinery for proving univalence of
categories!

```agda
  displayed-SIP
    : is-univalent {S = S}
        (HomT→Str (λ A B f → ∣ spec .is-hom (f .fst) (A .snd) (B .snd) ∣))
    → is-category Structured-objects
  displayed-SIP univ = thin-SIP λ A B α β →
       sym (transport-refl _)
    ·· ap (λ e → subst S e A) (sym ua-id-equiv)
    ·· from-pathp (univ (_ , id-equiv) .fst α)
```

By construction, such a category of structured objects admits a faithful
functor into the category of sets.

```agda
  Forget-structure : Functor Structured-objects (Sets ℓ)
  Forget-structure = πᶠ Thin-structure-over

  Structured-hom-path : is-faithful Forget-structure
  Structured-hom-path p =
    total-hom-path Thin-structure-over p (is-prop→pathp (λ _ → hlevel!) _ _)

module _ {ℓ o′ ℓ′} {S : Type ℓ → Type o′} {spec : Thin-structure ℓ′ S} where
  private
    module So = Precategory (Structured-objects spec)
    module Som = Cat.Morphism (Structured-objects spec)

  ⌞_⌟ : So.Ob → Type ℓ
  ⌞ x ⌟ = ∣ x .fst ∣

  _#_ : ∀ {a b : So.Ob} → So.Hom a b → ⌞ a ⌟ → ⌞ b ⌟
  f # x = f .Total-hom.hom x

  Homomorphism-path
    : ∀ {x y : So.Ob} {f g : So.Hom x y}
    → (∀ x → f # x ≡ g # x)
    → f ≡ g
  Homomorphism-path h = Structured-hom-path spec (funext h)

  Homomorphism-monic
    : ∀ {x y : So.Ob} {f : So.Hom x y}
    → (∀ {x y} (p : f # x ≡ f # y) → x ≡ y)
    → Som.is-monic f
  Homomorphism-monic wit g h p = Homomorphism-path λ x → wit (ap hom p $ₚ x)
```
