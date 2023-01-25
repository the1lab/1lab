```agda
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Reasoning
import Cat.Displayed.Reasoning

module Cat.Displayed.Morphism
  {o ℓ o′ ℓ′}
  {ℬ : Precategory o ℓ}
  (ℰ : Displayed ℬ o′ ℓ′)
  where
```

<!--
```agda
open Displayed ℰ
open Cat.Reasoning ℬ
open Cat.Displayed.Reasoning ℰ
private variable
  a b c d : Ob
  f : Hom a b
  a′ b′ c′ ′ : Ob[ a ]
```
-->

# Displayed Morphisms

This module defines the displayed analogs of monomorphisms, epimorphisms,
and isomorphisms.

## Monos

Displayed [monomorphisms] have the the same left-cancellation properties
as their non-displayed counterparts. However, they must be displayed over
a monomorphism in the base.

[monomorphisms]: Cat.Morphism.html#Monos

```agda
is-monic[_]
  : ∀ {a′ : Ob[ a ]} {b′ : Ob[ b ]} {f : Hom a b}
  → is-monic f → Hom[ f ] a′ b′
  → Type _ 
is-monic[_] {a = a} {a′ = a′} {f = f} mono f′ =
  ∀ {c c′} {g h : Hom c a}
  → (g′ : Hom[ g ] c′ a′) (h′ : Hom[ h ] c′ a′)
  → (p : f ∘ g ≡ f ∘ h)
  → f′ ∘′ g′ ≡[ p ] f′ ∘′ h′
  → g′ ≡[ mono g h p ] h′

is-monic[]-is-prop
  : ∀ {a′ : Ob[ a ]} {b′ : Ob[ b ]} {f : Hom a b}
  → (mono : is-monic f) → (f′ : Hom[ f ] a′ b′)
  → is-prop (is-monic[ mono ] f′)
is-monic[]-is-prop {a′ = a′} mono f′ mono[] mono[]′ i {c′ = c′} g′ h′ p p′ =
  is-set→squarep (λ i j → Hom[ mono _ _ p j ]-set c′ a′)
    refl (mono[] g′ h′ p p′) (mono[]′ g′ h′ p p′) refl i

record _↪[_]_
  {a b} (a′ : Ob[ a ]) (f : a ↪ b) (b′ : Ob[ b ])
  : Type (o ⊔ ℓ ⊔ o′ ⊔ ℓ′)
  where
  no-eta-equality
  field
    mor′ : Hom[ f .mor ] a′ b′
    monic′ : is-monic[ f .monic ] mor′

open _↪[_]_ public
```

## Weak Monos

When working in a displayed setting, we also have weaker versions of
the morphism classes we are familiar with, wherein we can only left/right
cancel morphisms that are displayed over the same morphism in the base.
We denote these morphisms classes as "weak".

```agda
is-weak-monic
  : ∀ {a′ : Ob[ a ]} {b′ : Ob[ b ]} {f : Hom a b}
  → Hom[ f ] a′ b′
  → Type _ 
is-weak-monic {a = a} {a′ = a′} {f = f} f′ =
  ∀ {c c′} {g : Hom c a}
  → (g′ g″ : Hom[ g ] c′ a′)
  → f′ ∘′ g′ ≡ f′ ∘′ g″
  → g′ ≡ g″

is-weak-monic-is-prop
  : ∀ {a′ : Ob[ a ]} {b′ : Ob[ b ]} {f : Hom a b}
  → (f′ : Hom[ f ] a′ b′)
  → is-prop (is-weak-monic f′)
is-weak-monic-is-prop f′ mono mono′ i g′ g″ p =
  is-prop→pathp (λ i → Hom[ _ ]-set _ _ g′ g″)
    (mono g′ g″ p) (mono′ g′ g″ p) i

record _↪ʷ_
  {a b} (a′ : Ob[ a ]) (f : Hom a b) (b′ : Ob[ b ])
  : Type (o ⊔ ℓ ⊔ o′ ⊔ ℓ′)
  where
  no-eta-equality
  field
    mor′ : Hom[ f ] a′ b′
    weak-monic : is-weak-monic mor′
```

## Epis

Displayed [epimorphisms] are defined in a similar fashion.

[epimorphisms]: Cat.Morphism.html#Epis

```agda
is-epic[_]
  : ∀ {a′ : Ob[ a ]} {b′ : Ob[ b ]} {f : Hom a b}
  → is-epic f → Hom[ f ] a′ b′
  → Type _ 
is-epic[_] {b = b} {b′ = b′} {f = f} epi f′ =
  ∀ {c} {c′} {g h : Hom b c}
  → (g′ : Hom[ g ] b′ c′) (h′ : Hom[ h ] b′ c′)
  → (p : g ∘ f ≡ h ∘ f)
  → g′ ∘′ f′ ≡[ p ] h′ ∘′ f′
  → g′ ≡[ epi g h p ] h′

is-epic[]-is-prop
  : ∀ {a′ : Ob[ a ]} {b′ : Ob[ b ]} {f : Hom a b}
  → (epi : is-epic f) → (f′ : Hom[ f ] a′ b′)
  → is-prop (is-epic[ epi ] f′)
is-epic[]-is-prop {b′ = b′} epi f′ epi[] epi[]′ i {c′ = c′} g′ h′ p p′ =
  is-set→squarep (λ i j → Hom[ epi _ _ p j ]-set b′ c′)
    refl (epi[] g′ h′ p p′) (epi[]′ g′ h′ p p′) refl i

record _↠[_]_
  {a b} (a′ : Ob[ a ]) (f : a ↠ b) (b′ : Ob[ b ])
  : Type (o ⊔ ℓ ⊔ o′ ⊔ ℓ′)
  where
  no-eta-equality
  field
    mor′ : Hom[ f .mor ] a′ b′
    monic′ : is-epic[ f .epic ] mor′
```

## Weak Epis

We can define a weaker notion of epis that is dual to the definition of
a weak mono.

```agda
is-weak-epic
  : ∀ {a′ : Ob[ a ]} {b′ : Ob[ b ]} {f : Hom a b}
  → Hom[ f ] a′ b′
  → Type _ 
is-weak-epic {b = b} {b′ = b′} {f = f} f′ =
  ∀ {c c′} {g : Hom b c}
  → (g′ g″ : Hom[ g ] b′ c′)
  → g′ ∘′ f′ ≡ g″ ∘′ f′
  → g′ ≡ g″

is-weak-epic-is-prop
  : ∀ {a′ : Ob[ a ]} {b′ : Ob[ b ]} {f : Hom a b}
  → (f′ : Hom[ f ] a′ b′)
  → is-prop (is-weak-monic f′)
is-weak-epic-is-prop f′ epi epi′ i g′ g″ p =
  is-prop→pathp (λ i → Hom[ _ ]-set _ _ g′ g″)
    (epi g′ g″ p) (epi′ g′ g″ p) i

record _↠ʷ_
  {a b} (a′ : Ob[ a ]) (f : Hom a b) (b′ : Ob[ b ])
  : Type (o ⊔ ℓ ⊔ o′ ⊔ ℓ′)
  where
  no-eta-equality
  field
    mor′ : Hom[ f ] a′ b′
    weak-epic : is-weak-epic mor′
```

## Sections

Following the same pattern as before, we define a notion of displayed
sections.

```agda
_section-of[_]_
  : ∀ {x y} {s : Hom y x} {r : Hom x y}
  → ∀ {x′ y′} (s′ : Hom[ s ] y′ x′) → s section-of r → (r′ : Hom[ r ] x′ y′)
  → Type _
s′ section-of[ p ] r′ = r′ ∘′ s′ ≡[ p ] id′

record has-section[_]
  {x y x′ y′} {r : Hom x y} (sect : has-section r) (r′ : Hom[ r ] x′ y′)
  : Type ℓ′
  where
  no-eta-equality
  field
    section′ : Hom[ sect .section ] y′ x′
    is-section′ : section′ section-of[ sect .is-section ] r′
```

We also distinguish the sections that are displayed over the identity
morphism; these are known as "vertical sections".

```agda
_section-of↓_
  : ∀ {x} {x′ x″ : Ob[ x ]} (s′ : Hom[ id ] x″ x′) → (r : Hom[ id ] x′ x″)
  → Type _
s′ section-of↓ r′ = s′ section-of[ idl id ] r′

has-section↓ : ∀ {x} {x′ x″ : Ob[ x ]} (r′ : Hom[ id ] x′ x″) → Type _
has-section↓ r′ = has-section[ id-has-section ] r′
```

## Retracts

We can do something similar for retracts.

```agda
_retract-of[_]_
  : ∀ {x y} {s : Hom y x} {r : Hom x y}
  → ∀ {x′ y′} (r′ : Hom[ r ] x′ y′) → r retract-of s → (s′ : Hom[ s ] y′ x′)
  → Type _
r′ retract-of[ p ] s′ = r′ ∘′ s′ ≡[ p ] id′


record has-retract[_]
  {x y x′ y′} {s : Hom x y} (ret : has-retract s) (s′ : Hom[ s ] x′ y′)
  : Type ℓ′
  where
  no-eta-equality
  field
    retract′ : Hom[ ret .retract ] y′ x′
    is-retarct′ : retract′ retract-of[ ret .is-retract ] s′
```

We also define vertical retracts in a similar manner as before.

```agda
_retract-of↓_
  : ∀ {x} {x′ x″ : Ob[ x ]} (r′ : Hom[ id ] x′ x″) → (s : Hom[ id ] x″ x′)
  → Type _
r′ retract-of↓ s′ = r′ retract-of[ idl id ] s′

has-retract↓ : ∀ {x} {x′ x″ : Ob[ x ]} (s′ : Hom[ id ] x″ x′) → Type _
has-retract↓ s′ = has-retract[ id-has-retract ] s′
```

## Isos

Displayed [isomorphisms] must also be defined over isomorphisms in the
base.

[isomorphisms]: Cat.Morphism.html#Isos

```agda
record Inverses[_]
  {a b a′ b′} {f : Hom a b} {g : Hom b a}
  (inv : Inverses f g)
  (f′ : Hom[ f ] a′ b′) (g′ : Hom[ g ] b′ a′)
  : Type ℓ′
  where
  no-eta-equality
  field
    invl′ : f′ ∘′ g′ ≡[ Inverses.invl inv ] id′
    invr′ : g′ ∘′ f′ ≡[ Inverses.invr inv ] id′

record is-invertible[_]
  {a b a′ b′} {f : Hom a b}
  (f-inv : is-invertible f)
  (f′ : Hom[ f ] a′ b′)
  : Type ℓ′
  where
  no-eta-equality
  field
    inv′ : Hom[ is-invertible.inv f-inv ] b′ a′
    inverses′ : Inverses[ is-invertible.inverses f-inv ] f′ inv′

  open Inverses[_] inverses′ public

record _≅[_]_
  {a b} (a′ : Ob[ a ]) (i : a ≅ b) (b′ : Ob[ b ])
  : Type ℓ′
  where
  no-eta-equality
  field
    to′ : Hom[ i .to ] a′ b′
    from′ : Hom[ i .from ] b′ a′
    inverses′ : Inverses[ i .inverses ] to′ from′

  open Inverses[_] inverses′ public

open _≅[_]_ public
```

Since isomorphisms over the identity map will be of particular
importance, we also define their own type: they are the _vertical
isomorphisms_.

```agda
_≅↓_ : {x : Ob} (A B : Ob[ x ]) → Type ℓ′
_≅↓_ = _≅[ id-iso ]_

is-invertible↓ : {x : Ob} {x′ x″ : Ob[ x ]} → Hom[ id ] x′ x″ → Type _
is-invertible↓ = is-invertible[ id-invertible ]
```

Like their non-displayed counterparts, existence of displayed inverses
is a proposition.

```agda
Inverses[]-are-prop
  : ∀ {a b a′ b′} {f : Hom a b} {g : Hom b a}
  → (inv : Inverses f g)
  → (f′ : Hom[ f ] a′ b′) (g′ : Hom[ g ] b′ a′)
  → is-prop (Inverses[ inv ] f′ g′)
Inverses[]-are-prop inv f′ g′ inv[] inv[]′ i .Inverses[_].invl′ =
  is-set→squarep (λ i j → Hom[ Inverses.invl inv j ]-set _ _)
    refl (Inverses[_].invl′ inv[]) (Inverses[_].invl′ inv[]′) refl i
Inverses[]-are-prop inv f′ g′ inv[] inv[]′ i .Inverses[_].invr′ =
  is-set→squarep (λ i j → Hom[ Inverses.invr inv j ]-set _ _)
    refl (Inverses[_].invr′ inv[]) (Inverses[_].invr′ inv[]′) refl i

is-invertible[]-is-prop
  : ∀ {a b a′ b′} {f : Hom a b}
  → (f-inv : is-invertible f)
  → (f′ : Hom[ f ] a′ b′)
  → is-prop (is-invertible[ f-inv ] f′)
is-invertible[]-is-prop inv f′ p q = path where
  module inv = is-invertible inv
  module p = is-invertible[_] p
  module q = is-invertible[_] q

  inv≡inv′ : p.inv′ ≡ q.inv′
  inv≡inv′ =
    p.inv′                           ≡⟨ shiftr (insertr inv.invl) (insertr′ _ q.invl′) ⟩
    hom[] ((p.inv′ ∘′ f′) ∘′ q.inv′) ≡⟨ weave _ (eliml inv.invr) refl (eliml′ _ p.invr′) ⟩
    hom[] q.inv′                     ≡⟨ liberate _ ⟩
    q.inv′ ∎

  path : p ≡ q
  path i .is-invertible[_].inv′ = inv≡inv′ i
  path i .is-invertible[_].inverses′ =
    is-prop→pathp (λ i → Inverses[]-are-prop inv.inverses f′ (inv≡inv′ i))
      p.inverses′ q.inverses′ i
```

<!--
```agda
make-iso[_]
  : ∀ {a b a′ b′}
  → (iso : a ≅ b)
  → (f′ : Hom[ iso .to ] a′ b′) (g′ : Hom[ iso .from ] b′ a′)
  → f′ ∘′ g′ ≡[ iso .invl ] id′ 
  → g′ ∘′ f′ ≡[ iso .invr ] id′
  → a′ ≅[ iso ] b′
make-iso[ inv ] f′ g′ p q .to′ = f′
make-iso[ inv ] f′ g′ p q .from′ = g′
make-iso[ inv ] f′ g′ p q .inverses′ .Inverses[_].invl′ = p
make-iso[ inv ] f′ g′ p q .inverses′ .Inverses[_].invr′ = q

≅[]-path
  : {x y : Ob} {A : Ob[ x ]} {B : Ob[ y ]} {f : x ≅ y}
    {p q : A ≅[ f ] B}
  → p .to′ ≡ q .to′
  → p .from′ ≡ q .from′
  → p ≡ q
≅[]-path {p = p} {q = q} a b i .to′ = a i
≅[]-path {p = p} {q = q} a b i .from′ = b i
≅[]-path {f = f} {p = p} {q = q} a b i .inverses′ .Inverses[_].invl′ j =
  is-set→squarep (λ i j → Hom[ f .invl j ]-set _ _)
    (λ i → a i ∘′ b i) (p .invl′) (q .invl′) (λ i → id′) i j
≅[]-path {f = f} {p = p} {q = q} a b i .inverses′ .Inverses[_].invr′ j =
  is-set→squarep (λ i j → Hom[ f .invr j ]-set _ _)
    (λ i → b i ∘′ a i) (p .invr′) (q .invr′) (λ i → id′) i j
```
-->

As in the non-displayed case, the identity isomorphism is always an
iso. In fact, it is a vertical iso!

```agda
id-iso↓ : ∀ {x} {x′ : Ob[ x ]} → x′ ≅↓ x′
id-iso↓ = make-iso[ id-iso ] id′ id′ (idl′ id′) (idl′ id′)
```

