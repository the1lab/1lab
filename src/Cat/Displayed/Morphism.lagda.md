<!--
```agda
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Reasoning
import Cat.Reasoning
```
-->

```agda
module Cat.Displayed.Morphism
  {o ℓ o' ℓ'}
  {ℬ : Precategory o ℓ}
  (ℰ : Displayed ℬ o' ℓ')
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
  a' b' c' : Ob[ a ]
```
-->

# Displayed morphisms

This module defines the displayed analogs of monomorphisms, epimorphisms,
and isomorphisms.

## Monos {defines="displayed-monomorphism"}

_Displayed_ [[monomorphisms]] have the the same left-cancellation properties
as their non-displayed counterparts. However, they must be displayed over
a monomorphism in the base.

```agda
is-monic[_]
  : ∀ {a' : Ob[ a ]} {b' : Ob[ b ]} {f : Hom a b}
  → is-monic f → Hom[ f ] a' b'
  → Type _
is-monic[_] {a = a} {a' = a'} {f = f} mono f' =
  ∀ {c c'} {g h : Hom c a}
  → (g' : Hom[ g ] c' a') (h' : Hom[ h ] c' a')
  → (p : f ∘ g ≡ f ∘ h)
  → f' ∘' g' ≡[ p ] f' ∘' h'
  → g' ≡[ mono g h p ] h'

is-monic[]-is-prop
  : ∀ {a' : Ob[ a ]} {b' : Ob[ b ]} {f : Hom a b}
  → (mono : is-monic f) → (f' : Hom[ f ] a' b')
  → is-prop (is-monic[ mono ] f')
is-monic[]-is-prop {a' = a'} mono f' mono[] mono[]' i {c' = c'} g' h' p p' =
  is-set→squarep (λ i j → Hom[ mono _ _ p j ]-set c' a')
    refl (mono[] g' h' p p') (mono[]' g' h' p p') refl i

record _↪[_]_
  {a b} (a' : Ob[ a ]) (f : a ↪ b) (b' : Ob[ b ])
  : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ')
  where
  no-eta-equality
  field
    mor' : Hom[ f .mor ] a' b'
    monic' : is-monic[ f .monic ] mor'

open _↪[_]_ public
```

## Weak monos

When working in a displayed setting, we also have weaker versions of
the morphism classes we are familiar with, wherein we can only left/right
cancel morphisms that are displayed over the same morphism in the base.
We denote these morphisms classes as "weak".

```agda
is-weak-monic
  : ∀ {a' : Ob[ a ]} {b' : Ob[ b ]} {f : Hom a b}
  → Hom[ f ] a' b'
  → Type _
is-weak-monic {a = a} {a' = a'} {f = f} f' =
  ∀ {c c'} {g : Hom c a}
  → (g' g'' : Hom[ g ] c' a')
  → f' ∘' g' ≡ f' ∘' g''
  → g' ≡ g''

is-weak-monic-is-prop
  : ∀ {a' : Ob[ a ]} {b' : Ob[ b ]} {f : Hom a b}
  → (f' : Hom[ f ] a' b')
  → is-prop (is-weak-monic f')
is-weak-monic-is-prop f' mono mono' i g' g'' p =
  is-prop→pathp (λ i → Hom[ _ ]-set _ _ g' g'')
    (mono g' g'' p) (mono' g' g'' p) i

record weak-mono-over
  {a b} (f : Hom a b) (a' : Ob[ a ]) (b' : Ob[ b ])
  : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ')
  where
  no-eta-equality
  field
    mor' : Hom[ f ] a' b'
    weak-monic : is-weak-monic mor'

open weak-mono-over public
```

## Epis

Displayed [epimorphisms] are defined in a similar fashion.

[epimorphisms]: Cat.Morphism.html#epis

```agda
is-epic[_]
  : ∀ {a' : Ob[ a ]} {b' : Ob[ b ]} {f : Hom a b}
  → is-epic f → Hom[ f ] a' b'
  → Type _
is-epic[_] {b = b} {b' = b'} {f = f} epi f' =
  ∀ {c} {c'} {g h : Hom b c}
  → (g' : Hom[ g ] b' c') (h' : Hom[ h ] b' c')
  → (p : g ∘ f ≡ h ∘ f)
  → g' ∘' f' ≡[ p ] h' ∘' f'
  → g' ≡[ epi g h p ] h'

is-epic[]-is-prop
  : ∀ {a' : Ob[ a ]} {b' : Ob[ b ]} {f : Hom a b}
  → (epi : is-epic f) → (f' : Hom[ f ] a' b')
  → is-prop (is-epic[ epi ] f')
is-epic[]-is-prop {b' = b'} epi f' epi[] epi[]' i {c' = c'} g' h' p p' =
  is-set→squarep (λ i j → Hom[ epi _ _ p j ]-set b' c')
    refl (epi[] g' h' p p') (epi[]' g' h' p p') refl i

record _↠[_]_
  {a b} (a' : Ob[ a ]) (f : a ↠ b) (b' : Ob[ b ])
  : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ')
  where
  no-eta-equality
  field
    mor' : Hom[ f .mor ] a' b'
    epic' : is-epic[ f .epic ] mor'

open _↠[_]_ public
```

## Weak epis

We can define a weaker notion of epis that is dual to the definition of
a weak mono.

```agda
is-weak-epic
  : ∀ {a' : Ob[ a ]} {b' : Ob[ b ]} {f : Hom a b}
  → Hom[ f ] a' b'
  → Type _
is-weak-epic {b = b} {b' = b'} {f = f} f' =
  ∀ {c c'} {g : Hom b c}
  → (g' g'' : Hom[ g ] b' c')
  → g' ∘' f' ≡ g'' ∘' f'
  → g' ≡ g''

is-weak-epic-is-prop
  : ∀ {a' : Ob[ a ]} {b' : Ob[ b ]} {f : Hom a b}
  → (f' : Hom[ f ] a' b')
  → is-prop (is-weak-monic f')
is-weak-epic-is-prop f' epi epi' i g' g'' p =
  is-prop→pathp (λ i → Hom[ _ ]-set _ _ g' g'')
    (epi g' g'' p) (epi' g' g'' p) i

record weak-epi-over
  {a b} (f : Hom a b) (a' : Ob[ a ]) (b' : Ob[ b ])
  : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ')
  where
  no-eta-equality
  field
    mor' : Hom[ f ] a' b'
    weak-epic : is-weak-epic mor'

open weak-epi-over public
```

## Sections

Following the same pattern as before, we define a notion of displayed
sections.

```agda
_section-of[_]_
  : ∀ {x y} {s : Hom y x} {r : Hom x y}
  → ∀ {x' y'} (s' : Hom[ s ] y' x') → s section-of r → (r' : Hom[ r ] x' y')
  → Type _
s' section-of[ p ] r' = r' ∘' s' ≡[ p ] id'

record has-section[_]
  {x y x' y'} {r : Hom x y} (sect : has-section r) (r' : Hom[ r ] x' y')
  : Type ℓ'
  where
  no-eta-equality
  field
    section' : Hom[ sect .section ] y' x'
    is-section' : section' section-of[ sect .is-section ] r'

open has-section[_] public
```

We also distinguish the sections that are displayed over the identity
morphism; these are known as "vertical sections".

```agda
_section-of↓_
  : ∀ {x} {x' x'' : Ob[ x ]} (s' : Hom[ id ] x'' x') → (r : Hom[ id ] x' x'')
  → Type _
s' section-of↓ r' = s' section-of[ idl id ] r'

has-section↓ : ∀ {x} {x' x'' : Ob[ x ]} (r' : Hom[ id ] x' x'') → Type _
has-section↓ r' = has-section[ id-has-section ] r'
```

## Retracts

We can do something similar for retracts.

```agda
_retract-of[_]_
  : ∀ {x y} {s : Hom y x} {r : Hom x y}
  → ∀ {x' y'} (r' : Hom[ r ] x' y') → r retract-of s → (s' : Hom[ s ] y' x')
  → Type _
r' retract-of[ p ] s' = r' ∘' s' ≡[ p ] id'


record has-retract[_]
  {x y x' y'} {s : Hom x y} (ret : has-retract s) (s' : Hom[ s ] x' y')
  : Type ℓ'
  where
  no-eta-equality
  field
    retract' : Hom[ ret .retract ] y' x'
    is-retract' : retract' retract-of[ ret .is-retract ] s'

open has-retract[_] public
```

We also define vertical retracts in a similar manner as before.

```agda
_retract-of↓_
  : ∀ {x} {x' x'' : Ob[ x ]} (r' : Hom[ id ] x' x'') → (s : Hom[ id ] x'' x')
  → Type _
r' retract-of↓ s' = r' retract-of[ idl id ] s'

has-retract↓ : ∀ {x} {x' x'' : Ob[ x ]} (s' : Hom[ id ] x'' x') → Type _
has-retract↓ s' = has-retract[ id-has-retract ] s'
```

## Isos

Displayed [isomorphisms] must also be defined over isomorphisms in the
base.

[isomorphisms]: Cat.Morphism.html#isos

```agda
record Inverses[_]
  {a b a' b'} {f : Hom a b} {g : Hom b a}
  (inv : Inverses f g)
  (f' : Hom[ f ] a' b') (g' : Hom[ g ] b' a')
  : Type ℓ'
  where
  no-eta-equality
  field
    invl' : f' ∘' g' ≡[ Inverses.invl inv ] id'
    invr' : g' ∘' f' ≡[ Inverses.invr inv ] id'

record is-invertible[_]
  {a b a' b'} {f : Hom a b}
  (f-inv : is-invertible f)
  (f' : Hom[ f ] a' b')
  : Type ℓ'
  where
  no-eta-equality
  field
    inv' : Hom[ is-invertible.inv f-inv ] b' a'
    inverses' : Inverses[ is-invertible.inverses f-inv ] f' inv'

  open Inverses[_] inverses' public

record _≅[_]_
  {a b} (a' : Ob[ a ]) (i : a ≅ b) (b' : Ob[ b ])
  : Type ℓ'
  where
  no-eta-equality
  field
    to' : Hom[ i .to ] a' b'
    from' : Hom[ i .from ] b' a'
    inverses' : Inverses[ i .inverses ] to' from'

  open Inverses[_] inverses' public

open _≅[_]_ public
```

Since isomorphisms over the identity map will be of particular
importance, we also define their own type: they are the _vertical
isomorphisms_.

```agda
_≅↓_ : {x : Ob} (A B : Ob[ x ]) → Type ℓ'
_≅↓_ = _≅[ id-iso ]_

is-invertible↓ : {x : Ob} {x' x'' : Ob[ x ]} → Hom[ id ] x' x'' → Type _
is-invertible↓ = is-invertible[ id-invertible ]

make-invertible↓
  : ∀ {x} {x' x'' : Ob[ x ]} {f' : Hom[ id ] x' x''}
  → (g' : Hom[ id ] x'' x')
  → f' ∘' g' ≡[ idl _ ] id'
  → g' ∘' f' ≡[ idl _ ] id'
  → is-invertible↓ f'
make-invertible↓ g' p q .is-invertible[_].inv' = g'
make-invertible↓ g' p q .is-invertible[_].inverses' .Inverses[_].invl' = p
make-invertible↓ g' p q .is-invertible[_].inverses' .Inverses[_].invr' = q
```

Like their non-displayed counterparts, existence of displayed inverses
is a proposition.

```agda
Inverses[]-are-prop
  : ∀ {a b a' b'} {f : Hom a b} {g : Hom b a}
  → (inv : Inverses f g)
  → (f' : Hom[ f ] a' b') (g' : Hom[ g ] b' a')
  → is-prop (Inverses[ inv ] f' g')
Inverses[]-are-prop inv f' g' inv[] inv[]' i .Inverses[_].invl' =
  is-set→squarep (λ i j → Hom[ Inverses.invl inv j ]-set _ _)
    refl (Inverses[_].invl' inv[]) (Inverses[_].invl' inv[]') refl i
Inverses[]-are-prop inv f' g' inv[] inv[]' i .Inverses[_].invr' =
  is-set→squarep (λ i j → Hom[ Inverses.invr inv j ]-set _ _)
    refl (Inverses[_].invr' inv[]) (Inverses[_].invr' inv[]') refl i

is-invertible[]-is-prop
  : ∀ {a b a' b'} {f : Hom a b}
  → (f-inv : is-invertible f)
  → (f' : Hom[ f ] a' b')
  → is-prop (is-invertible[ f-inv ] f')
is-invertible[]-is-prop inv f' p q = path where
  module inv = is-invertible inv
  module p = is-invertible[_] p
  module q = is-invertible[_] q

  inv≡inv' : p.inv' ≡ q.inv'
  inv≡inv' =
    p.inv'                           ≡⟨ shiftr (insertr inv.invl) (insertr' _ q.invl') ⟩
    hom[] ((p.inv' ∘' f') ∘' q.inv') ≡⟨ weave _ (eliml inv.invr) refl (eliml' _ p.invr') ⟩
    hom[] q.inv'                     ≡⟨ liberate _ ⟩
    q.inv' ∎

  path : p ≡ q
  path i .is-invertible[_].inv' = inv≡inv' i
  path i .is-invertible[_].inverses' =
    is-prop→pathp (λ i → Inverses[]-are-prop inv.inverses f' (inv≡inv' i))
      p.inverses' q.inverses' i
```

<!--
```agda
make-iso[_]
  : ∀ {a b a' b'}
  → (iso : a ≅ b)
  → (f' : Hom[ iso .to ] a' b') (g' : Hom[ iso .from ] b' a')
  → f' ∘' g' ≡[ iso .invl ] id'
  → g' ∘' f' ≡[ iso .invr ] id'
  → a' ≅[ iso ] b'
make-iso[ inv ] f' g' p q .to' = f'
make-iso[ inv ] f' g' p q .from' = g'
make-iso[ inv ] f' g' p q .inverses' .Inverses[_].invl' = p
make-iso[ inv ] f' g' p q .inverses' .Inverses[_].invr' = q

make-vertical-iso
  : ∀ {x} {x' x'' : Ob[ x ]}
  → (f' : Hom[ id ] x' x'') (g' : Hom[ id ] x'' x')
  → f' ∘' g' ≡[ idl _ ] id'
  → g' ∘' f' ≡[ idl _ ] id'
  → x' ≅↓ x''
make-vertical-iso = make-iso[ id-iso ]

invertible[]→iso[]
  : ∀ {a b a' b'} {f : Hom a b} {f' : Hom[ f ] a' b'}
  → {i : is-invertible f}
  → is-invertible[ i ] f'
  → a' ≅[ invertible→iso f i ] b'
invertible[]→iso[] {f' = f'} i =
  make-iso[ _ ]
    f'
    (is-invertible[_].inv' i)
    (is-invertible[_].invl' i)
    (is-invertible[_].invr' i)

≅[]-path
  : {x y : Ob} {A : Ob[ x ]} {B : Ob[ y ]} {f : x ≅ y}
    {p q : A ≅[ f ] B}
  → p .to' ≡ q .to'
  → p ≡ q
≅[]-path {f = f} {p = p} {q = q} a = it where
  p' : PathP (λ i → is-invertible[ iso→invertible f ] (a i))
    (record { inv' = p .from' ; inverses' = p .inverses' })
    (record { inv' = q .from' ; inverses' = q .inverses' })
  p' = is-prop→pathp (λ i → is-invertible[]-is-prop _ (a i)) _ _

  it : p ≡ q
  it i .to'       = a i
  it i .from'     = p' i .is-invertible[_].inv'
  it i .inverses' = p' i .is-invertible[_].inverses'

instance
  Extensional-≅[]
    : ∀ {ℓr} {x y : Ob} {x' : Ob[ x ]} {y' : Ob[ y ]} {f : x ≅ y}
    → ⦃ sa : Extensional (Hom[ f .to ] x' y') ℓr ⦄
    → Extensional (x' ≅[ f ] y') ℓr
  Extensional-≅[] ⦃ sa ⦄ = injection→extensional! ≅[]-path sa
```
-->

As in the non-displayed case, the identity isomorphism is always an
iso. In fact, it is a vertical iso!

```agda
id-iso↓ : ∀ {x} {x' : Ob[ x ]} → x' ≅↓ x'
id-iso↓ = make-iso[ id-iso ] id' id' (idl' id') (idl' id')
```

Isomorphisms are also instances of sections and retracts.

```agda
inverses[]→to-has-section[]
  : ∀ {f : Hom a b} {g : Hom b a}
  → ∀ {a' b'} {f' : Hom[ f ] a' b'} {g' : Hom[ g ] b' a'}
  → {inv : Inverses f g} → Inverses[ inv ] f' g'
  → has-section[ inverses→to-has-section inv ] f'
inverses[]→to-has-section[] {g' = g'} inv' .section' = g'
inverses[]→to-has-section[] inv' .is-section' = Inverses[_].invl' inv'

inverses[]→from-has-section[]
  : ∀ {f : Hom a b} {g : Hom b a}
  → ∀ {a' b'} {f' : Hom[ f ] a' b'} {g' : Hom[ g ] b' a'}
  → {inv : Inverses f g} → Inverses[ inv ] f' g'
  → has-section[ inverses→from-has-section inv ] g'
inverses[]→from-has-section[] {f' = f'} inv' .section' = f'
inverses[]→from-has-section[] inv' .is-section' = Inverses[_].invr' inv'

inverses[]→to-has-retract[]
  : ∀ {f : Hom a b} {g : Hom b a}
  → ∀ {a' b'} {f' : Hom[ f ] a' b'} {g' : Hom[ g ] b' a'}
  → {inv : Inverses f g} → Inverses[ inv ] f' g'
  → has-retract[ inverses→to-has-retract inv ] f'
inverses[]→to-has-retract[] {g' = g'} inv' .retract' = g'
inverses[]→to-has-retract[] inv' .is-retract' = Inverses[_].invr' inv'

inverses[]→from-has-retract[]
  : ∀ {f : Hom a b} {g : Hom b a}
  → ∀ {a' b'} {f' : Hom[ f ] a' b'} {g' : Hom[ g ] b' a'}
  → {inv : Inverses f g} → Inverses[ inv ] f' g'
  → has-retract[ inverses→from-has-retract inv ] g'
inverses[]→from-has-retract[] {f' = f'} inv' .retract' = f'
inverses[]→from-has-retract[] inv' .is-retract' = Inverses[_].invl' inv'

iso[]→to-has-section[]
  : {f : a ≅ b} → (f' : a' ≅[ f ] b')
  → has-section[ iso→to-has-section f ] (f' .to')
iso[]→to-has-section[] f' .section' = f' .from'
iso[]→to-has-section[] f' .is-section' = f' .invl'

iso[]→from-has-section[]
  : {f : a ≅ b} → (f' : a' ≅[ f ] b')
  → has-section[ iso→from-has-section f ] (f' .from')
iso[]→from-has-section[] f' .section' = f' .to'
iso[]→from-has-section[] f' .is-section' = f' .invr'

iso[]→to-has-retract[]
  : {f : a ≅ b} → (f' : a' ≅[ f ] b')
  → has-retract[ iso→to-has-retract f ] (f' .to')
iso[]→to-has-retract[] f' .retract' = f' .from'
iso[]→to-has-retract[] f' .is-retract' = f' .invr'

iso[]→from-has-retract[]
  : {f : a ≅ b} → (f' : a' ≅[ f ] b')
  → has-retract[ iso→from-has-retract f ] (f' .from')
iso[]→from-has-retract[] f' .retract' = f' .to'
iso[]→from-has-retract[] f' .is-retract' = f' .invl'
```
