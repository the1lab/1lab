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
open Cat.Displayed.Reasoning ℰ
open Cat.Reasoning ℬ

private variable
  ℓi : Level
  Ix : Type ℓi
  a b c d : Ob
  aᵢ bᵢ cᵢ : Ix → Ob
  f g h : Hom a b
  a' b' c' : Ob[ a ]
  aᵢ'  bᵢ' cᵢ' : (ix : Ix) → Ob[ bᵢ ix ]
  f' g' h' : Hom[ f ] a' b'
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

## Weak monos {defines="weak-monomorphism weakly-monic"}

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
  ∀ {c c'} {g h : Hom c a}
  → (g' : Hom[ g ] c' a') (h' : Hom[ h ] c' a')
  → (p : g ≡ h)
  → f' ∘' g' ≡[ ap (f ∘_) p ] f' ∘' h'
  → g' ≡[ p ] h'

is-weak-monic-is-prop
  : ∀ {a' : Ob[ a ]} {b' : Ob[ b ]} {f : Hom a b}
  → (f' : Hom[ f ] a' b')
  → is-prop (is-weak-monic f')
is-weak-monic-is-prop f' = hlevel 1

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

Weak monomorphisms are closed under composition, and every displayed
monomorphism is weakly monic.

```agda
∘-is-weak-monic
  : is-weak-monic f'
  → is-weak-monic g'
  → is-weak-monic (f' ∘' g')
∘-is-weak-monic {f' = f'} {g' = g'} f'-weak-monic g'-weak-monic h' k' p p' =
  g'-weak-monic h' k' p $
  f'-weak-monic (g' ∘' h') (g' ∘' k') (ap₂ _∘_ refl p) $ begin[]
    f' ∘' g' ∘' h'   ≡[]⟨ assoc' f' g' h' ⟩
    (f' ∘' g') ∘' h' ≡[]⟨ p' ⟩
    (f' ∘' g') ∘' k' ≡[]˘⟨ assoc' f' g' k' ⟩
    f' ∘' g' ∘' k'   ∎[]

is-monic[]→is-weak-monic
  : {f-monic : is-monic f}
  → is-monic[ f-monic ] f'
  → is-weak-monic f'
is-monic[]→is-weak-monic f'-monic g' h' p p' =
  cast[] $ f'-monic g' h' (ap₂ _∘_ refl p) p'
```

If $f' \circ g'$ is weakly monic, then so is $g'$.

```agda
weak-monic-cancell
  : is-weak-monic (f' ∘' g')
  → is-weak-monic g'
weak-monic-cancell {f' = f'} {g' = g'} fg-weak-monic h' k' p p' =
  fg-weak-monic h' k' p (extendr' _ p')
```

Moreover, postcomposition with a weak monomorphism is an [[embedding]].
This suggests that weak monomorphisms are the "right" notion of
monomorphisms in displayed categories.

```agda
weak-monic-postcomp-embedding
  : {f : Hom b c} {g : Hom a b}
  → {f' : Hom[ f ] b' c'}
  → is-weak-monic f'
  → is-embedding {A = Hom[ g ] a' b'} (f' ∘'_)
weak-monic-postcomp-embedding {f' = f'} f'-weak-monic =
  injective→is-embedding (hlevel 2) (f' ∘'_) λ {g'} {h'} → f'-weak-monic g' h' refl
```

### Jointly weak monos

We can generalize the notion of weak monomorphisms to families of morphisms, which
yields a displayed version of a [[jointly monic family]].

:::{.definition #jointly-weak-monic-family}
A family of displayed morphisms $f_{i}' : A' \to_{f_{i}} B_{i}'$ is *jointly monic*
if for all $g', g'' : X' \to_{g} A'$, $g' = g''$ if $f_{i}' \circ g' = f_{i} \circ g''$
for all $i : I$.
:::

```agda
is-jointly-weak-monic
  : {fᵢ : (ix : Ix) → Hom a (bᵢ ix)}
  → (fᵢ' : (ix : Ix) → Hom[ fᵢ ix ] a' (bᵢ' ix))
  → Type _
is-jointly-weak-monic {a = a} {a' = a'} {fᵢ = fᵢ} fᵢ' =
  ∀ {x x'} {g h : Hom x a}
  → (g' : Hom[ g ] x' a') (h' : Hom[ h ] x' a')
  → (p : g ≡ h)
  → (∀ ix → fᵢ' ix ∘' g' ≡[ ap (fᵢ ix ∘_) p ] fᵢ' ix ∘' h')
  → g' ≡[ p ] h'
```

Jointly weak monic families are closed under precomposition
with weak monos.

```agda
∘-is-jointly-weak-monic
  : {fᵢ : (ix : Ix) → Hom a (bᵢ ix)}
  → {fᵢ' : (ix : Ix) → Hom[ fᵢ ix ] a' (bᵢ' ix)}
  → is-jointly-weak-monic fᵢ'
  → is-weak-monic g'
  → is-jointly-weak-monic (λ ix → fᵢ' ix ∘' g')
∘-is-jointly-weak-monic {g' = g'} {fᵢ' = fᵢ'} fᵢ'-joint-mono g'-joint-mono h' h'' p p' =
  g'-joint-mono h' h'' p $
  fᵢ'-joint-mono (g' ∘' h') (g' ∘' h'') (ap₂ _∘_ refl p) λ ix → begin[]
    fᵢ' ix ∘' g' ∘' h'    ≡[]⟨ assoc' (fᵢ' ix) g' h' ⟩
    (fᵢ' ix ∘' g') ∘' h'  ≡[]⟨ p' ix ⟩
    (fᵢ' ix ∘' g') ∘' h'' ≡[]˘⟨ assoc' (fᵢ' ix) g' h'' ⟩
    fᵢ' ix ∘' g' ∘' h''   ∎[]
```

Similarly, if $f_{i}' \circ g'$ is a jointly weak monic family, then
$g'$ must be a weak mono.

```agda
jointly-weak-monic-cancell
  : {fᵢ : (ix : Ix) → Hom a (bᵢ ix)}
  → {fᵢ' : (ix : Ix) → Hom[ fᵢ ix ] a' (bᵢ' ix)}
  → is-jointly-weak-monic (λ ix → fᵢ' ix ∘' g')
  → is-weak-monic g'
jointly-weak-monic-cancell fᵢ'-joint-mono h' h'' p p' =
  fᵢ'-joint-mono h' h'' p λ _ → extendr' (ap₂ _∘_ refl p) p'
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
  ∀ {c c'} {g h : Hom b c}
  → (g' : Hom[ g ] b' c') (h' : Hom[ h ] b' c')
  → (p : g ≡ h)
  → g' ∘' f' ≡[ ap (_∘ f) p ] h' ∘' f'
  → g' ≡[ p ] h'

is-weak-epic-is-prop
  : ∀ {a' : Ob[ a ]} {b' : Ob[ b ]} {f : Hom a b}
  → (f' : Hom[ f ] a' b')
  → is-prop (is-weak-epic f')
is-weak-epic-is-prop f' = hlevel 1

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
```

<!--
```agda
open _≅[_]_ public
{-# INLINE _≅[_]_.constructor #-}
```
-->

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
{-# INLINE make-iso[_] #-}
make-iso[ inv ] f' g' p q = record { to' = f' ; from' = g' ; inverses' = record { invl' = p ; invr' = q }}

make-invertible[_]
  : ∀ {a b a' b'} {f : Hom a b} {f' : Hom[ f ] a' b'}
  → (f-inv : is-invertible f)
  → (f-inv' : Hom[ is-invertible.inv f-inv ] b' a')
  → f' ∘' f-inv' ≡[ is-invertible.invl f-inv ] id'
  → f-inv' ∘' f' ≡[ is-invertible.invr f-inv ] id'
  → is-invertible[ f-inv ] f'
make-invertible[ f-inv ] f-inv' p q .is-invertible[_].inv' = f-inv'
make-invertible[ f-inv ] f-inv' p q .is-invertible[_].inverses' .Inverses[_].invl' = p
make-invertible[ f-inv ] f-inv' p q .is-invertible[_].inverses' .Inverses[_].invr' = q

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
invertible[]→iso[] {f' = f'} i = make-iso[ _ ] f'
  (is-invertible[_].inv' i)
  (is-invertible[_].invl' i)
  (is-invertible[_].invr' i)

iso[]→invertible[]
  : ∀ {a b a' b'}
  → {i : a ≅ b}
  → (i' : a' ≅[ i ] b')
  → is-invertible[ iso→invertible i ] (i' .to')
iso[]→invertible[] {i = i} i' =
  make-invertible[ (iso→invertible i) ] (i' .from') (i' .invl') (i' .invr')

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

_Iso[]⁻¹
  : ∀ {a b a' b'} {i : a ≅ b}
  → a' ≅[ i ] b'
  → b' ≅[ i Iso⁻¹ ] a'
(i' Iso[]⁻¹) .to' = i' .from'
(i' Iso[]⁻¹) .from' = i' .to'
(i' Iso[]⁻¹) .inverses' .Inverses[_].invl' = i' .invr'
(i' Iso[]⁻¹) .inverses' .Inverses[_].invr' = i' .invl'
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

module _
  {f : Hom a b} {f' : Hom[ f ] a' b'}
  {f-inv : is-invertible f}
  (f'-inv : is-invertible[ f-inv ] f')
  where
  private module f' = is-invertible[_] f'-inv

  invertible[]→to-has-section[] : has-section[ invertible→to-has-section f-inv ] f'
  invertible[]→to-has-section[] .section' = f'.inv'
  invertible[]→to-has-section[] .is-section' = f'.invl'

  invertible[]→from-has-section[] : has-section[ invertible→from-has-section f-inv ] f'.inv'
  invertible[]→from-has-section[] .section' = f'
  invertible[]→from-has-section[] .is-section' = f'.invr'

  invertible[]→to-has-retract[] : has-retract[ invertible→to-has-retract f-inv ] f'
  invertible[]→to-has-retract[] .retract' = f'.inv'
  invertible[]→to-has-retract[] .is-retract' = f'.invr'

  invertible[]→from-has-retract[] : has-retract[ invertible→from-has-retract f-inv ] f'.inv'
  invertible[]→from-has-retract[] .retract' = f'
  invertible[]→from-has-retract[] .is-retract' = f'.invl'

  invertible[]→monic[] : is-monic[ invertible→monic f-inv ] f'
  invertible[]→monic[] g' h' p p' =
    cast[] $ introl[] _ f'.invr' ∙[] extendr[] _ p' ∙[] eliml[] _ f'.invr'


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

<!--
```agda
module _
  {f : Hom a b} {f' : Hom[ f ] a' b'}
  {f-section : has-section f}
  (f-section' : has-section[ f-section ] f')
  where abstract
  private
    module f = has-section f-section
    module f' = has-section[_] f-section'

  pre-section'
    : ∀ {h₁ : Hom b c} {h₂ : Hom a c}
    → {p : h₁ ∘ f ≡ h₂} {q : h₁ ≡ h₂ ∘ f.section}
    → {h₁' : Hom[ h₁ ] b' c'} {h₂' : Hom[ h₂ ] a' c'}
    → h₁' ∘' f' ≡[ p ] h₂'
    → h₁' ≡[ q ] h₂' ∘' f'.section'
  pre-section' {p = p} {q = q} {h₁' = h₁'} {h₂' = h₂'} p' =
    symP (rswizzle' (sym p) f.is-section (symP p') f'.is-section')

  pre-section[]
    : ∀ {h₁ : Hom b c} {h₂ : Hom a c}
    → {p : h₁ ∘ f ≡ h₂}
    → {h₁' : Hom[ h₁ ] b' c'} {h₂' : Hom[ h₂ ] a' c'}
    → h₁' ∘' f' ≡[ p ] h₂'
    → h₁' ≡[ pre-section f-section p ] h₂' ∘' f'.section'
  pre-section[] = pre-section'

  post-section'
    : ∀ {h₁ : Hom c b} {h₂ : Hom c a}
    → {p : f.section ∘ h₁ ≡ h₂} {q : h₁ ≡ f ∘ h₂}
    → {h₁' : Hom[ h₁ ] c' b'} {h₂' : Hom[ h₂ ] c' a'}
    → f'.section' ∘' h₁' ≡[ p ] h₂'
    → h₁' ≡[ q ] f' ∘' h₂'
  post-section' {p = p} {q = q} {h₁' = h₁'} {h₂' = h₂'} p' =
    symP (lswizzle' (sym p) f.is-section (symP p') f'.is-section')

  post-section[]
    : ∀ {h₁ : Hom c b} {h₂ : Hom c a}
    → {p : f.section ∘ h₁ ≡ h₂}
    → {h₁' : Hom[ h₁ ] c' b'} {h₂' : Hom[ h₂ ] c' a'}
    → f'.section' ∘' h₁' ≡[ p ] h₂'
    → h₁' ≡[ post-section f-section p ] f' ∘' h₂'
  post-section[] = post-section'
```
-->
