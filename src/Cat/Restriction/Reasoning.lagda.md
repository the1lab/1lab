<!--
```agda
open import Cat.Restriction.Base
open import Cat.Prelude

import Cat.Diagram.Idempotent
import Cat.Reasoning
```
-->

```agda
module Cat.Restriction.Reasoning
  {o ℓ} {C : Precategory o ℓ}
  (C-restrict : Restriction-category C)
  where
```

<!--
```agda
open Cat.Diagram.Idempotent C public
open Cat.Reasoning C public
open Restriction-category C-restrict public
```
-->

# Reasoning in restriction categories

This module provides some useful lemmas about restriction categories.
We begin by noting that for every $f$, $\restrict{f}$ is an [idempotent].

[idempotent]: Cat.Diagram.Idempotent.html

```agda
↓-idem : ∀ {x y} (f : Hom x y) → is-idempotent (f ↓)
↓-idem f =
  f ↓ ∘ f ↓   ≡˘⟨ ↓-smashr f f ⟩
  (f ∘ f ↓) ↓ ≡⟨ ap _↓ (↓-dom f) ⟩
  f ↓         ∎
```

Next, some useful lemmas about pre and postcomposition of a restriction
map.

```agda
↓-cancelr : ∀ {x y z} (f : Hom y z) (g : Hom x y) → (f ∘ g) ↓ ∘ g ↓ ≡ (f ∘ g) ↓
↓-cancelr f g =
  (f ∘ g) ↓ ∘ g ↓   ≡˘⟨ ↓-smashr g (f ∘ g) ⟩
  ((f ∘ g) ∘ g ↓) ↓ ≡⟨ ap _↓ (pullr (↓-dom g)) ⟩
  (f ∘ g) ↓         ∎


↓-cancell : ∀ {x y z} (f : Hom y z) (g : Hom x y) → g ↓ ∘ (f ∘ g) ↓ ≡ (f ∘ g) ↓
↓-cancell f g =
  g ↓ ∘ (f ∘ g) ↓  ≡⟨ ↓-comm g (f ∘ g) ⟩
  (f ∘ g) ↓ ∘ g ↓  ≡⟨ ↓-cancelr f g ⟩
  (f ∘ g) ↓        ∎
```

We can use these to show that $\restrict{(\restrict{f}g)} = \restrict{(f \circ g)}$,
which is somewhat hard to motivate, but ends up being a useful algebraic
manipulation.

```agda
↓-smashl : ∀ {x y z} (f : Hom y z) (g : Hom x y) → (f ↓ ∘ g) ↓ ≡ (f ∘ g) ↓
↓-smashl f g =
  ((f ↓) ∘ g) ↓     ≡⟨ ap _↓ (↓-swap f g) ⟩
  (g ∘ (f ∘ g) ↓) ↓ ≡⟨ ↓-smashr (f ∘ g) g ⟩
  g ↓ ∘ (f ∘ g) ↓   ≡⟨ ↓-cancell f g ⟩
  (f ∘ g) ↓ ∎

↓-smash : ∀ {x y z} (f : Hom x z) (g : Hom x y) → (f ↓ ∘ g ↓) ↓ ≡ f ↓ ∘ g ↓
↓-smash f g =
  (f ↓ ∘ g ↓) ↓ ≡⟨ ↓-smashl f (g ↓) ⟩
  (f ∘ g ↓) ↓   ≡⟨ ↓-smashr g f ⟩
  f ↓ ∘ g ↓ ∎
```

Next, we note that iterating $(-)downarrow$ does nothing.

```agda
↓-join : ∀ {x y} (f : Hom x y) → (f ↓) ↓ ≡ f ↓
↓-join f =
  (f ↓) ↓       ≡⟨ ap _↓ (sym (↓-idem f)) ⟩
  (f ↓ ∘ f ↓) ↓ ≡⟨ ↓-smashr f (f ↓) ⟩
  (f ↓) ↓ ∘ f ↓ ≡⟨ ↓-comm (f ↓) f ⟩
  f ↓ ∘ (f ↓) ↓ ≡⟨ ↓-dom (f ↓) ⟩
  f ↓ ∎
```

## Total morphisms

We say that a morphism $f : X \to Y$ in a restriction category is **total**
if its restriction $\restrict{f}$ is the identity morphism.

```agda
is-total : ∀ {x y} → Hom x y → Type _
is-total f = f ↓ ≡ id

record Total (x y : Ob) : Type ℓ where
  no-eta-equality
  field
    mor : Hom x y
    has-total : is-total mor

open Total public
```

Being total is a proposition, so the collection of total morphisms
forms a set.

```agda
is-total-is-prop : ∀ {x y} → (f : Hom x y) → is-prop (is-total f)
is-total-is-prop f = Hom-set _ _ _ _

Total-is-set : ∀ {x y} → is-set (Total x y)
```

<!--
```agda
Total-is-set = Iso→is-hlevel 2 eqv $
  Σ-is-hlevel 2 (Hom-set _ _) λ _ →
  Path-is-hlevel 2 (Hom-set _ _)
  where unquoteDecl eqv = declare-record-iso eqv (quote Total)

instance
  H-Level-Total : ∀ {x y} {n} → H-Level (Total x y) (suc (suc n))
  H-Level-Total = basic-instance 2 Total-is-set
```
-->


If $f$ is [[monic]], then it is a total morphism.

[monic]: Cat.Morphism.html#monos

```agda
monic→total : ∀ {x y} {f : Hom x y} → is-monic f → is-total f
monic→total {f = f} monic = monic (f ↓) id (↓-dom f ∙ sym (idr _))
```

As a corollary, every isomorphism is total.

```agda
invertible→total : ∀ {x y} {f : Hom x y} → is-invertible f → is-total f
invertible→total f-inv = monic→total (invertible→monic f-inv)
```

The identity morphism is total, as it is monic.

```agda
id-total : ∀ {x} → is-total (id {x})
id-total = monic→total id-monic
```

Total morphisms are closed under composition.

```agda
total-∘
  : ∀ {x y z} {f : Hom y z} {g : Hom x y}
  → is-total f → is-total g → is-total (f ∘ g)
total-∘ {f = f} {g = g} f-total g-total =
  (f ∘ g) ↓   ≡˘⟨ ↓-smashl f g ⟩
  (f ↓ ∘ g) ↓ ≡⟨ ap _↓ (eliml f-total) ⟩
  g ↓         ≡⟨ g-total ⟩
  id          ∎

_∘Total_ : ∀ {x y z} → Total y z → Total x y → Total x z
(f ∘Total g) .mor = f .mor ∘ g .mor
(f ∘Total g) .has-total = total-∘ (f .has-total) (g .has-total)
```

Furthermore, if $f \circ g$ is total, then $g$ must also be total.

```agda
total-cancell
  : ∀ {x y z} {f : Hom y z} {g : Hom x y}
  → is-total (f ∘ g) → is-total g
total-cancell {f = f} {g = g} fg-total =
  g ↓             ≡⟨ intror fg-total ⟩
  g ↓ ∘ (f ∘ g) ↓ ≡⟨ ↓-cancell f g ⟩
  (f ∘ g) ↓       ≡⟨ fg-total ⟩
  id ∎
```

If $f$ is total, then $\restrict{(fg)} = \restrict{g}$.

```agda
total-smashl
  : ∀ {x y z} {f : Hom y z} {g : Hom x y}
  → is-total f → (f ∘ g) ↓ ≡ g ↓
total-smashl {f = f} {g = g} f-total =
  (f ∘ g) ↓ ≡˘⟨ ↓-smashl f g ⟩
  (f ↓ ∘ g) ↓ ≡⟨ ap _↓ (eliml f-total) ⟩
  g ↓ ∎
```

## Restriction idempotents

We say that a morphism $f : X \to X$ is a **restriction idempotent** if
$\restrict{f} = f$.

```agda
is-restriction-idempotent : ∀ {x} → (f : Hom x x) → Type _
is-restriction-idempotent f = f ↓ ≡ f
```

As the name suggests, restriction idempotents are idempotents.

```agda
restriction-idempotent→idempotent
  : ∀ {x} {f : Hom x x}
  → is-restriction-idempotent f → is-idempotent f
restriction-idempotent→idempotent {f = f} f-dom =
  f ∘ f ≡⟨ ap (f ∘_) (sym f-dom) ⟩
  f ∘ f ↓ ≡⟨ ↓-dom f ⟩
  f ∎
```

Furthermore, every morphism $\restrict{f}$ is a restriction idempotent.

```agda
↓-restriction-idempotent : ∀ {x y} (f : Hom x y) → is-restriction-idempotent (f ↓)
↓-restriction-idempotent f = ↓-join f
```

If $f$ and $g$ are restriction idempotents, then they commute.

```agda
restriction-idem-comm
  : ∀ {x} {f g : Hom x x}
  → is-restriction-idempotent f → is-restriction-idempotent g
  → f ∘ g ≡ g ∘ f
restriction-idem-comm f-dom g-dom =
  ap₂ _∘_ (sym f-dom) (sym g-dom)
  ·· ↓-comm _ _
  ·· ap₂ _∘_ g-dom f-dom
```

## Restricted monics

A morphism $f : X \to Y$ is a **restricted monic** if for all
$g, h : A \to X$, $fg = fh$ implies that $\restrict{f}g = \restrict{f}h$.
Intuitively, this is the correct notion of monic for a partial function;
we cannot guarantee that $g$ and $h$ are equal if $fg = fh$, as $f$ may
diverge on some inputs where $g$ and $h$ disagree.

```agda
is-restricted-monic : ∀ {x y} → Hom x y → Type _
is-restricted-monic {x} {y} f =
  ∀ {a} → (g h : Hom a x) → f ∘ g ≡ f ∘ h → f ↓ ∘ g ≡ f ↓ ∘ h
```

If $f$ is a total restricted monic, then $f$ is monic.

```agda
restricted-monic+total→monic
  : ∀ {x y} {f : Hom x y}
  → is-restricted-monic f → is-total f
  → is-monic f
restricted-monic+total→monic {f = f} f-rmonic f-total g1 g2 p =
  g1       ≡⟨ introl f-total ⟩
  f ↓ ∘ g1 ≡⟨ f-rmonic g1 g2 p ⟩
  f ↓ ∘ g2 ≡⟨ eliml f-total ⟩
  g2 ∎
```

Restricted monics are closed under composition.

```agda
restricted-monic-∘
  : ∀ {x y z} {f : Hom y z} {g : Hom x y}
  → is-restricted-monic f → is-restricted-monic g
  → is-restricted-monic (f ∘ g)
restricted-monic-∘ {f = f} {g = g} f-rmonic g-rmonic h1 h2 p =
  (f ∘ g) ↓ ∘ h1         ≡⟨ pushl (sym (↓-cancell f g)) ⟩
  g ↓ ∘ (f ∘ g) ↓ ∘ h1   ≡⟨ g-rmonic _ _ g-lemma ⟩
  (g ↓) ∘ (f ∘ g) ↓ ∘ h2 ≡⟨ pulll (↓-cancell f g) ⟩
  (f ∘ g) ↓ ∘ h2 ∎
  where
    p-assoc : f ∘ g ∘ h1 ≡ f ∘ g ∘ h2
    p-assoc = assoc _ _ _ ·· p ·· sym (assoc _ _ _)

    g-lemma : g ∘ (f ∘ g) ↓ ∘ h1 ≡ g ∘ (f ∘ g) ↓ ∘ h2
    g-lemma =
      g ∘ (f ∘ g) ↓ ∘ h1 ≡⟨ extendl (sym (↓-swap f g)) ⟩
      f ↓ ∘ g ∘ h1       ≡⟨ f-rmonic _ _ p-assoc ⟩
      f ↓ ∘ g ∘ h2       ≡⟨ extendl (↓-swap f g) ⟩
      g ∘ (f ∘ g) ↓ ∘ h2 ∎
```

Furthermore, if $fg$ is a restricted monic and $f$ is total,
then $g$ is a restricted monic.

```agda
restricted-monic-cancell
  : ∀ {x y z} {f : Hom y z} {g : Hom x y}
  → is-restricted-monic (f ∘ g)
  → is-total f
  → is-restricted-monic g
restricted-monic-cancell {f = f} {g = g} fg-rmonic f-total h1 h2 p =
  g ↓ ∘ h1           ≡⟨ ap (_∘ h1) (sym (total-smashl f-total)) ⟩
  (f ∘ g) ↓ ∘ h1     ≡⟨ fg-rmonic h1 h2 (sym (assoc _ _ _) ·· ap (f ∘_) p ·· assoc _ _ _) ⟩
  (f ∘ g) ↓ ∘ h2     ≡⟨ ap (_∘ h2) (total-smashl f-total) ⟩
  g ↓ ∘ h2           ∎
```

## Restricted retracts

Let $r : X \to Y$ and $s : Y \to X$ be a pair of morphisms. The map
$r$ is a **restricted retract** of $s$ when $rs = \restrict{s}$.

```agda
_restricted-retract-of_ : ∀ {x y} (r : Hom x y) (s : Hom y x) → Type _
r restricted-retract-of s = r ∘ s ≡ s ↓

record has-restricted-retract {x y} (s : Hom y x) : Type ℓ where
  no-eta-equality
  field
    ↓-retract : Hom x y
    is-restricted-retract : ↓-retract restricted-retract-of s

open has-restricted-retract public
```

If $f$ is total and has a restricted retract, then it has a retract.

```agda
has-restricted-retract+total→has-retract
  : ∀ {x y} {f : Hom x y}
  → has-restricted-retract f → is-total f → has-retract f
has-restricted-retract+total→has-retract {f = f} f-sect f-total =
  make-retract (f-sect .↓-retract) $
    f-sect .↓-retract ∘ f ≡⟨ f-sect .is-restricted-retract ⟩
    f ↓                   ≡⟨ f-total ⟩
    id                    ∎
```

If $s$ has a restricted retract, then it is a restricted mono.

```agda
has-restricted-retract→restricted-monic
  : ∀ {x y} {f : Hom x y}
  → has-restricted-retract f
  → is-restricted-monic f
has-restricted-retract→restricted-monic {f = f} f-sect g1 g2 p =
  f ↓ ∘ g1 ≡⟨ pushl (sym $ f-sect .is-restricted-retract) ⟩
  f-sect .↓-retract ∘ f ∘ g1 ≡⟨ ap (f-sect .↓-retract ∘_) p ⟩
  f-sect .↓-retract ∘ f ∘ g2 ≡⟨ pulll (f-sect .is-restricted-retract) ⟩
  f ↓ ∘ g2 ∎
```

If $f$ and $g$ have restricted retracts, then so does $fg$.

```agda
restricted-retract-∘
  : ∀ {x y z} {f : Hom y z} {g : Hom x y}
  → has-restricted-retract f → has-restricted-retract g
  → has-restricted-retract (f ∘ g)
restricted-retract-∘ {f = f} {g = g} f-sect g-sect .↓-retract =
  g-sect .↓-retract ∘ f-sect .↓-retract
restricted-retract-∘ {f = f} {g = g} f-sect g-sect .is-restricted-retract =
  (g-sect .↓-retract ∘ f-sect .↓-retract) ∘ f ∘ g ≡⟨ pull-inner (f-sect .is-restricted-retract) ⟩
  g-sect .↓-retract ∘ f ↓ ∘ g                     ≡⟨ ap (g-sect .↓-retract ∘_) (↓-swap f g) ⟩
  g-sect .↓-retract ∘ g ∘ (f ∘ g) ↓               ≡⟨ pulll (g-sect .is-restricted-retract) ⟩
  g ↓ ∘ (f ∘ g) ↓                                 ≡⟨ ↓-cancell f g ⟩
  (f ∘ g) ↓                                       ∎
```


If $fg$ has a restricted retract and $f$ is total, then $g$ has a
restricted retract.

```agda
has-restricted-retract-cancell
  : ∀ {x y z} {f : Hom y z} {g : Hom x y}
  → has-restricted-retract (f ∘ g)
  → is-total f
  → has-restricted-retract g
has-restricted-retract-cancell {f = f} fg-sect f-total .↓-retract =
  fg-sect .↓-retract ∘ f
has-restricted-retract-cancell {f = f} {g = g} fg-sect f-total .is-restricted-retract =
  (fg-sect .↓-retract ∘ f) ∘ g ≡⟨ sym (assoc _ _ _) ∙ fg-sect .is-restricted-retract ⟩
  (f ∘ g) ↓                    ≡⟨ total-smashl f-total ⟩
  g ↓ ∎
```

## Restricted isomorphisms

Let $f : X \to Y$ and $g : Y \to X$ be a pair of morphisms. $f$ and $g$
are **restricted inverses** if $fg = \restrict{g}$ and
$gf = \restrict{f}$.

```agda
record restricted-inverses
  {x y} (f : Hom x y) (g : Hom y x)
  : Type ℓ where
  no-eta-equality
  field
    ↓-invl : f ∘ g ≡ g ↓
    ↓-invr : g ∘ f ≡ f ↓

open restricted-inverses

record is-restricted-invertible {x y} (f : Hom x y) : Type ℓ where
  no-eta-equality
  field
    ↓-inv : Hom y x
    ↓-inverses : restricted-inverses f ↓-inv

  open restricted-inverses ↓-inverses public

record _↓≅_ (x y : Ob) : Type ℓ where
  no-eta-equality
  field
    ↓-to : Hom x y
    ↓-from : Hom y x
    ↓-inverses : restricted-inverses ↓-to ↓-from

  open restricted-inverses ↓-inverses public

open _↓≅_ public
```

A given morphism is a has a unique restricted inverse.

```agda
restricted-inverses-is-prop
  : ∀ {x y} {f : Hom x y} {g : Hom y x}
  → is-prop (restricted-inverses f g)
restricted-inverses-is-prop x y i .↓-invl =
  Hom-set _ _ _ _ (x .↓-invl) (y .↓-invl) i
restricted-inverses-is-prop x y i .↓-invr =
  Hom-set _ _ _ _ (x .↓-invr) (y .↓-invr) i

is-restricted-invertible-is-prop
   : ∀ {x y} {f : Hom x y}
   → is-prop (is-restricted-invertible f)
is-restricted-invertible-is-prop {f = f} g h = p where
  module g = is-restricted-invertible g
  module h = is-restricted-invertible h

  g≡h : g.↓-inv ≡ h.↓-inv
  g≡h =
    g.↓-inv                                 ≡˘⟨ ↓-dom _ ⟩
    g.↓-inv ∘ g.↓-inv ↓                     ≡⟨ ap (g.↓-inv ∘_) (sym g.↓-invl) ⟩
    g.↓-inv ∘ f ∘ g.↓-inv                   ≡⟨ extendl (g.↓-invr ∙ sym h.↓-invr) ⟩
    h.↓-inv ∘ ⌜ f ⌝ ∘ g.↓-inv               ≡⟨ ap! (sym (↓-dom f) ∙ ap (f ∘_) (sym h.↓-invr)) ⟩
    h.↓-inv ∘ (f ∘ h.↓-inv ∘ f) ∘ g.↓-inv   ≡⟨ ap (h.↓-inv ∘_) (pullr (pullr g.↓-invl) ∙ pulll h.↓-invl) ⟩
    h.↓-inv ∘ h.↓-inv ↓ ∘ g.↓-inv ↓         ≡⟨ ap (h.↓-inv ∘_) (↓-comm _ _) ⟩
    h.↓-inv ∘ g.↓-inv ↓ ∘ h.↓-inv ↓         ≡⟨ ap (h.↓-inv ∘_) (pushl (sym g.↓-invl) ∙ pushr (pushr (sym h.↓-invl))) ⟩
    h.↓-inv ∘ ⌜ f ∘ g.↓-inv ∘ f ⌝ ∘ h.↓-inv ≡⟨ ap! (ap (f ∘_) g.↓-invr ∙ ↓-dom f) ⟩
    h.↓-inv ∘ f ∘ h.↓-inv                   ≡⟨ ap (h.↓-inv ∘_) (h.↓-invl)  ⟩
    h.↓-inv ∘ h.↓-inv ↓                     ≡⟨ ↓-dom _ ⟩
    h.↓-inv                                 ∎

  p : g ≡ h
  p i .is-restricted-invertible.↓-inv = g≡h i
  p i .is-restricted-invertible.↓-inverses =
    is-prop→pathp (λ i → restricted-inverses-is-prop {f = f} {g = g≡h i})
      g.↓-inverses h.↓-inverses i
```

If $f$ and $g$ are both total and restricted inverses, then they are inverses.

```agda
restricted-inverses+total→inverses
  : ∀ {x y} {f : Hom x y} {g : Hom y x}
  → restricted-inverses f g
  → is-total f
  → is-total g
  → Inverses f g
restricted-inverses+total→inverses {f = f} {g = g} fg-inv f-total g-total = record
    { invl = fg-inv .↓-invl ∙ g-total
    ; invr = fg-inv .↓-invr ∙ f-total
    }
```

## Refining morphisms

Let $\cC$ be a restriction category, and $f, g : \cC(X,Y)$. We say that
$g$ **refines** $f$ if $g$ agrees with $f$ when restricted to the domain of
$f$.

```agda
_≤_ : ∀ {x y} → Hom x y → Hom x y → Type ℓ
f ≤ g = g ∘ f ↓ ≡ f
```

The refinement relation is reflexive, transitive, and anti-symmetric.

```agda
≤-refl : ∀ {x y} {f : Hom x y} → f ≤ f
≤-refl {f = f} = ↓-dom f

≤-trans : ∀ {x y} {f g h : Hom x y} → f ≤ g → g ≤ h → f ≤ h
≤-trans {f = f} {g = g} {h = h} p q =
  h ∘ ⌜ f ⌝ ↓       ≡⟨ ap! (sym p) ⟩
  h ∘ (g ∘ (f ↓)) ↓ ≡⟨ ap (h ∘_) (↓-smashr f g) ⟩
  h ∘ g ↓ ∘ f ↓     ≡⟨ pulll q ⟩
  g ∘ f ↓           ≡⟨ p ⟩
  f                 ∎

≤-antisym : ∀ {x y} {f g : Hom x y} → f ≤ g → g ≤ f → f ≡ g
≤-antisym {f = f} {g = g} p q =
  f             ≡⟨ sym p ⟩
  g ∘ f ↓       ≡⟨ pushl (sym q) ⟩
  f ∘ g ↓ ∘ f ↓ ≡⟨ ap (f ∘_) (↓-comm g f) ⟩
  f ∘ f ↓ ∘ g ↓ ≡⟨ pulll (↓-dom f) ⟩
  f ∘ (g ↓)     ≡⟨ q ⟩
  g ∎
```

Furthermore, composition preserves refinement.

```agda
∘-preserves-≤
  : ∀ {x y z} {f g : Hom y z} {h i : Hom x y}
  → f ≤ g → h ≤ i → (f ∘ h) ≤ (g ∘ i)
∘-preserves-≤ {f = f} {g = g} {h = h} {i = i} p q =
  (g ∘ i) ∘ ⌜ f ∘ h ⌝ ↓          ≡⟨ ap! (pushr (sym q)) ⟩
  (g ∘ i) ∘ ((f ∘ i) ∘ (h ↓)) ↓  ≡⟨ ap ((g ∘ i) ∘_) (↓-smashr h (f ∘ i)) ⟩
  (g ∘ i) ∘ (f ∘ i) ↓ ∘ h ↓      ≡⟨ extendr (extendl (sym (↓-swap f i))) ⟩
  (g ∘ f ↓) ∘ (i ∘ h ↓)          ≡⟨ ap₂ _∘_ p q ⟩
  f ∘ h                          ∎
```
