<!--
```agda
open import Cat.Functor.Subcategory
open import Cat.Displayed.Total
open import Cat.Prelude

open import Order.Base
open import Order.DCPO
open import Order.Diagram.Lub

import Order.DCPO.Reasoning as DCPO
```
-->

```agda
module Order.DCPO.Morphism where
```

<!--
```agda
```
-->

# Reasoning with Scott-continuous functions

This module exposes a better API for working with Scott-continuous
functions, and also proves a collection of useful lemmas.

```agda
module Scott {o ℓ} {D E : DCPO o ℓ} (f : DCPOs.Hom D E) where
  private
    module D = DCPO D
    module E = DCPO E

  mono : Posets.Hom D.poset E.poset
  mono = Subcat-hom.hom f

  hom : D.Ob → E.Ob
  hom x = Total-hom.hom mono x

  monotone : ∀ x y → x D.≤ y → hom x E.≤ hom y
  monotone = Total-hom.preserves mono

  opaque
    pres-lub
      : ∀ {Ix} (s : Ix → D.Ob) → is-directed-family D.poset s
      → ∀ x → D.is-lub s x → E.is-lub (hom ⊙ s) (hom x)
    pres-lub = Subcat-hom.witness f

    directed
      : ∀ {Ix} {s : Ix → D.Ob} → is-directed-family D.poset s
      → is-directed-family E.poset (hom ⊙ s)
    directed dir = monotone∘directed (Subcat-hom.hom f) dir

    pres-⋃
      : ∀ {Ix} (s : Ix → D.Ob) → (dir : is-directed-family D.poset s)
      → hom (D.⋃ s dir) ≡ E.⋃ (hom ⊙ s) (directed dir)
    pres-⋃ s dir =
      E.≤-antisym
        (is-lub.least (pres-lub s dir (D.⋃ s dir) (D.⋃.has-lub s dir))
          (E.⋃ (hom ⊙ s) (directed dir))
          (E.⋃.fam≤lub (hom ⊙ s) (directed dir)))
        (E.⋃.least (hom ⊙ s) (directed dir) (hom (D.⋃ s dir)) λ i →
          monotone (s i) (D.⋃ s dir) (D.⋃.fam≤lub s dir i))
```

<!--
```agda
module _ {o ℓ} {D E : DCPO o ℓ} where
  private
    module D = DCPO D
    module E = DCPO E
  open Total-hom

  scott-path
    : ∀ {f g : DCPOs.Hom D E}
    → (∀ x → Scott.hom f x ≡ Scott.hom g x)
    → f ≡ g
  scott-path p =
    Subcat-hom-path $
    total-hom-path _ (funext p) $
    is-prop→pathp (λ i → is-monotone-is-prop (λ x → p x i) D.poset-on E.poset-on) _ _
```
-->

Recall that every Scott-continuous function from a DCPO is monotone. This
allows for a nicer API for constructing Scott-continuous functions.

```agda
  to-scott
    : (f : D.Ob → E.Ob)
    → (∀ {Ix} (s : Ix → D.Ob) → (dir : is-directed-family D.poset s)
       → ∀ x → is-lub D.poset s x → is-lub E.poset (f ⊙ s) (f x))
    → DCPOs.Hom D E
  to-scott f pres =
    sub-hom (total-hom f (dcpo+scott→monotone D.has-dcpo f pres)) pres
```

Let $D$ and $E$ be a pair of DCPOs. If $f : D \to E$ is monotone, and
$f (\bigcup s) \lsq \bigcup fs$ for every directed family $s$, then
$f$ is Scott-continuous.

```agda
  monotone→is-scott-continuous
    : (f : Posets.Hom D.poset E.poset)
    → (∀ {Ix} (s : Ix → D.Ob) → (fam : is-directed-family D.poset s)
     → f .hom (D.⋃ s fam) E.≤ E.⋃ (f .hom ⊙ s) (monotone∘directed f fam))
    → is-scott-continuous f
  monotone→is-scott-continuous f pres s dir x x-lub .is-lub.fam≤lub i =
    f .preserves _ _ (is-lub.fam≤lub x-lub i)
  monotone→is-scott-continuous f pres s dir x x-lub .is-lub.least y le =
    f .hom x           E.≤⟨ f .preserves _ _ (is-lub.least x-lub (D.⋃ s dir) (D.⋃.fam≤lub _ _)) ⟩
    f .hom (D.⋃ s dir) E.≤⟨ pres s dir ⟩
    E.⋃ (f .hom ⊙ s) _ E.≤⟨ E.⋃.least _ _ y le ⟩
    y E.≤∎
```
