<!--
```agda
-- Required to get pathp in DCPO-on to go through.
{-# OPTIONS --lossy-unification #-}
open import Data.Bool

open import Cat.Displayed.Univalence.Thin
open import Cat.Displayed.Total
open import Cat.Prelude

open import Order.Base
open import Order.Instances.Props

import Cat.Reasoning
import Order.Reasoning
open import Order.Diagram.Lub
```
-->

```agda
module Order.DCPO where
```

<!--
```agda
open Total-hom

private variable
  o ℓ ℓ' : Level
  Ix A B : Type o
```
-->

# Directed-Complete Partial Orders

Let $(P, \le)$ be a [partial order]. A family of elements $f : I \to P$ is
a **semi-directed family** if for every $i, j$, there merely exists
some $k$ such $f i \le f k$ and $f j \le f k$. A semidirected family
$f : I \to P$ is a **directed family** when $I$ is merely inhabited.

[partial order]: Order.Base.html

```agda
module _ {o ℓ} (P : Poset o ℓ) where
  open Order.Reasoning P

  is-semidirected-family : ∀ {Ix : Type o} → (Ix → Ob) → Type _
  is-semidirected-family {Ix = Ix} f = ∀ i j → ∃[ k ∈ Ix ] (f i ≤ f k × f j ≤ f k)

  record is-directed-family {Ix : Type o} (f : Ix → Ob) : Type (o ⊔ ℓ) where
    no-eta-equality
    field
      elt : ∥ Ix ∥
      semidirected : is-semidirected-family f

```

The poset $(P, \le)$ is a **directed-complete partial order**, or DCPO,
if it has [least upper bounds] of all directed families.

[least upper bounds]: Order.Diagram.Lub.html

```agda
  record is-dcpo : Type (lsuc o ⊔ ℓ) where
    no-eta-equality
    field
      directed-lubs
        : ∀ {Ix : Type o} (f : Ix → Ob) → is-directed-family f → Lub P f

    module ⋃ {Ix : Type o} (f : Ix → Ob) (dir : is-directed-family f) =
      Lub (directed-lubs f dir)

    open ⋃ renaming (lub to ⋃) public
```

Note that being a DCPO is a property of a poset, as least upper bounds
are unique.

<!--
```agda
module _ {o ℓ} {P : Poset o ℓ} where
  open Order.Reasoning P
  open is-dcpo
```
-->

```agda
  is-dcpo-is-prop : is-prop (is-dcpo P)
  is-dcpo-is-prop = Iso→is-hlevel 1 eqv $
    Π-is-hlevel′ 1 λ _ →
    Π-is-hlevel² 1 λ _ _ → Lub-is-prop P
    where unquoteDecl eqv = declare-record-iso eqv (quote is-dcpo) 
```

<!--
```agda
record DCPO-on {o} (ℓ : Level) (A : Type o) : Type (lsuc (o ⊔ ℓ)) where
  no-eta-equality
  field
    poset-on : Poset-on ℓ A
  open Poset-on poset-on public

  poset : Poset o ℓ
  poset = el A has-is-set , poset-on

  field
    has-dcpo : is-dcpo (el A has-is-set , poset-on)
  open is-dcpo has-dcpo public


DCPO-on-pathp
  : ∀ {A B : Type o}
  → {A-dcpo : DCPO-on ℓ A} {B-dcpo : DCPO-on ℓ B}
  → (p : A ≡ B)
  → PathP (λ i → p i → p i → Type ℓ) (DCPO-on._≤_ A-dcpo) (DCPO-on._≤_ B-dcpo)
  → PathP (λ i → DCPO-on ℓ (p i)) A-dcpo B-dcpo
DCPO-on-pathp {o = o} {ℓ = ℓ} {A-dcpo = A-dcpo} {B-dcpo} p q = dcpo-path where
  module A = DCPO-on A-dcpo
  module B = DCPO-on B-dcpo

  abstract
    on-path : PathP (λ i → Poset-on ℓ (p i)) A.poset-on B.poset-on
    on-path = Poset-on-pathp p q

  poset-line : I → Poset o ℓ
  poset-line i = el (p i) (Poset-on.has-is-set (on-path i)) , on-path i

  dcpo-path : PathP (λ i → DCPO-on ℓ (p i)) A-dcpo B-dcpo
  dcpo-path i .DCPO-on.poset-on = on-path i
  dcpo-path i .DCPO-on.has-dcpo =
    is-prop→pathp
      (λ i → is-dcpo-is-prop {P = poset-line i})
      A.has-dcpo B.has-dcpo i

DCPO-on-path
  : ∀ {A : Type o}
  → {P Q : DCPO-on ℓ A}
  → (∀ x y → DCPO-on._≤_ P x y ≡ DCPO-on._≤_ Q x y)
  → P ≡ Q
DCPO-on-path p = DCPO-on-pathp refl (funext λ x → funext λ y → p x y)

open is-directed-family
```
-->

# Scott-Continuous Maps

Let $(P, \le, \bigcup)$ and $(Q, \lsq, \bigsqcup)$ be a pair of DCPOs.
A function $f : P \to Q$ is **Scott-continuous** if it preserves all
directed least upper bounds.

```agda
record is-scott-continuous
  {A B : Type o}
  (f : A → B) (A-dcpo : DCPO-on ℓ A) (B-dcpo : DCPO-on ℓ B)
  : Type (lsuc o ⊔ ℓ)
  where
  private
    module A = DCPO-on A-dcpo
    module B = DCPO-on B-dcpo
  field
    pres-lub
      : ∀ {Ix} (s : Ix → A) (fam : is-directed-family A.poset s)
      → ∀ x → is-lub A.poset s x → is-lub B.poset (f ⊙ s) (f x)

open is-scott-continuous
open DCPO-on
```



Note that being Scott-continuous is a property of a function, as being
a least upper bound is also a proposition.

```agda
is-scott-continuous-is-prop
  : ∀ {A B : Type o}
  → (f : A → B) → (A-dcpo : DCPO-on ℓ A) → (B-dcpo : DCPO-on ℓ B)
  → is-prop (is-scott-continuous f A-dcpo B-dcpo)
is-scott-continuous-is-prop f A-dcpo B-dcpo =
  Iso→is-hlevel 1 eqv $
  Π-is-hlevel′ 1 λ _ →
  Π-is-hlevel³ 1 λ _ _ _ → Π-is-hlevel 1 λ _ _ _ →
  is-lub-is-prop (poset B-dcpo) _ _
  where unquoteDecl eqv = declare-record-iso eqv (quote is-scott-continuous) 
```

Every Scott-continuous function is monotone. Let $(P, \le, \bigcup)$ and
$(Q, \lsq, \bigsqcup)$ be a pair of DCPOs, let $f : P \to Q$ be a
Scott-continuous function, and let $x \le y$. We can then construct
a directed family $s : \rm{Bool} \to P$ with $s(true) = x$ and
$s(false) = y$. Note that $y$ is the least upper bound of this family,
so $f(y)$ must be an upper bound of $f \circ s$ in $Q$. From this,
we can deduce that $f(x) \lsq f(y)$.

```agda
scott→monotone
  : ∀ {A B : Type o}
  → {f : A → B} {A-dcpo : DCPO-on ℓ A} {B-dcpo : DCPO-on ℓ B}
  → is-scott-continuous f A-dcpo B-dcpo
  → is-monotone f (poset-on A-dcpo) (poset-on B-dcpo)
scott→monotone {A = A} {B} {f} {A-dcpo} {B-dcpo} scott x y p =
  is-lub.fam≤lub fs-lub (lift true)
  where
    module A = DCPO-on A-dcpo
    module B = DCPO-on B-dcpo

    s : Lift _ Bool → A
    s (lift b) = if b then x else y

    sx≤sfalse : ∀ b → s b A.≤ s (lift false)
    sx≤sfalse (lift true) = p
    sx≤sfalse (lift false) = A.≤-refl

    s-directed : is-directed-family A.poset s
    s-directed .elt =
      inc (lift true)
    s-directed .semidirected i j =
      inc (lift false , sx≤sfalse _ , sx≤sfalse _)

    s-lub : is-lub A.poset s y
    s-lub .is-lub.fam≤lub = sx≤sfalse
    s-lub .is-lub.least z lt = lt (lift false)

    fs-lub : is-lub B.poset (f ⊙ s) (f y)
    fs-lub = scott .pres-lub s s-directed y s-lub
```

Next, a small little lemma; if $f : P \to Q$ is monotone and $s : I \to P$
is a directed family, then $fs : I \to Q$ is also a directed family.

```agda
monotone∘directed
  : ∀ {Ix : Type o} {P Q : Poset o ℓ}
  → {f : ∣ P .fst ∣ → ∣ Q .fst ∣} {s : Ix → ∣ P .fst ∣}
  → is-monotone f (P .snd) (Q .snd)
  → is-directed-family P s
  → is-directed-family Q (f ⊙ s)
monotone∘directed mono fam .elt = fam .elt
monotone∘directed mono fam .is-directed-family.semidirected i j =
  ∥-∥-map (Σ-map₂ (×-map (mono _ _) (mono _ _)))
    (fam .semidirected i j)
```

<!--
```agda
scott∘directed
  : ∀ {Ix : Type o}
  → {A B : Type o}{A-dcpo : DCPO-on ℓ A} {B-dcpo : DCPO-on ℓ B}
  → {f : A → B} {s : Ix → A}
  → is-scott-continuous f A-dcpo B-dcpo
  → is-directed-family (DCPO-on.poset A-dcpo) s
  → is-directed-family (DCPO-on.poset B-dcpo) (f ⊙ s)
scott∘directed scott dir = monotone∘directed (scott→monotone scott) dir

scott-⋃
  : ∀ {A B : Type o} {A-dcpo : DCPO-on ℓ A} {B-dcpo : DCPO-on ℓ B}
  → (let module A = DCPO-on A-dcpo) (let module B = DCPO-on B-dcpo)
  → {f : A → B}
  → (scott : is-scott-continuous f A-dcpo B-dcpo)
  → ∀ (s : Ix → A) (dir : is-directed-family A.poset s)
  → f (A.⋃ s dir) ≡ B.⋃ (f ⊙ s) (scott∘directed scott dir)
scott-⋃ {A-dcpo = A-dcpo} {B-dcpo = B-dcpo} scott s dir =
  B.≤-antisym
    (is-lub.least (scott .pres-lub s dir _ (A.⋃.has-lub s dir)) _ (B.⋃.fam≤lub _ _))
    (B.⋃.least _ _ _ λ ix → scott→monotone scott _ _ (A.⋃.fam≤lub _ _ ix))
  where
    module A = DCPO-on A-dcpo
    module B = DCPO-on B-dcpo
```
-->

If $f : P \to Q$ is monotone, and $f (\bigcup s) \lsq \bigcup fs$ for
every directed family $s$, then $f$ is Scott-continuous.

```agda
monotone→scott
  : ∀ {A B : Type o}
  → {f : A → B} {A-dcpo : DCPO-on ℓ A} {B-dcpo : DCPO-on ℓ B}
  → (let module A = DCPO-on A-dcpo) (let module B = DCPO-on B-dcpo)
  → (mono : is-monotone f A.poset-on B.poset-on)
  → (∀ {Ix} (s : Ix → A) → (fam : is-directed-family A.poset s)
     → f (A.⋃ s fam) B.≤ B.⋃ (f ⊙ s) (monotone∘directed mono fam))
  → is-scott-continuous f A-dcpo B-dcpo
monotone→scott {f = f} {A-dcpo} {B-dcpo} mono pres .pres-lub s fam x x-lub =
  fx-lub where
  module A = DCPO-on A-dcpo
  module B = DCPO-on B-dcpo
  open is-lub

  fx-lub : is-lub B.poset (f ⊙ s) (f x)
  fx-lub .fam≤lub ix =
    mono _ _ (x-lub .fam≤lub ix)
  fx-lub .least z lt =
    B.≤-trans (mono _ _ (x-lub .least (A.⋃ s fam) (A.⋃.fam≤lub _ _))) $
    B.≤-trans (pres s fam)
    (B.⋃.least _ _ z lt)
```

The identity function is Scott-continuous.

```agda
scott-id
  : ∀ {A : Type o} {A-dcpo : DCPO-on ℓ A}
  → is-scott-continuous (λ x → x) A-dcpo A-dcpo
scott-id .pres-lub s fam x lub = lub
```

```agda
scott-∘
  : ∀ {A B C : Type o}
  → {A-dcpo : DCPO-on ℓ A} {B-dcpo : DCPO-on ℓ B} {C-dcpo : DCPO-on ℓ C}
  → {f : B → C} {g : A → B}
  → is-scott-continuous f B-dcpo C-dcpo
  → is-scott-continuous g A-dcpo B-dcpo
  → is-scott-continuous (f ⊙ g) A-dcpo C-dcpo
scott-∘ {f = f} {g = g} f-scott g-scott .pres-lub s fam x lub =
  f-scott .pres-lub (g ⊙ s)
    (monotone∘directed (scott→monotone g-scott) fam)
    (g x)
    (g-scott .pres-lub s fam x lub)
```

# The Category of DCPOs

DCPOs and Scott-continuous maps can be organized into a [displayed category]
over $\Sets$. We will use our usual [machinery for displaying]
[univalent categories] over $\Sets$.

[displayed category]: Cat.Displayed.Base.html
[machinery for displaying]: Cat.Displayed.Univalence.Thin.html
[univalent categories]: Cat.Univalent.html

```agda
DCPO-structure : ∀ o ℓ → Thin-structure {ℓ = o} (lsuc o ⊔ ℓ) (DCPO-on ℓ)
DCPO-structure o ℓ .is-hom f A B .∣_∣ =
  is-scott-continuous f A B
DCPO-structure o ℓ .is-hom f A B .is-tr =
  is-scott-continuous-is-prop f A B 
DCPO-structure o ℓ .id-is-hom {s = A} = scott-id
DCPO-structure o ℓ .∘-is-hom _ _ = scott-∘
DCPO-structure o ℓ .id-hom-unique {s = s} {t = t} scott scott' =
  DCPO-on-path λ x y →
    ua $ prop-ext s.≤-thin t.≤-thin
      (scott→monotone scott x y)
      (scott→monotone scott' x y)
  where
    module s = DCPO-on s
    module t = DCPO-on t

DCPOs : ∀ o ℓ → Precategory _ _
DCPOs o ℓ = Structured-objects (DCPO-structure o ℓ)

module DCPOs {o ℓ} = Cat.Reasoning (DCPOs o ℓ)
DCPO : (o ℓ : Level) → Type (lsuc o ⊔ lsuc ℓ)
DCPO o ℓ = DCPOs.Ob {o} {ℓ}
```

We have a forgetful functor from the category of DCPOs to the category
of posets.

```agda
Scott→Mono
  : ∀ {o ℓ} {D E : DCPO o ℓ}
  → DCPOs.Hom D E
  → Posets.Hom (DCPO-on.poset (D .snd)) (DCPO-on.poset (E .snd))
Scott→Mono f = total-hom (f .hom) (scott→monotone (f .preserves))

DCPOs→Posets : ∀ {o ℓ} → Functor (DCPOs o ℓ) (Posets o ℓ)
DCPOs→Posets .Functor.F₀ (A , A-dcpo) = A , DCPO-on.poset-on A-dcpo
DCPOs→Posets .Functor.F₁ f = total-hom (f .hom) (scott→monotone (f .preserves))
DCPOs→Posets .Functor.F-id = total-hom-path _ refl refl
DCPOs→Posets .Functor.F-∘ {z = z} _ _  =
  total-hom-path _ refl $ funext λ _ → funext λ _ → funext λ _ → ≤-thin (z .snd) _ _
```
