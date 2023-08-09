<!--
```agda
open import Data.Bool

open import Cat.Displayed.Total
open import Cat.Functor.Subcategory
open import Cat.Prelude

open import Order.Base
open import Order.Diagram.Lub

import Cat.Reasoning
import Order.Reasoning as Poset
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
  open Poset P

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
  open Poset P
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

# Scott-Continuous Maps

Let $(P, \le)$ and $(Q, \lsq)$ be a pair of posets. 
A monotone map $f : P \to Q$ is **Scott-continuous** if it preserves all
directed least upper bounds.

<!--
```agda
module _ {P Q : Poset o ℓ} where
  private
    module P = Poset P
    module Q = Poset Q

  open is-directed-family
```
-->

```agda
  is-scott-continuous : (f : Posets.Hom P Q) → Type _
  is-scott-continuous f =
    ∀ {Ix} (s : Ix → P.Ob) (fam : is-directed-family P s)
    → ∀ x → is-lub P s x → is-lub Q (f .hom ⊙ s) (f .hom x)

  is-scott-continuous-is-prop
    : ∀ (f : Posets.Hom P Q) → is-prop (is-scott-continuous f)
  is-scott-continuous-is-prop _ =
    Π-is-hlevel′ 1 λ _ → Π-is-hlevel³ 1 λ _ _ _  → Π-is-hlevel 1 λ _ →
    is-lub-is-prop Q
```

If $(P, \le)$ is a DCPO, then any function $f : P \to Q$ that preserves
directed least upper bounds is monotone. Start by constructing a directed
family $s : \rm{Bool} \to P$ with $s(true) = x$ and $s(false) = y$.
Note that $y$ is the least upper bound of this family,
so $f(y)$ must be an upper bound of $f \circ s$ in $Q$. From this,
we can deduce that $f(x) \lsq f(y)$.

```agda
  dcpo+scott→monotone
    : is-dcpo P
    → (f : P.Ob → Q.Ob)
    → (∀ {Ix} (s : Ix → Poset.Ob P) (fam : is-directed-family P s)
       → ∀ x → is-lub P s x → is-lub Q (f ⊙ s) (f x))
    → is-monotone f (P .snd) (Q .snd)
  dcpo+scott→monotone is-dcpo f scott x y p =
    is-lub.fam≤lub fs-lub (lift true)
    where

      s : Lift _ Bool → P.Ob 
      s (lift b) = if b then x else y

      sx≤sfalse : ∀ b → s b P.≤ s (lift false)
      sx≤sfalse (lift true) = p
      sx≤sfalse (lift false) = P.≤-refl

      s-directed : is-directed-family P s
      s-directed .elt =
        inc (lift true)
      s-directed .semidirected i j =
        inc (lift false , sx≤sfalse _ , sx≤sfalse _)

      s-lub : is-lub P s y
      s-lub .is-lub.fam≤lub = sx≤sfalse
      s-lub .is-lub.least z lt = lt (lift false)

      fs-lub : is-lub Q (f ⊙ s) (f y)
      fs-lub = scott s s-directed y s-lub
```

Next, a small little lemma; if $f : P \to Q$ is monotone and $s : I \to P$
is a directed family, then $fs : I \to Q$ is also a directed family.

```agda
  monotone∘directed
    : ∀ {Ix : Type o}
    → {s : Ix → P.Ob}
    → (f : Posets.Hom P Q)
    → is-directed-family P s
    → is-directed-family Q (f .hom ⊙ s)
  monotone∘directed f dir .elt = dir .elt
  monotone∘directed f dir .is-directed-family.semidirected i j =
    ∥-∥-map (Σ-map₂ (×-map (f .preserves _ _) (f .preserves _ _)))
      (dir .semidirected i j)
```

The identity function is Scott-continuous.

```agda
scott-id
  : ∀ {P : Poset o ℓ}
  → is-scott-continuous (Posets.id {x = P})
scott-id s fam x lub = lub
```

Scott-continuous functions are closed under composition.

```agda
scott-∘
  : ∀ {P Q R : Poset o ℓ}
  → (f : Posets.Hom Q R) (g : Posets.Hom P Q)
  → is-scott-continuous f → is-scott-continuous g
  → is-scott-continuous (f Posets.∘ g)
scott-∘ f g f-scott g-scott s dir x lub =
  f-scott (g .hom ⊙ s)
    (monotone∘directed g dir)
    (g .hom x)
    (g-scott s dir x lub)
```


# The Category of DCPOs

DCPOs form a [subcategory] of the category of posets. Furthermore, the category
of DCPOs is [univalent], as being a DPCO is a property of a poset.

[subcategory]: Cat.Functor.Subcategory.html
[univalent]: Cat.Univalent.html

```agda
DCPOs-subcat : ∀ (o ℓ : Level) → Subcat (Posets o ℓ) (lsuc o ⊔ ℓ) (lsuc o ⊔ ℓ)
DCPOs-subcat o ℓ .Subcat.is-ob = is-dcpo
DCPOs-subcat o ℓ .Subcat.is-hom f _ _ = is-scott-continuous f
DCPOs-subcat o ℓ .Subcat.is-hom-prop f _ _ = is-scott-continuous-is-prop f
DCPOs-subcat o ℓ .Subcat.is-hom-id _ = scott-id
DCPOs-subcat o ℓ .Subcat.is-hom-∘ {f = f} {g = g} = scott-∘ f g

DCPOs : ∀ (o ℓ : Level) → Precategory (lsuc (o ⊔ ℓ)) (lsuc o ⊔ ℓ)
DCPOs o ℓ = Subcategory (DCPOs-subcat o ℓ)

DCPOs-is-category : ∀ {o ℓ} → is-category (DCPOs o ℓ)
DCPOs-is-category = subcat-is-category Posets-is-category (λ _ → is-dcpo-is-prop)
```

<!--
```agda
module DCPOs {o ℓ : Level} = Cat.Reasoning (DCPOs o ℓ)

DCPO : (o ℓ : Level) → Type _
DCPO o ℓ = DCPOs.Ob {o} {ℓ}

Forget-DCPO : ∀ {o ℓ} → Functor (DCPOs o ℓ) (Sets o)
Forget-DCPO = πᶠ _ F∘ Forget-subcat
```
-->

