<!--
```agda
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Prelude

open import Data.Bool

open import Order.Base
open import Order.Cat

import Order.Reasoning
```
-->

```agda
module Order.Diagram.Glb {o ℓ} (P : Poset o ℓ) where
```

<!--
```agda
open Order.Reasoning P
```
-->

# Greatest lower bounds {defines="greatest-lower-bound"}

A **glb** $g$ (short for **greatest lower bound**) for a family of
elements $(a_i)_{i : I}$ is, as the name implies, a greatest element
among the lower bounds of the $a_i$. Being a lower bound means that we
have $g \le a_i$ for all $i : I$; Being the _greatest_ lower bound means
that if we're given some other $m$ satisfying $m \le a_i$ (for each
$i$), then we have $m \le u$.

A more common _word_ to use for "greatest lower bound" is "meet". But
since "meet" is a fairly uninformative name, and "glb" (pronounced
"glib") is just plain fun to say, we stick with the non-word for the
indexed concept. However, if we're talking about the glb of a binary
family, _then_ we use the word "meet". The distinction here is entirely
artificial, and it's just because we can't reuse the identifier
`is-glb`{.Agda} for these two slightly different cases. Summing up: to
us, a meet is a glb of two elements.

```agda
record is-glb {ℓᵢ} {I : Type ℓᵢ} (F : I → Ob) (glb : Ob)
        : Type (o ⊔ ℓ ⊔ ℓᵢ) where
  no-eta-equality
  field
    glb≤fam  : ∀ i → glb ≤ F i
    greatest : (lb' : Ob) → (∀ i → lb' ≤ F i) → lb' ≤ glb

record Glb {ℓᵢ} {I : Type ℓᵢ} (F : I → Ob) : Type (o ⊔ ℓ ⊔ ℓᵢ) where
  no-eta-equality
  field
    glb : Ob
    has-glb : is-glb F glb
  open is-glb has-glb public
```

<!--
```agda
open is-glb

private unquoteDecl eqv = declare-record-iso eqv (quote is-glb)

is-glb-is-prop
  : ∀ {ℓᵢ} {I : Type ℓᵢ} {F : I → Ob} {glb : Ob}
  → is-prop (is-glb F glb)
is-glb-is-prop = Iso→is-hlevel 1 eqv hlevel!

instance
  H-Level-is-glb
    : ∀ {ℓᵢ} {I : Type ℓᵢ} {F : I → Ob} {glb : Ob} {n}
    → H-Level (is-glb F glb) (suc n)
  H-Level-is-glb = prop-instance is-glb-is-prop

glb-unique
  : ∀ {ℓᵢ} {I : Type ℓᵢ} {F : I → Ob} {x y}
  → is-glb F x → is-glb F y
  → x ≡ y
glb-unique is is' = ≤-antisym
  (is' .greatest _ (is .glb≤fam))
  (is .greatest _ (is' .glb≤fam))

Glb-is-prop
  : ∀ {ℓᵢ} {I : Type ℓᵢ} {F : I → Ob}
  → is-prop (Glb F)
Glb-is-prop p q i .Glb.glb =
  glb-unique (Glb.has-glb p) (Glb.has-glb q) i
Glb-is-prop {F = F} p q i .Glb.has-glb =
  is-prop→pathp {B = λ i → is-glb F (glb-unique (Glb.has-glb p) (Glb.has-glb q) i)}
    (λ i → hlevel 1)
    (Glb.has-glb p) (Glb.has-glb q) i

instance
  H-Level-Glb
    : ∀ {ℓᵢ} {I : Type ℓᵢ} {F : I → Ob} {n}
    → H-Level (Glb F) (suc n)
  H-Level-Glb = prop-instance Glb-is-prop

lift-is-glb
  : ∀ {ℓᵢ ℓᵢ'} {I : Type ℓᵢ} {F : I → Ob} {glb}
  → is-glb F glb → is-glb (F ⊙ Lift.lower {ℓ = ℓᵢ'}) glb
lift-is-glb is .glb≤fam (lift ix) = is .glb≤fam ix
lift-is-glb is .greatest ub' le = is .greatest ub' (le ⊙ lift)

lift-glb
  : ∀ {ℓᵢ ℓᵢ'} {I : Type ℓᵢ} {F : I → Ob}
  → Glb F → Glb (F ⊙ Lift.lower {ℓ = ℓᵢ'})
lift-glb glb .Glb.glb = Glb.glb glb
lift-glb glb .Glb.has-glb = lift-is-glb (Glb.has-glb glb)

lower-is-glb
  : ∀ {ℓᵢ ℓᵢ'} {I : Type ℓᵢ} {F : I → Ob} {glb}
  → is-glb (F ⊙ Lift.lower {ℓ = ℓᵢ'}) glb → is-glb F glb
lower-is-glb is .glb≤fam ix = is .glb≤fam (lift ix)
lower-is-glb is .greatest ub' le = is .greatest ub' (le ⊙ Lift.lower)

lower-glb
  : ∀ {ℓᵢ ℓᵢ'} {I : Type ℓᵢ} {F : I → Ob}
  → Glb (F ⊙ Lift.lower {ℓ = ℓᵢ'}) → Glb F
lower-glb glb .Glb.glb = Glb.glb glb
lower-glb glb .Glb.has-glb = lower-is-glb (Glb.has-glb glb)
```
-->

## Meets {defines="meet"}

As mentioned before, in the binary case, we refer to glbs as **meets**:
The meet of $a$ and $b$ is, if it exists, the greatest element
satisfying $(a \cap b) \le a$ and $(a \cap b) \le b$.

```agda
record is-meet (a b : Ob) (glb : Ob) : Type (o ⊔ ℓ) where
  no-eta-equality
  field
    meet≤l   : glb ≤ a
    meet≤r   : glb ≤ b
    greatest : (lb' : Ob) → lb' ≤ a → lb' ≤ b → lb' ≤ glb

record Meet (a b : Ob) : Type (o ⊔ ℓ) where
  no-eta-equality
  field
    glb : Ob
    has-meet : is-meet a b glb
  open is-meet has-meet public

open is-meet
```

A shuffling of terms shows that being a meet is precisely being the
greatest lower bound of a family of two elements.

```agda
is-meet→is-glb : ∀ {a b glb} → is-meet a b glb → is-glb (if_then a else b) glb
is-meet→is-glb meet .glb≤fam true = meet .meet≤l
is-meet→is-glb meet .glb≤fam false = meet .meet≤r
is-meet→is-glb meet .greatest glb' x = meet .greatest glb' (x true) (x false)

is-glb→is-meet : ∀ {F : Bool → Ob} {glb} → is-glb F glb → is-meet (F true) (F false) glb
is-glb→is-meet glb .meet≤l = glb .glb≤fam true
is-glb→is-meet glb .meet≤r = glb .glb≤fam false
is-glb→is-meet glb .greatest lb' lb'<a lb'<b = glb .greatest lb' λ where
  true  → lb'<a
  false → lb'<b
```

<!--
```agda
private unquoteDecl eqv' = declare-record-iso eqv' (quote is-meet)

instance
  H-Level-is-meet
    : ∀ {a b glb : Ob} {n}
    → H-Level (is-meet a b glb) (suc n)
  H-Level-is-meet = prop-instance $ Iso→is-hlevel 1 eqv' hlevel!

meet-unique : ∀ {a b x y} → is-meet a b x → is-meet a b y → x ≡ y
meet-unique x-meet y-meet =
  glb-unique (is-meet→is-glb x-meet) (is-meet→is-glb y-meet)

Meet-is-prop : ∀ {a b} → is-prop (Meet a b)
Meet-is-prop p q i .Meet.glb =
  meet-unique (Meet.has-meet p) (Meet.has-meet q) i
Meet-is-prop {a = a} {b = b} p q i .Meet.has-meet =
  is-prop→pathp {B = λ i → is-meet a b (meet-unique (Meet.has-meet p) (Meet.has-meet q) i)}
    (λ i → hlevel 1)
    (Meet.has-meet p) (Meet.has-meet q) i

instance
  H-Level-Meet
    : ∀ {a b} {n}
    → H-Level (Meet a b) (suc n)
  H-Level-Meet = prop-instance Meet-is-prop

Meet→Glb : ∀ {a b} → Meet a b → Glb (if_then a else b)
Meet→Glb meet .Glb.glb = Meet.glb meet
Meet→Glb meet .Glb.has-glb = is-meet→is-glb (Meet.has-meet meet)

Glb→Meet : ∀ {a b} → Glb (if_then a else b) → Meet a b
Glb→Meet glb .Meet.glb = Glb.glb glb
Glb→Meet glb .Meet.has-meet = is-glb→is-meet (Glb.has-glb glb)

is-meet≃is-glb : ∀ {a b glb : Ob} → is-equiv (is-meet→is-glb {a} {b} {glb})
is-meet≃is-glb = prop-ext! _ is-glb→is-meet .snd

Meet≃Glb : ∀ {a b} → is-equiv (Meet→Glb {a} {b})
Meet≃Glb = prop-ext! _ Glb→Meet .snd
```
-->

An important lemma about meets is that, if $x \le y$, then the greatest
lower bound of $x$ and $y$ is just $x$:

```agda
le→is-meet : ∀ {a b} → a ≤ b → is-meet a b a
le→is-meet a≤b .meet≤l = ≤-refl
le→is-meet a≤b .meet≤r = a≤b
le→is-meet a≤b .greatest lb' lb'≤a _ = lb'≤a

le-meet : ∀ {a b l} → a ≤ b → is-meet a b l → a ≡ l
le-meet a≤b l = meet-unique (le→is-meet a≤b) l
```

### As products

When passing from posets to categories, meets become [[products]]:
coming from the other direction, if a category $\cC$ has each
$\hom(x,y)$ a [[proposition]], then products in $\cC$ are simply meets.

```agda
open is-product
open Product

is-meet→product : ∀ {a b glb : Ob} → is-meet a b glb → Product (poset→category P) a b
is-meet→product glb .apex = _
is-meet→product glb .π₁ = glb .is-meet.meet≤l
is-meet→product glb .π₂ = glb .is-meet.meet≤r
is-meet→product glb .has-is-product .⟨_,_⟩ q<a q<b =
  glb .is-meet.greatest _ q<a q<b
is-meet→product glb .has-is-product .π₁∘factor = prop!
is-meet→product glb .has-is-product .π₂∘factor = prop!
is-meet→product glb .has-is-product .unique _ _ _ = prop!
```

## Top elements

A **top element** in a partial order $(P, \le)$ is an element $\top : P$
that is larger than any other element in $P$. This is the same as being
a greatest lower bound for the empty family $\bot \to P$.

```agda
is-top : Ob → Type _
is-top top = ∀ x → x ≤ top

record Top : Type (o ⊔ ℓ) where
  field
    top : Ob
    has-top : is-top top

  ! : ∀ {x} → x ≤ top
  ! = has-top _

is-top→is-glb : ∀ {glb} {f : ⊥ → _} → is-top glb → is-glb f glb
is-top→is-glb is-top .greatest x _ = is-top x

is-glb→is-top : ∀ {glb} {f : ⊥ → _} → is-glb f glb → is-top glb
is-glb→is-top glb x = glb .greatest x λ ()
```

<!--
```agda
is-top-is-prop : ∀ x → is-prop (is-top x)
is-top-is-prop _ = hlevel!

top-unique : ∀ {x y} → is-top x → is-top y → x ≡ y
top-unique p q = ≤-antisym (q _) (p _)

Top-is-prop : is-prop Top
Top-is-prop p q i .Top.top =
  top-unique (Top.has-top p) (Top.has-top q) i
Top-is-prop p q i .Top.has-top =
  is-prop→pathp
    (λ i → is-top-is-prop (top-unique (Top.has-top p) (Top.has-top q) i))
    (Top.has-top p) (Top.has-top q) i

instance
  H-Level-Top
    : ∀ {n}
    → H-Level Top (suc n)
  H-Level-Top = prop-instance Top-is-prop

Top→Glb : ∀ {f : ⊥ → _} → Top → Glb f
Top→Glb top .Glb.glb = Top.top top
Top→Glb top .Glb.has-glb = is-top→is-glb (Top.has-top top)

Glb→Top : ∀ {f : ⊥ → _} → Glb f → Top
Glb→Top glb .Top.top = Glb.glb glb
Glb→Top glb .Top.has-top = is-glb→is-top (Glb.has-glb glb)

is-top≃is-glb : ∀ {glb} {f} → is-equiv (is-top→is-glb {glb} {f})
is-top≃is-glb = prop-ext! _ is-glb→is-top .snd

Top≃Glb : ∀ {f} → is-equiv (Top→Glb {f})
Top≃Glb = prop-ext! _ Glb→Top .snd
```
-->

### As terminal objects

Bottoms are the decategorifcation of [[terminal objects]]; we don't need to
require the uniqueness of the universal morphism, as we've replaced our
hom-sets with hom-props!

```agda
is-top→terminal : ∀ {x} → is-top x → is-terminal (poset→category P) x
is-top→terminal is-top x .centre = is-top x
is-top→terminal is-top x .paths _ = ≤-thin _ _

terminal→is-top : ∀ {x} → is-terminal (poset→category P) x → is-top x
terminal→is-top terminal x = terminal x .centre
```
