---
description: |
  Quasigroups.
---
<!--
```agda
open import 1Lab.Type.Sigma

open import Algebra.Magma

open import Cat.Displayed.Univalence.Thin
open import Cat.Displayed.Total
open import Cat.Prelude hiding (_/_)

import Cat.Reasoning
```
-->

```agda
module Algebra.Quasigroup where
```

# Quasigroups

Traditionally, [[groups]] are defined as [[monoids]] where every element
has a ([necessarily unique]) inverse. However, there is another path to
the theory of groups that emphasizes division/subtraction over inverses.
This perspective is especially interesting when generalizing groups to
non-associative settings; axioms of the form $xx^{-1} = 1$ are rather
ill-behaved without associativity, as inverses are no longer necessarily
unique!

[necessarily unique]: Algebra.Monoid.html#inverses

<!--
```agda
private variable
  ℓ ℓ' : Level
  A B : Type ℓ

open Cat.Displayed.Univalence.Thin using (Extensional-Hom) public
```
-->

## Right quasigroups

For the sake of maximum generality, we will build up to the definition
of quasigroups in stages, starting with right quasigroups.

:::{.definition #right-quasigroup}
Let $\star : A \to A \to A$ be a binary operator. $(A, \star)$ is a
**right quasigroup** if $(A, \star)$ is a [[magma]], and there is some
binary operator $/ : A \to A A$, subject to the following axioms:

- For all $x, y : A$, $(y / x) \star x = y$
- For all $x, y : A$, $(y \star x) / x = y$
:::

```agda
record is-right-quasigroup {ℓ} {A : Type ℓ} (_⋆_ : A → A → A) : Type ℓ where
  no-eta-equality
  field
    _/_ : A → A → A
    /-invl : ∀ x y → (x / y) ⋆ y ≡ x
    /-invr : ∀ x y → (x ⋆ y) / y ≡ x
    has-is-magma : is-magma _⋆_

  open is-magma has-is-magma public
```

Intuitively, the $/ : A \to A \to A$ operation acts like a sort of
right-biased division. This is further cemented by noting that
the existence of such an operation implies that every $x : A$, the action
$- \star x : A \to A$ is an [[equivalence]].

```agda
  ⋆-equivr : ∀ x → is-equiv (_⋆ x)
  ⋆-equivr x .is-eqv y .centre = y / x , /-invl y x
  ⋆-equivr x .is-eqv y .paths (l , lx=y) =
    Σ-prop-path (λ l → has-is-set (l ⋆ x) y) $
      y / x       ≡˘⟨ ap (_/ x) lx=y ⟩
      (l ⋆ x) / x ≡⟨ /-invr l x ⟩
      l           ∎
```

This in turn implies that $- / x : A \to A$ is an equivalence.

```agda
  /-equivr : ∀ x → is-equiv (_/ x)
  /-equivr x = inverse-is-equiv (⋆-equivr x)
```

As easy corollaries, we get that multiplication and division in $A$ are
right-cancellative.


```agda
  opaque
    ⋆-cancelr : ∀ {x y} (z : A) → x ⋆ z ≡ y ⋆ z → x ≡ y
    ⋆-cancelr z = Equiv.injective (_⋆ z , ⋆-equivr z)

    /-cancelr : ∀ {x y} (z : A) → x / z ≡ y / z → x ≡ y
    /-cancelr z = Equiv.injective (_/ z , /-equivr z)
```

It turns out that $- \star x$ being an equivalence is a sufficient condition
for a $A$ to be a right quasigroup, provided that $A$ is a [[set]].

```agda
⋆-equivr→is-right-quasigroup
  : ∀ {_⋆_ : A → A → A}
  → is-set A
  → (∀ x → is-equiv (_⋆ x))
  → is-right-quasigroup _⋆_
```

The proof is an exercise in unrolling definitions. If $- \star x$ is an
equivalence, then $(- \star y)^{-1}(x)$ serves as a perfectly valid
definition of $x / y$; both axioms follow directly from the
unit and counit of the equivalence.

```agda
⋆-equivr→is-right-quasigroup {_⋆_ = _⋆_} A-set ⋆-eqv =
  ⋆-right-quasi
  where
    open is-right-quasigroup

    module ⋆-eqv x = Equiv (_⋆ x , ⋆-eqv x)

    ⋆-right-quasi : is-right-quasigroup _⋆_
    ⋆-right-quasi ._/_ x y = ⋆-eqv.from y x
    ⋆-right-quasi ./-invl x y = ⋆-eqv.ε y x
    ⋆-right-quasi ./-invr x y = ⋆-eqv.η y x
    ⋆-right-quasi .has-is-magma .is-magma.has-is-set = A-set
```

We can upgrade this correspondence to an equivalence, as we definitionally
get back the same division operation we started with after round-tripping.

```agda
is-right-quasigroup≃⋆-equivr
  : ∀ {_⋆_ : A → A → A}
  → is-right-quasigroup _⋆_ ≃ (is-set A × (∀ x → is-equiv (_⋆ x)))
is-right-quasigroup≃⋆-equivr {_⋆_ = _⋆_} =
  Iso→Equiv $
    ⟨ has-is-set , ⋆-equivr ⟩ ,
    iso (uncurry ⋆-equivr→is-right-quasigroup)
      (λ _ → prop!)
     (λ ⋆-right-quasi →
      let open is-right-quasigroup ⋆-right-quasi in
      Iso.injective eqv (refl ,ₚ prop!))
  where
    open is-right-quasigroup
    unquoteDecl eqv = declare-record-iso eqv (quote is-right-quasigroup)
```

Crucially, this means that the division operation $/ : A \to A \to A$
is actually a [[property]] rather than structure, as both `is-equiv`{.Agda} and
`is-set`{.Agda} are propositions.

```agda
is-right-quasigroup-is-prop
  : ∀ {_⋆_ : A → A → A}
  → is-prop (is-right-quasigroup _⋆_)
is-right-quasigroup-is-prop {A = A} =
  Equiv→is-hlevel 1 is-right-quasigroup≃⋆-equivr (hlevel 1)
```

<!--
```agda
instance
  H-Level-is-right-quasigroup
    : ∀ {_⋆_ : A → A → A} {n}
    → H-Level (is-right-quasigroup _⋆_) (suc n)
  H-Level-is-right-quasigroup = prop-instance is-right-quasigroup-is-prop
```
-->

### Right quasigroup homomorphisms

In the previous section, we proved that the existence of a right division
operation was actually a property of a magma, rather than structure. We shall now see
that right division is automatically preserved by magma homomorphisms.

We start by defining the corresponding notion of structure for right
quasigroups.

:::{.definition #right-quasigroup-structure}
A **right quasigroup structure** on a type $A$ is a binary operation
$\star : A \to A \to A$ such that $(A, \star)$ is a right quasigroup.
:::

```agda
record Right-quasigroup-on {ℓ} (A : Type ℓ) : Type ℓ where
  no-eta-equality
  field
    _⋆_ : A → A → A
    has-is-right-quasigroup : is-right-quasigroup _⋆_

  open is-right-quasigroup has-is-right-quasigroup public

```

:::{.definition #right-quasigroup-homomorphism}
A **right quasigroup homomorphism** between two right quasigroups $A, B$
is a function $f : A \to B$ such that $f (x \star y) = f x \star f y$.
:::

```agda
record is-right-quasigroup-hom
  {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  (f : A → B)
  (S : Right-quasigroup-on A) (T : Right-quasigroup-on B)
  : Type (ℓ ⊔ ℓ')
  where
  no-eta-equality
  private
    module A = Right-quasigroup-on S
    module B = Right-quasigroup-on T
  field
    pres-⋆ : ∀ x y → f (x A.⋆ y) ≡ f x B.⋆ f y
```

Preservation of right division follows almost immediately from
right-cancellativity.


```agda
  pres-/ : ∀ x y → f (x A./ y) ≡ f x B./ f y
  pres-/ x y =
    B.⋆-cancelr (f y) $
      f (x A./ y) B.⋆ f y   ≡˘⟨ pres-⋆ (x A./ y) y ⟩
      f ((x A./ y) A.⋆ y)   ≡⟨ ap f (A./-invl x y) ⟩
      f x                   ≡˘⟨ B./-invl (f x) (f y) ⟩
      (f x B./ f y) B.⋆ f y ∎
```

<!--
```agda
is-right-quasigroup-hom-is-prop
  : {f : A → B}
  → {S : Right-quasigroup-on A} {T : Right-quasigroup-on B}
  → is-prop (is-right-quasigroup-hom f S T)
is-right-quasigroup-hom-is-prop {T = T} =
  Iso→is-hlevel! 1 eqv
  where
    open Right-quasigroup-on T
    private unquoteDecl eqv = declare-record-iso eqv (quote is-right-quasigroup-hom)

instance
  H-Level-is-right-quasigroup-hom
    : {f : A → B}
    → {S : Right-quasigroup-on A} {T : Right-quasigroup-on B}
    → ∀ {n} → H-Level (is-right-quasigroup-hom f S T) (suc n)
  H-Level-is-right-quasigroup-hom = prop-instance is-right-quasigroup-hom-is-prop
```
-->

<!--
```agda
module _ where
  open is-right-quasigroup-hom
  open Right-quasigroup-on

  Right-quasigroup-on-pathp
    : ∀ {A : I → Type ℓ}
    → {S : Right-quasigroup-on (A i0)} {T : Right-quasigroup-on (A i1)}
    → PathP (λ i → ∀ (x y : A i) → A i) (S ._⋆_) (T ._⋆_)
    → PathP (λ i → Right-quasigroup-on (A i)) S T
  Right-quasigroup-on-pathp {S = S} {T = T} p i ._⋆_ x y =
    p i x y
  Right-quasigroup-on-pathp {S = S} {T = T} p i .has-is-right-quasigroup =
    is-prop→pathp
      (λ i → is-right-quasigroup-is-prop {_⋆_ = p i})
      (S .has-is-right-quasigroup)
      (T .has-is-right-quasigroup)
      i
```
-->

Right quasigroups are algebraic structures, so they form a [[thin structure]]
over $\Sets$.

```agda
  Right-quasigroup-structure : ∀ ℓ → Thin-structure ℓ Right-quasigroup-on
  Right-quasigroup-structure ℓ .is-hom f A B .∣_∣ =
    is-right-quasigroup-hom f A B
  Right-quasigroup-structure ℓ .is-hom f A B .is-tr =
    is-right-quasigroup-hom-is-prop
  Right-quasigroup-structure ℓ .id-is-hom .pres-⋆ x y =
    refl
  Right-quasigroup-structure ℓ .∘-is-hom f g f-hom g-hom .pres-⋆ x y =
    ap f (g-hom .pres-⋆ x y) ∙ f-hom .pres-⋆ (g x) (g y)
  Right-quasigroup-structure ℓ .id-hom-unique {A} {S} {T} p q =
    Right-quasigroup-on-pathp (ext (p .pres-⋆))

```

This observation lets us neatly organize right quasigroups into a [[category]].

```agda
Right-quasigroups : ∀ ℓ → Precategory (lsuc ℓ) ℓ
Right-quasigroups ℓ = Structured-objects (Right-quasigroup-structure ℓ)

module Right-quasigroups {ℓ} = Cat.Reasoning (Right-quasigroups ℓ)

Right-quasigroup : (ℓ : Level) → Type (lsuc ℓ)
Right-quasigroup ℓ = Right-quasigroups.Ob {ℓ}
```

<!--
```agda
module Right-quasigroup {ℓ} (A : Right-quasigroup ℓ) where
  open Right-quasigroup-on (A .snd) public
```
-->


## Left quasigroups

We can dualise the definition of right quasigroups to arrive at the
notion of a **left quasigroup**.

:::{.definition #left-quasigroup}
Let $\star : A \to A \to A$ be a binary operator. $(A, \star)$ is a
**left quasigroup** if $(A, \star)$ is a [[magma]], and there is some
binary operator $\backslash : A \to A \to A$, subject to the following axioms:

- For all $x, y : A$, $x \star (x \backslash y) = y$
- For all $x, y : A$, $x \backslash (x \star y) = y$
:::


```agda
record is-left-quasigroup {ℓ} {A : Type ℓ} (_⋆_ : A → A → A) : Type ℓ where
  no-eta-equality
  field
    _⧵_ : A → A → A
    ⧵-invr : ∀ x y → x ⋆ (x ⧵ y) ≡ y
    ⧵-invl : ∀ x y → x ⧵ (x ⋆ y) ≡ y
    has-is-magma : is-magma _⋆_

  open is-magma has-is-magma public
```

Intuitively, we should think of $x \backslash y$ as "$y$ divided by $x$" or
"$y$ over $x$". This is reinforced by the fact that for every $x : A$, the action
$x \star - : A \to A$ is an [[equivalence]].

```agda
  ⋆-equivl : ∀ x → is-equiv (x ⋆_)
  ⋆-equivl x .is-eqv y .centre = x ⧵ y , ⧵-invr x y
  ⋆-equivl x .is-eqv y .paths (r , xr=y) =
    Σ-prop-path (λ r → has-is-set (x ⋆ r) y) $
      x ⧵ y       ≡˘⟨ ap (x ⧵_) xr=y ⟩
      x ⧵ (x ⋆ r) ≡⟨ ⧵-invl x r ⟩
      r ∎

  ⧵-equivl : ∀ x → is-equiv (x ⧵_)
  ⧵-equivl x = inverse-is-equiv (⋆-equivl x)
```

This implies that that multiplication and division in $A$ is left-cancellative.

```agda
  opaque
    ⋆-cancell : ∀ (x : A) {y z} → x ⋆ y ≡ x ⋆ z → y ≡ z
    ⋆-cancell x = Equiv.injective (x ⋆_ , ⋆-equivl x)

    ⧵-cancell : ∀ (x : A) {y z} → x ⧵ y ≡ x ⧵ z → y ≡ z
    ⧵-cancell x = Equiv.injective (x ⧵_ , ⧵-equivl x)
```

Next, we shall show that left quasigroups are formally dual to right quasigroups.

```agda
is-left-quasigroup≃op-is-right-quasigroup
  : ∀ {_⋆_ : A → A → A}
  → is-left-quasigroup _⋆_ ≃ is-right-quasigroup (λ x y → y ⋆ x)
```

<details>
<summary>The proof of this fact is rather tedious, so we will omit the
details.
</summary>

```agda
is-left-quasigroup→op-is-right-quasigroup
  : ∀ {_⋆_ : A → A → A}
  → is-left-quasigroup _⋆_ → is-right-quasigroup (λ x y → y ⋆ x)

is-right-quasigroup→op-is-left-quasigroup
  : ∀ {_⋆_ : A → A → A}
  → is-right-quasigroup _⋆_ → is-left-quasigroup (λ x y → y ⋆ x)

is-left-quasigroup→op-is-right-quasigroup {_⋆_ = _⋆_} A-quasi = A-op-quasi
  where
    open is-left-quasigroup A-quasi
    open is-right-quasigroup

    A-op-quasi : is-right-quasigroup (λ x y → y ⋆ x)
    A-op-quasi ._/_ x y = y ⧵ x
    A-op-quasi ./-invr = flip ⧵-invl
    A-op-quasi ./-invl = flip ⧵-invr
    A-op-quasi .has-is-magma .is-magma.has-is-set = hlevel 2

is-right-quasigroup→op-is-left-quasigroup {_⋆_ = _⋆_} A-quasi = A-op-quasi
  where
    open is-right-quasigroup A-quasi
    open is-left-quasigroup

    A-op-quasi : is-left-quasigroup (λ x y → y ⋆ x)
    A-op-quasi ._⧵_ x y = y / x
    A-op-quasi .⧵-invr = flip /-invl
    A-op-quasi .⧵-invl = flip /-invr
    A-op-quasi .has-is-magma .is-magma.has-is-set = hlevel 2

is-left-quasigroup≃op-is-right-quasigroup =
  Iso→Equiv $
    is-left-quasigroup→op-is-right-quasigroup ,
    iso is-right-quasigroup→op-is-left-quasigroup
      (λ _ → prop!)
      (λ ⋆-left-quasi →
        let open is-left-quasigroup ⋆-left-quasi in
        Iso.injective eqv (refl ,ₚ prop!))
    where
      private unquoteDecl eqv = declare-record-iso eqv (quote is-left-quasigroup)
```
</details>


This in turn means that being a left quasigroup is a property of a binary
operation.

```agda
is-left-quasigroup-is-prop
  : ∀ {_⋆_ : A → A → A}
  → is-prop (is-left-quasigroup _⋆_)
is-left-quasigroup-is-prop {A = A} =
  Equiv→is-hlevel 1 (is-left-quasigroup≃op-is-right-quasigroup) (hlevel 1)
```

<!--
```agda
instance
  H-Level-is-left-quasigroup
    : ∀ {_⋆_ : A → A → A} {n}
    → H-Level (is-left-quasigroup _⋆_) (suc n)
  H-Level-is-left-quasigroup = prop-instance is-left-quasigroup-is-prop
```
-->

<!--
```agda
⋆-equivl→is-left-quasigroup
  : ∀ {_⋆_ : A → A → A}
  → is-set A
  → (∀ x → is-equiv (x ⋆_))
  → is-left-quasigroup _⋆_
⋆-equivl→is-left-quasigroup A-set eqv =
  is-right-quasigroup→op-is-left-quasigroup $
  ⋆-equivr→is-right-quasigroup A-set eqv

is-left-quasigroup≃⋆-equivl
  : ∀ {_⋆_ : A → A → A}
  → is-left-quasigroup _⋆_ ≃ (is-set A × (∀ x → is-equiv (x ⋆_)))
is-left-quasigroup≃⋆-equivl =
  is-left-quasigroup≃op-is-right-quasigroup
  ∙e is-right-quasigroup≃⋆-equivr
```
-->

### Left quasigroup homomorphisms

We can continue dualizing to define a notion of homomorphism for
left quasigroups, though we shall be much more terse in our development.
Following the pattern of right quasigroups, we begin by defining
**left quasigroup structures**.


:::{.definition #left-quasigroup-structure}
A **left quasigroup structure** on a type $A$ is a binary operation
$\star : A \to A \to A$ such that $(A, \star)$ is a left quasigroup.
:::

```agda
record Left-quasigroup-on {ℓ} (A : Type ℓ) : Type ℓ where
  no-eta-equality
  field
    _⋆_ : A → A → A
    has-is-left-quasigroup : is-left-quasigroup _⋆_

  open is-left-quasigroup has-is-left-quasigroup public
```


:::{.definition #left-quasigroup-homomorphism}
A **left quasigroup homomorphism** between two left quasigroups $A, B$
is a function $f : A \to B$ such that $f (x \star y) = f x \star f y$.
:::

```agda
record is-left-quasigroup-hom
  {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  (f : A → B)
  (S : Left-quasigroup-on A) (T : Left-quasigroup-on B)
  : Type (ℓ ⊔ ℓ')
  where
  no-eta-equality
  private
    module A = Left-quasigroup-on S
    module B = Left-quasigroup-on T
  field
    pres-⋆ : ∀ x y → f (x A.⋆ y) ≡ f x B.⋆ f y
```

Dual to right quasigroups, preservation of left division follows from
left-cancellativity.

```agda
  pres-⧵ : ∀ x y → f (x A.⧵ y) ≡ f x B.⧵ f y
  pres-⧵ x y =
    B.⋆-cancell (f x) $
      f x B.⋆ f (x A.⧵ y)     ≡˘⟨ pres-⋆ x (x A.⧵ y) ⟩
      f (x A.⋆ (x A.⧵ y))     ≡⟨ ap f (A.⧵-invr x y) ⟩
      f y                     ≡˘⟨ B.⧵-invr (f x) (f y) ⟩
      f x B.⋆ (f x B.⧵ f y) ∎
```

<!--
```agda
is-left-quasigroup-hom-is-prop
  : {f : A → B}
  → {S : Left-quasigroup-on A} {T : Left-quasigroup-on B}
  → is-prop (is-left-quasigroup-hom f S T)
is-left-quasigroup-hom-is-prop {T = T} =
  Iso→is-hlevel! 1 eqv
  where
    open Left-quasigroup-on T
    private unquoteDecl eqv = declare-record-iso eqv (quote is-left-quasigroup-hom)

instance
  H-Level-is-left-quasigroup-hom
    : {f : A → B}
    → {S : Left-quasigroup-on A} {T : Left-quasigroup-on B}
    → ∀ {n} → H-Level (is-left-quasigroup-hom f S T) (suc n)
  H-Level-is-left-quasigroup-hom = prop-instance is-left-quasigroup-hom-is-prop
```
-->

Left quasigroups are algebraic structures, so they form a [[thin structure]]
over $\Sets$.

<!--
```agda
module _ where
  open is-left-quasigroup-hom
  open Left-quasigroup-on

  Left-quasigroup-on-pathp
    : ∀ {A : I → Type ℓ}
    → {S : Left-quasigroup-on (A i0)} {T : Left-quasigroup-on (A i1)}
    → PathP (λ i → ∀ (x y : A i) → A i) (S ._⋆_) (T ._⋆_)
    → PathP (λ i → Left-quasigroup-on (A i)) S T
  Left-quasigroup-on-pathp {S = S} {T = T} p i ._⋆_ x y =
    p i x y
  Left-quasigroup-on-pathp {S = S} {T = T} p i .has-is-left-quasigroup =
    is-prop→pathp
      (λ i → is-left-quasigroup-is-prop {_⋆_ = p i})
      (S .has-is-left-quasigroup)
      (T .has-is-left-quasigroup)
      i
```
-->

```agda
  Left-quasigroup-structure : ∀ ℓ → Thin-structure ℓ Left-quasigroup-on
  Left-quasigroup-structure ℓ .is-hom f A B .∣_∣ =
    is-left-quasigroup-hom f A B
  Left-quasigroup-structure ℓ .is-hom f A B .is-tr =
    is-left-quasigroup-hom-is-prop
  Left-quasigroup-structure ℓ .id-is-hom .pres-⋆ x y =
    refl
  Left-quasigroup-structure ℓ .∘-is-hom f g f-hom g-hom .pres-⋆ x y =
    ap f (g-hom .pres-⋆ x y) ∙ f-hom .pres-⋆ (g x) (g y)
  Left-quasigroup-structure ℓ .id-hom-unique p q =
    Left-quasigroup-on-pathp (ext (p .pres-⋆))
```

This observation lets us assemble left quasigroups into a [[category]].

```agda
Left-quasigroups : ∀ ℓ → Precategory (lsuc ℓ) ℓ
Left-quasigroups ℓ = Structured-objects (Left-quasigroup-structure ℓ)

module Left-quasigroups {ℓ} = Cat.Reasoning (Left-quasigroups ℓ)

Left-quasigroup : (ℓ : Level) → Type (lsuc ℓ)
Left-quasigroup ℓ = Left-quasigroups.Ob {ℓ}
```

<!--
```agda
module Left-quasigroup {ℓ} (A : Left-quasigroup ℓ) where
  open Left-quasigroup-on (A .snd) public
```
-->


## Quasigroups

:::{.definition #quasigroup}
A type $A$ equipped with a binary operation $\star : A \to A \to A$ is
a **quasigroup** if it is a [[left quasigroup]] and a [[right quasigroup]].
:::


```agda
record is-quasigroup {ℓ} {A : Type ℓ} (_⋆_ : A → A → A) : Type ℓ where
  no-eta-equality
  field
    has-is-left-quasigroup : is-left-quasigroup _⋆_
    has-is-right-quasigroup : is-right-quasigroup _⋆_
```

<!--
```agda
  open is-left-quasigroup has-is-left-quasigroup public
  open is-right-quasigroup has-is-right-quasigroup
    hiding (has-is-magma; underlying-set; magma-hlevel; has-is-set) public
```
-->

Quasigroups obey the **latin square property**: for every $x, y : A$,
there exists a unique pair $l, r : A$ such that $l \star x = y$ and $x \star r = y$.

```agda
  ⋆-latin : ∀ x y → is-contr (Σ[ l ∈ A ] Σ[ r ∈ A ] (l ⋆ x ≡ y × x ⋆ r ≡ y))
```

The proof is an exercise in equivalence yoga: by definition, a quasigroup
is both a left and right quasigroup, so multiplication on the left and right
is an equivalence, so the types $\Sigma (l : A) l \star x = y$ and
$\Sigma (r : A) r \star x = y$ are both contractible. Moreover,
$(\Sigma (l : A) l \star x = y) \times (\Sigma (r : A) r \star x = y)$ is
equivalent to $\Sigma (l : A) \Sigma (r : A) (l \star x = y \times x \star r = y)$,
so the latter must also be contractible.

```agda
  ⋆-latin x y =
    Equiv→is-hlevel 0
      latin-eqv
      (×-is-hlevel 0 (⋆-equivr x .is-eqv y) (⋆-equivl x .is-eqv y))
    where
      latin-eqv
        : (Σ[ l ∈ A ] Σ[ r ∈ A ] (l ⋆ x ≡ y × x ⋆ r ≡ y))
        ≃ ((Σ[ l ∈ A ] l ⋆ x ≡ y) × (Σ[ r ∈ A ] x ⋆ r ≡ y))
      latin-eqv =
        Σ[ l ∈ A ] Σ[ r ∈ A ] (l ⋆ x ≡ y × x ⋆ r ≡ y)     ≃⟨ Σ-ap id≃ (λ l → Σ-swap₂) ⟩
        Σ[ l ∈ A ] (l ⋆ x ≡ y × (Σ[ r ∈ A ] (x ⋆ r) ≡ y)) ≃⟨ Σ-assoc ⟩
        (Σ[ l ∈ A ] l ⋆ x ≡ y) × (Σ[ r ∈ A ] x ⋆ r ≡ y)   ≃∎
```

We also have the following pair of useful identities that relate
left and right division.

```agda
  /-⧵-cancelr : ∀ x y → x / (y ⧵ x) ≡ y
  /-⧵-cancelr x y =
    x / (y ⧵ x)             ≡˘⟨ ap (_/ (y ⧵ x)) (⧵-invr y x) ⟩
    (y ⋆ (y ⧵ x)) / (y ⧵ x) ≡⟨ /-invr y (y ⧵ x) ⟩
    y                       ∎

  /-⧵-cancell : ∀ x y → (x / y) ⧵ x ≡ y
  /-⧵-cancell x y =
    (x / y) ⧵ x             ≡˘⟨ ap ((x / y) ⧵_) (/-invl x y) ⟩
    (x / y) ⧵ ((x / y) ⋆ y) ≡⟨ ⧵-invl (x / y) y ⟩
    y                       ∎
```

<!--
```agda
unquoteDecl H-Level-is-quasigroup = declare-record-hlevel 1 H-Level-is-quasigroup (quote is-quasigroup)

is-quasigroup-is-prop
  : ∀ {_⋆_ : A → A → A}
  → is-prop (is-quasigroup _⋆_)
is-quasigroup-is-prop = hlevel 1
```
-->

### Quasigroup homomorphisms

:::{.definition #quasigroup-structure}
A **quasigroup structure** on a type $A$ is a binary operation
$\star : A \to A \to A$ such that $(A, \star)$ is a quasigroup.
:::

```agda
record Quasigroup-on {ℓ} (A : Type ℓ) : Type ℓ where
  no-eta-equality
  field
    _⋆_ : A → A → A
    has-is-quasigroup : is-quasigroup _⋆_

  open is-quasigroup has-is-quasigroup public
```

<!--
```agda
  left-quasigroup-on : Left-quasigroup-on A
  left-quasigroup-on .Left-quasigroup-on._⋆_ = _⋆_
  left-quasigroup-on .Left-quasigroup-on.has-is-left-quasigroup =
    has-is-left-quasigroup

  right-quasigroup-on : Right-quasigroup-on A
  right-quasigroup-on .Right-quasigroup-on._⋆_ = _⋆_
  right-quasigroup-on .Right-quasigroup-on.has-is-right-quasigroup =
    has-is-right-quasigroup
```
-->

:::{.definition #quasigroup-homomorphism}
A **quasigroup homomorphism** between two quasigroups $A, B$
is a function $f : A \to B$ such that $f (x \star y) = f x \star f y$.
:::


```agda
record is-quasigroup-hom
  {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  (f : A → B)
  (S : Quasigroup-on A) (T : Quasigroup-on B)
  : Type (ℓ ⊔ ℓ')
  where
  no-eta-equality
  private
    module A = Quasigroup-on S
    module B = Quasigroup-on T
  field
    pres-⋆ : ∀ x y → f (x A.⋆ y) ≡ f x B.⋆ f y
```

<!--
```agda
  has-is-left-quasigroup-hom
    : is-left-quasigroup-hom f A.left-quasigroup-on B.left-quasigroup-on
  has-is-left-quasigroup-hom .is-left-quasigroup-hom.pres-⋆ = pres-⋆

  has-is-right-quasigroup-hom
    : is-right-quasigroup-hom f A.right-quasigroup-on B.right-quasigroup-on
  has-is-right-quasigroup-hom .is-right-quasigroup-hom.pres-⋆ = pres-⋆

  open is-left-quasigroup-hom has-is-left-quasigroup-hom
    hiding (pres-⋆)
    public

  open is-right-quasigroup-hom has-is-right-quasigroup-hom
    hiding (pres-⋆)
    public
```
-->

<!--
```agda
is-quasigroup-hom-is-prop
  : {f : A → B}
  → {S : Quasigroup-on A} {T : Quasigroup-on B}
  → is-prop (is-quasigroup-hom f S T)
is-quasigroup-hom-is-prop {T = T} =
  Iso→is-hlevel! 1 eqv
  where
    open Quasigroup-on T
    private unquoteDecl eqv = declare-record-iso eqv (quote is-quasigroup-hom)

instance
  H-Level-is-quasigroup-hom
    : {f : A → B}
    → {S : Quasigroup-on A} {T : Quasigroup-on B}
    → ∀ {n} → H-Level (is-quasigroup-hom f S T) (suc n)
  H-Level-is-quasigroup-hom = prop-instance is-quasigroup-hom-is-prop
```
-->

<!--
```agda
module _ where
  open is-quasigroup-hom
  open Quasigroup-on

  Quasigroup-on-pathp
    : ∀ {A : I → Type ℓ}
    → {S : Quasigroup-on (A i0)} {T : Quasigroup-on (A i1)}
    → PathP (λ i → ∀ (x y : A i) → A i) (S ._⋆_) (T ._⋆_)
    → PathP (λ i → Quasigroup-on (A i)) S T
  Quasigroup-on-pathp {S = S} {T = T} p i ._⋆_ x y =
    p i x y
  Quasigroup-on-pathp {S = S} {T = T} p i .has-is-quasigroup =
    is-prop→pathp
      (λ i → is-quasigroup-is-prop {_⋆_ = p i})
      (S .has-is-quasigroup)
      (T .has-is-quasigroup)
      i
```
-->

Quasigroups and quasigroup homomorphisms form a [[thin structure]].

```agda
  Quasigroup-structure : ∀ ℓ → Thin-structure ℓ Quasigroup-on
```

<details>
<summary>
</summary>

```agda
  Quasigroup-structure ℓ .is-hom f A B .∣_∣ =
    is-quasigroup-hom f A B
  Quasigroup-structure ℓ .is-hom f A B .is-tr =
    is-quasigroup-hom-is-prop
  Quasigroup-structure ℓ .id-is-hom .pres-⋆ x y =
    refl
  Quasigroup-structure ℓ .∘-is-hom f g f-hom g-hom .pres-⋆ x y =
    ap f (g-hom .pres-⋆ x y) ∙ f-hom .pres-⋆ (g x) (g y)
  Quasigroup-structure ℓ .id-hom-unique p q =
    Quasigroup-on-pathp (ext (p .pres-⋆))
```
</details>

This gives us a tidy way to construct the category of quasigroups.

```agda
Quasigroups : ∀ ℓ → Precategory (lsuc ℓ) ℓ
Quasigroups ℓ = Structured-objects (Quasigroup-structure ℓ)

module Quasigroups {ℓ} = Cat.Reasoning (Quasigroups ℓ)

Quasigroup : (ℓ : Level) → Type (lsuc ℓ)
Quasigroup ℓ = Quasigroups.Ob {ℓ}
```

<!--
```agda
module Quasigroup {ℓ} (A : Quasigroup ℓ) where
  open Quasigroup-on (A .snd) public

  left-quasigroup : Left-quasigroup ℓ
  left-quasigroup = A .fst , left-quasigroup-on

  right-quasigroup : Right-quasigroup ℓ
  right-quasigroup = A .fst , right-quasigroup-on
```
-->

## Constructing quasigroups

The interfaces for `is-quasigroup`{.Agda} and `Quasigroup-on`{.Agda} are
deeply nested and contain some duplication, so we introduce some helper
functions for constructing them.

```agda
record make-quasigroup {ℓ} (A : Type ℓ) : Type ℓ where
  field
    quasigroup-is-set : is-set A
    _⋆_ : A → A → A
    _⧵_ : A → A → A
    _/_ : A → A → A

    /-invl : ∀ x y → (x / y) ⋆ y ≡ x
    /-invr : ∀ x y → (x ⋆ y) / y ≡ x
    ⧵-invr : ∀ x y → x ⋆ (x ⧵ y) ≡ y
    ⧵-invl : ∀ x y → x ⧵ (x ⋆ y) ≡ y
```

<!--
```agda
  to-is-quasigroup : is-quasigroup _⋆_
  to-is-quasigroup .is-quasigroup.has-is-left-quasigroup .is-left-quasigroup._⧵_ = _⧵_
  to-is-quasigroup .is-quasigroup.has-is-left-quasigroup .is-left-quasigroup.⧵-invr = ⧵-invr
  to-is-quasigroup .is-quasigroup.has-is-left-quasigroup .is-left-quasigroup.⧵-invl = ⧵-invl
  to-is-quasigroup .is-quasigroup.has-is-left-quasigroup .is-left-quasigroup.has-is-magma .is-magma.has-is-set = quasigroup-is-set
  to-is-quasigroup .is-quasigroup.has-is-right-quasigroup .is-right-quasigroup._/_ = _/_
  to-is-quasigroup .is-quasigroup.has-is-right-quasigroup .is-right-quasigroup./-invl = /-invl
  to-is-quasigroup .is-quasigroup.has-is-right-quasigroup .is-right-quasigroup./-invr = /-invr
  to-is-quasigroup .is-quasigroup.has-is-right-quasigroup .is-right-quasigroup.has-is-magma .is-magma.has-is-set = quasigroup-is-set

  to-quasigroup-on : Quasigroup-on A
  to-quasigroup-on .Quasigroup-on._⋆_ = _⋆_
  to-quasigroup-on .Quasigroup-on.has-is-quasigroup = to-is-quasigroup

  to-quasigroup : Quasigroup ℓ
  to-quasigroup .fst .∣_∣ = A
  to-quasigroup .fst .is-tr = quasigroup-is-set
  to-quasigroup .snd = to-quasigroup-on

open make-quasigroup using (to-is-quasigroup; to-quasigroup-on; to-quasigroup) public
```
-->
