```agda
open import 1Lab.Prelude

open import Order.Proset hiding (isMonotone)

module Order.Poset where
```

<!--
```agda
private variable
  ℓ ℓ' : Level
  A : Type ℓ
  R : A → A → Type ℓ
```
-->

# Posets

A **partial order** relation is a [preorder relation] that additionally
satisfies **antisymmetry**: If $x \le y$ and $y \le x$, then $x = y$. By
[Rijke's theorem], any type that admits a partial order relation is
automatically a [set], since we can take $R(x, y) = (x \le y) \land (y
\le x)$ as a reflexive relation which implies equality.

Using the language of enriched category theory, we can say that a poset
is a univalent category enriched over propositions.

[preorder relation]: Order.Proset.html#isPreorder
[Rijke's theorem]: 1Lab.HLevel.Sets.html#Rijke-isSet
[set]: 1Lab.HLevel.html#isSet

```agda
record isPartialOrder (R : A → A → Type ℓ') : Type (level-of A ⊔ ℓ') where
  field
    hasIsPreorder : isPreorder R
    antisym : ∀ {x y} → R x y → R y x → x ≡ y
  
  open isPreorder hasIsPreorder public
```

To prove that being a partial order is a property of an order relation,
we first establish the theorem claimed in the first paragraph: Any type
$A$ that admits a partial order relation $R$ is a set.

```agda
hasPartialOrder→isSet : ∀ {R : A → A → Type ℓ} → isPartialOrder R → isSet A
hasPartialOrder→isSet {A = A} {R = _≤_} ispo =
  Rijke-isSet {R = R'} reflexive' (λ { (x , y) → antisym x y }) isProp'
  where
    open isPartialOrder ispo
```

For the relation, we take $R(x, y) = (x \le y) \land (y \le x)$. By
antisymmetry, this implies $x = y$. Since propositions are closed under
products, this is a proposition.

```agda
    R' : A → A → Type _
    R' x y = (x ≤ y) × (y ≤ x)

    reflexive' : {x : A} → R' x x
    reflexive' = reflexive , reflexive

    isProp' : {x y : A} → isProp (R' x y)
    isProp' (a , b) (a' , b') i = propositional a a' i , propositional b b' i
```

This implies that the path component in `isPartialOrder`{.Agda} does not
get in the way of it being a proposition:

```agda
isProp-isPartialOrder : isProp (isPartialOrder R)
isProp-isPartialOrder x y i = p where
  open isPartialOrder

  p : isPartialOrder _
  p .hasIsPreorder = isProp-isPreorder (x .hasIsPreorder) (y .hasIsPreorder) i
  p .antisym p q = hasPartialOrder→isSet x _ _ (x .antisym p q) (y .antisym p q) i
```

A **poset** is a type equipped with a partial order relation. Since
admitting a preorder implies that the type is a set, it is not necessary
to additionally require that the type be a set.

```agda
record PosetOn {ℓ'} (A : Type ℓ) : Type (ℓ ⊔ lsuc ℓ') where
  field
    _≤_ : A → A → Type ℓ'
    hasIsPartialOrder : isPartialOrder _≤_

  open isPartialOrder hasIsPartialOrder public

Poset : ∀ (r ℓ : Level) → Type (lsuc (r ⊔ ℓ))
Poset r ℓ = Σ[ A ∈ Type ℓ ] (PosetOn {ℓ' = r} A)
```

An **equivalence of prosets** is an equivalence whose underlying map
both preserves _and_ reflects the order relation. This is not the usual
definition of an equivalence of prosets, which is an equivalence with
monotone underlying map (and monotone inverse).

```agda
record Poset≃ (A B : Poset ℓ ℓ') (e : A .fst ≃ B .fst) : Type (lsuc ℓ ⊔ ℓ') where
  private
    module A = PosetOn (A .snd)
    module B = PosetOn (B .snd)

  field
    pres-≤ : (x y : A .fst) → x A.≤ y ≡ e .fst x B.≤ e .fst y

open Poset≃
```

We can automatically prove that the type of posets is univalent, with
the relation being poset equivalence.

```agda
Poset-univalent : isUnivalent (HomT→Str (Poset≃ {ℓ = ℓ}))
Poset-univalent {ℓ = ℓ} = 
  autoUnivalentRecord
    (autoRecord (PosetOn {ℓ = ℓ} {ℓ' = ℓ}) (Poset≃ {ℓ = ℓ})
      (record:
        field[ _≤_ by pres-≤ ]
        axiom[ hasIsPartialOrder by (λ x → isProp-isPartialOrder) ]))
  where open PosetOn
```

A **monotone map** between posets is a function between the underlying
types that preserves the ordering. It can be shown that if an
equivalence `is monotone`{.Agda ident=isMonotone}, and has monotone
`inverse map`{.Agda ident=equiv→inverse}, then it is an `equivalence of
posets`{.Agda ident=Poset≃}.

```agda
isMonotone : (A B : Poset ℓ' ℓ) (e : A .fst → B .fst) → Type _
isMonotone (A , o) (B , o') f = (x y : A) → x ≤₁ y → f x ≤₂ f y
  where open PosetOn o  renaming (_≤_ to _≤₁_)
        open PosetOn o' renaming (_≤_ to _≤₂_)

monotoneEqv→Poset≃ : {A B : Poset ℓ' ℓ} (e : A .fst ≃ B .fst)
                   → isMonotone A B (e .fst)
                   → isMonotone B A (equiv→inverse (e .snd))
                   → Poset≃ A B e
monotoneEqv→Poset≃ {A = A} {B} (f , eqv) f-mono f⁻¹-mono .pres-≤ x y = ua eq' where
  module A = PosetOn (A .snd)
  module B = PosetOn (B .snd)
```

This is essentially because an equivalence with inverse map which
preserves the ordering is the same as an equivalence which preserves and
_reflects_ the ordering.

```agda
  f-reflects : (x y : _) → f x B.≤ f y → x A.≤ y
  f-reflects x y q =
    transport
      (λ i → equiv→retraction eqv x i A.≤ equiv→retraction eqv y i)
      (f⁻¹-mono (f x) (f y) q)

  eq' = propExt A.propositional B.propositional (f-mono x y) (f-reflects x y)
```

A map is said to be **antitone** if it _inverts_ the ordering relation:

```agda
isAntitone : (A B : Poset ℓ' ℓ) (e : A .fst → B .fst) → Type _
isAntitone (A , o) (B , o') f = (x y : A) → x ≤₁ y → f y ≤₂ f x
  where open PosetOn o  renaming (_≤_ to _≤₁_)
        open PosetOn o' renaming (_≤_ to _≤₂_)
```

# Meets and Joins

```agda
module _ (A : Poset ℓ' ℓ) where
  open PosetOn (A .snd)
```

Let $x$ and $y$ be elements of an arbitrary poset. We say that m is the
**meet** of $x$ and $y$ if it is the greatest element which is smaller
than $x$ and $y$. Diagramatically, we can draw a meet of $x$ and $y$ as
below.

```agda
  record isMeet (m x y : A .fst) : Type (ℓ' ⊔ ℓ) where
    field
      m≤x : m ≤ x
      m≤y : m ≤ y
      limiting : (a : A .fst) → a ≤ x → a ≤ y → a ≤ m
  open isMeet
```

Dually, the **join** of $x$ and $y$ is the least element which is
greater than $x$ and $y$.

```agda
  record isJoin (j x y : A .fst) : Type (ℓ' ⊔ ℓ) where
    field
      x≤j : x ≤ j
      y≤j : y ≤ j
      colimiting : (a : A .fst) → x ≤ a → y ≤ a → j ≤ a
  open isJoin
```

In a poset, because of antisymmetry, meets and joins are unique:

<!--
```
  private variable
    m m' j j' x y : A .fst
```
-->

```agda
  meet-unique : isMeet m x y → isMeet m' x y → m ≡ m'
  meet-unique m1 m2 = antisym m'≤m m≤m' where
    m≤m' = m1 .limiting _ (m2 .m≤x) (m2 .m≤y)
    m'≤m = m2 .limiting _ (m1 .m≤x) (m1 .m≤y)

  join-unique : isJoin j x y → isJoin j' x y → j ≡ j'
  join-unique m1 m2 = antisym j≤j' j'≤j where
    j≤j' = m1 .colimiting _ (m2 .x≤j) (m2 .y≤j)
    j'≤j = m2 .colimiting _ (m1 .x≤j) (m1 .y≤j)
```

<details>
<summary>
We also have that being a meet and being a join are properties of an
element, not structure.
</summary>

```agda
  isProp-isMeet : isProp (isMeet m x y)
  isProp-isMeet x y i .m≤x = propositional (x .m≤x) (y .m≤x) i
  isProp-isMeet x y i .m≤y = propositional (x .m≤y) (y .m≤y) i
  isProp-isMeet x y i .limiting a b c =
    propositional (x .limiting a b c) (y .limiting a b c) i

  isProp-isJoin : isProp (isJoin m x y)
  isProp-isJoin x y i .x≤j = propositional (x .x≤j) (y .x≤j) i
  isProp-isJoin x y i .y≤j = propositional (x .y≤j) (y .y≤j) i
  isProp-isJoin x y i .colimiting a b c =
    propositional (x .colimiting a b c) (y .colimiting a b c) i
```
</details>
