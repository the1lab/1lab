```agda
open import 1Lab.Prelude

module Order.Proset where
```

<!--
```agda
private variable
  ℓ ℓ' : Level
  A : Type ℓ
```
-->

# Prosets

A **preorder** is a relation, valued in propositions, which is reflexive
and transitive. Preorders generalise partial orders by dropping the
requirement for antisymmetry. A type equipped with a preorder is called a
**protype**.

```agda
record isPreorder (R : A → A → Type ℓ') : Type (level-of A ⊔ ℓ') where
  field
    reflexive     : ∀ {x} → R x x
    transitive    : ∀ {x y z} → R x y → R y z → R x z
    propositional : ∀ {x y} → isProp (R x y)

open isPreorder
```

A **proset structure** on a type equips the type with a choice of
preorder $x \le y$. Additionally, we require that the type `be a
set`{.Agda ident=hasIsSet}, so that prosets and monotone maps form a
category.

```agda
record ProsetOn {ℓ'} (A : Type ℓ) : Type (ℓ ⊔ lsuc ℓ') where
  field
    _≤_           : A → A → Type ℓ'
    hasIsSet      : isSet A
    hasIsPreorder : isPreorder _≤_

  open isPreorder hasIsPreorder public

open ProsetOn

Proset : (ℓ : Level) → Type (lsuc ℓ)
Proset ℓ = Σ[ A ∈ Type ℓ ] (ProsetOn {ℓ' = ℓ} A)
```

Since the relation is required to be propositional, being a preorder is
a property, not structure.

```agda
isProp-isPreorder : {R : A → A → Type ℓ'} → isProp (isPreorder R)
isProp-isPreorder x y i .reflexive =
  y .propositional (x .reflexive) (y .reflexive) i
isProp-isPreorder x y i .transitive p q =
  y .propositional (x .transitive p q) (y .transitive p q) i
isProp-isPreorder x y i .propositional =
  isProp-isProp (x .propositional) (y .propositional) i
```

An **equivalence of prosets** is an equivalence whose underlying map
both preserves _and_ reflects the order relation. This is not the usual
definition of an equivalence of prosets, which is an equivalence with
monotone underlying map (and monotone inverse).

```agda
record Proset≃ (A B : Proset ℓ) (e : A .fst ≃ B .fst) : Type (lsuc ℓ) where
  private
    module A = ProsetOn (A .snd)
    module B = ProsetOn (B .snd)

  field
    pres-≤ : (x y : A .fst) → x A.≤ y ≡ e .fst x B.≤ e .fst y

open Proset≃
```

The `Proset`{.Agda} type is univalent, where its notion of equivalence
is `Proset≃`{.Agda}.

```agda
Proset-univalent : isUnivalent (HomT→Str (Proset≃ {ℓ = ℓ}))
Proset-univalent {ℓ = ℓ} = 
  autoUnivalentRecord
    (autoRecord (ProsetOn {ℓ = ℓ} {ℓ' = ℓ}) (Proset≃ {ℓ = ℓ})
      (record:
        field[ _≤_ by pres-≤ ]
        axiom[ hasIsSet by (λ x → isProp-isHLevel 2) ]
        axiom[ hasIsPreorder by (λ x → isProp-isPreorder {R = x ._≤_}) ]))
```

A **monotone map** between prosets is a function between the underlying
types that preserves the ordering. It can be shown that if an
equivalence `is monotone`{.Agda ident=isMonotone}, and has monotone
`inverse map`{.Agda ident=equiv→inverse}, then it is an `equivalence of
prosets`{.Agda ident=Proset≃}.

```agda
isMonotone : (A B : Proset ℓ) (e : A .fst → B .fst) → Type _
isMonotone (A , o) (B , o') f = (x y : A) → x ≤₁ y → f x ≤₂ f y
  where open ProsetOn o renaming (_≤_ to _≤₁_)
        open ProsetOn o' renaming (_≤_ to _≤₂_)

monotoneEqv→Proset≃ : {A B : Proset ℓ} (e : A .fst ≃ B .fst)
                    → isMonotone A B (e .fst)
                    → isMonotone B A (equiv→inverse (e .snd))
                    → Proset≃ A B e
monotoneEqv→Proset≃ {A = A} {B} (f , eqv) f-mono f⁻¹-mono .pres-≤ x y = ua eq' where
  module A = ProsetOn (A .snd)
  module B = ProsetOn (B .snd)
```

This is essentially because an equivalence with inverse map which
preserves the ordering is the same as an equivalence which preserves and
_reflects_ the ordering.

```agda
  f-reflects : (x y : _) → f x B.≤ f y → x A.≤ y
  f-reflects x y q =
    transport (λ i → equiv→retraction eqv x i A.≤ equiv→retraction eqv y i)
      (f⁻¹-mono (f x) (f y) q)

  eq' = propExt (A .snd .hasIsPreorder .propositional)
                (B .snd .hasIsPreorder .propositional)
                (f-mono x y) (f-reflects x y)
```
