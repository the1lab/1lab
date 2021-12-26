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
    hasIsSet      : isSet A

open isPreorder
```

A **proset structure** on a type equips the type with a choice of
preorder $x \le y$.

```
record ProsetOn {ℓ'} (A : Type ℓ) : Type (ℓ ⊔ lsuc ℓ') where
  field
    _≤_           : A → A → Type ℓ'
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
isProp-isPreorder x y i .hasIsSet =
  isProp-isHLevel 2 (x .hasIsSet) (y .hasIsSet) i
```

An **equivalence of prosets** is an equivalence whose underlying map
preserves the ordering relation, up to equality. This is not the usual
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

Proset-univalent : isUnivalent (HomT→Str (Proset≃ {ℓ = ℓ}))
```

<!--
```
Proset-univalent {ℓ = ℓ} = 
  -- TODO: This causes an unsolved level meta and I literally don't have
  -- the faintest clue why. I also don't care enough to try to solve it
  -- anymore, lol.
  --
  autoUnivalentRecord
    (autoRecord (ProsetOn {ℓ = ℓ} {ℓ' = ℓ}) (Proset≃ {ℓ = ℓ})
      (record:
        field[ _≤_ by pres-≤ ]
        axiom[ hasIsPreorder by (λ x → isProp-isPreorder {R = x ._≤_}) ]))
  --
  -- Here's the macro expansion; It works, Agda just hates me.
  -- isUnivalent'→isUnivalent ProsetOn Proset≃
  -- (idfun
  --   ( (tm→⌜isUnivalent⌝ (s∙ s→ s∙ s→ s-const (Type ℓ)))

  --   → PropHelperType ProsetOn Proset≃
  --       (record: field[ _≤_ by pres-≤ ])
  --       (λ X₁ z → isSet X₁) hasIsSet

  --   → PropHelperType ProsetOn Proset≃
  --       (record: field[ _≤_ by pres-≤ ] axiom[ hasIsSet by (λ x → isProp-isHLevel 2) ])
  --       (λ X₁ z → isPreorder (z .fst .snd)) hasIsPreorder

  --   → isUnivalent' ProsetOn Proset≃)
  --  (λ ≤-univ isS-prop isP-prop →
  --     explicitUnivalentStr _ _
  --     (λ A B e streq i →
  --       λ { ._≤_ → ≤-univ (Σ-map₂ _≤_ A) (Σ-map₂ _≤_ B) e .fst (pres-≤ streq) i
  --         ; .hasIsSet
  --             → isS-prop .fst A B e (λ i₁ → tt , ≤-univ (Σ-map₂ _≤_ A) (Σ-map₂ _≤_ B) e .fst (pres-≤ streq) i₁) i
  --         ; .hasIsPreorder
  --             → isP-prop .fst A B e (λ i₁ →
  --                 (tt , equivFun (≤-univ (Σ-map₂ _≤_ A) (Σ-map₂ _≤_ B) e) (pres-≤ streq) i₁) ,
  --                 isS-prop .fst A B e (λ i₂ → tt , ≤-univ (Σ-map₂ _≤_ A) (Σ-map₂ _≤_ B) e .fst (pres-≤ streq) i₂) i₁)
  --               i
  --         })
  --     (λ A B e q → λ { .pres-≤ → equivInv (≤-univ (Σ-map₂ _≤_ A) (Σ-map₂ _≤_ B) e) (pathMap _≤_ q) })
  --     (λ A B e q j i →
  --       λ { ._≤_
  --             → equivSec (≤-univ (Σ-map₂ _≤_ A) (Σ-map₂ _≤_ B) e) (pathMap _≤_ q) j i
  --         ; .hasIsSet
  --             → isS-prop .snd A B e q (λ j₁ i₁ → tt , equivSec (≤-univ (Σ-map₂ _≤_ A) (Σ-map₂ _≤_ B) e) (pathMap _≤_ q) j₁ i₁) j i
  --         ; .hasIsPreorder
  --             → isP-prop .snd A B e q
  --               (λ j₁ i₁ →
  --                   (tt , equivSec (≤-univ (Σ-map₂ _≤_ A) (Σ-map₂ _≤_ B) e) (pathMap _≤_ q) j₁ i₁)
  --                   ,
  --                   isS-prop .snd A B e q
  --                   (λ j₂ i₂ → tt , equivSec (≤-univ (Σ-map₂ _≤_ A) (Σ-map₂ _≤_ B) e) (pathMap _≤_ q) j₂ i₂) j₁ i₁)
  --               j i
  --         })
  --     (λ A B e streq j → λ { .pres-≤ → equivRet (≤-univ (Σ-map₂ _≤_ A) (Σ-map₂ _≤_ B) e) (pres-≤ streq) j }))
  -- (tm→isUnivalent' (s∙ s→ s∙ s→ s-const (Type ℓ)))

  -- (derivePropHelper ProsetOn Proset≃
  --   (record: field[ _≤_ by pres-≤ ])
  --   (λ X₁ z → isSet X₁) hasIsSet
  --   (λ x → isProp-isHLevel 2))

  -- (derivePropHelper ProsetOn Proset≃
  --   (record: field[ _≤_ by pres-≤ ] axiom[ hasIsSet by (λ x → isProp-isHLevel 2) ])
  --   (λ X₁ z → isPreorder (z .fst .snd)) hasIsPreorder
  --   (λ x → isProp-isPreorder)))
  -- where
  --   open import 1Lab.Reflection
  --   open import 1Lab.Univalence.SIP.Record.Base
  --   open import 1Lab.Univalence.SIP.Record.Prop
  --   open import 1Lab.Univalence.SIP.Record
  --   open import 1Lab.Univalence.SIP.Auto
```
-->

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
monotoneEqv→Proset≃ {A = A} {B} (f , eqv) f-mono f¯¹-mono .pres-≤ x y = ua eq' where
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
      (f¯¹-mono (f x) (f y) q)

  eq' = propExt (A .snd .hasIsPreorder .propositional)
                (B .snd .hasIsPreorder .propositional)
                (f-mono x y) (f-reflects x y)
```