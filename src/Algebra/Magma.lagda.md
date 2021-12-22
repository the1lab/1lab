
```agda
open import 1Lab.Prelude

module Algebra.Magma where
```

<!--
```agda
private variable
  ℓ ℓ₁ : Level
  A : Type ℓ
```
-->

# ∞-Magmas

In common mathematical parlance, a **magma** is a set equipped with a
binary operation. In HoTT, we free ourselves from considering sets as a
primitive, and generalise to ∞-groupoids: An **∞-magma** is a _type_
equipped with a binary operation.

```agda
is∞Magma : Type ℓ → Type ℓ
is∞Magma X = X → X → X
```

Since we can canonically identify the predicate `is∞Magma`{.Agda} with a
`Structure`{.Agda} built with the structure language, we automatically
get a notion of ∞-Magma homomorphism, and a proof that
`∞MagmaStr`{.Agda} is a `univalent structure`{.Agda ident=isUnivalent}.

```agda
∞MagmaStr : Structure ℓ is∞Magma
∞MagmaStr = tm→Structure (s∙ s→ (s∙ s→ s∙))

∞MagmaStr-univ : isUnivalent (∞MagmaStr {ℓ = ℓ})
∞MagmaStr-univ = tm→Structure-univalent (s∙ s→ (s∙ s→ s∙))
```

∞-magmas form a viable structure because magmas (and therefore their
higher version) do not axiomatize any _paths_ that would require
further coherence conditions. However, when considering structures with
equalities, like semigroups or loops, we must restrict ourselves to sets
to get a reasonable object, hence the field `hasIsSet`{.Agda}.
To be able to properly generalize over these notions, we define magmas
as ∞-magmas whose carrier type is a set.

# Magmas
```agda
record isMagma {A : Type ℓ} (_⋆_ : A → A → A) : Type ℓ where
```

A **magma** is a `set`{.Agda ident=isSet} equipped with an arbitrary
binary operation `⋆`, on which no further laws are imposed. 

```agda
  field
    hasIsSet : isSet A

  underlying-set : Set ℓ
  underlying-set = _ , hasIsSet
    
open isMagma public
```
    
Note that we do not generally benefit from the set truncation of
arbitrary magmas - however, practically all structures built upon
`isMagma`{.Agda} do, since they contain equality fields which would
require complicated if not outright undefinable coherence conditions.

It also allows us to show that being a magma is a _property_:

```agda
isProp-isMagma : {_⋆_ : A → A → A} → isProp (isMagma _⋆_)
isProp-isMagma x y i .hasIsSet = isProp-isHLevel 2 (x .hasIsSet) (y .hasIsSet) i
```

By turning the operation parameter into an additional piece of data, we
get the notion of a **magma structure** on a type, as well as the
notion of a magma in general by doing the same to the carrier type.

```agda
record MagmaOn (A : Type ℓ) : Type ℓ where
  field
    _⋆_ : A → A → A

    hasIsMagma : isMagma _⋆_
    
  open isMagma hasIsMagma public

Magma : (ℓ : Level) → Type (lsuc ℓ)
Magma ℓ = Σ MagmaOn
```

We then define what it means for an equivalence between the carrier
types of two given magmas to be an **equivalence of magmas**: it has to
preserve the magma operation.

```agda
record
  Magma≃ (A B : Magma ℓ) (e : A .fst ≃ B .fst) : Type ℓ where
  private
    module A = MagmaOn (A .snd)
    module B = MagmaOn (B .snd)

  field
    pres-⋆ : (x y : A .fst) → e .fst (x A.⋆ y) ≡ e .fst x B.⋆ e .fst y

open Magma≃
```

By using record machinery that transforms our given definition into an
equivalent `description`{.Agda ident=StrDesc}, we can see that
`MagmaOn`{.Agda} forms a univalent structure, which allows us to
characterise the path type between two magmas as the type of their
equivalences by making use of the general
`structure identity principle`{.Agda ident=SIP}.

```agda
Magma-univalent : isUnivalent {ℓ = ℓ} (HomT→Str Magma≃)
Magma-univalent {ℓ = ℓ} = autoUnivalentRecord
  (autoRecord (MagmaOn {ℓ = ℓ}) Magma≃
  (record:
    field[ MagmaOn._⋆_ by pres-⋆ ]
    axiom[ MagmaOn.hasIsMagma by (λ _ → isProp-isMagma) ]))

Magma≡ : {A B : Magma ℓ} → (A ≃[ HomT→Str Magma≃ ] B) ≃ (A ≡ B)
Magma≡ = SIP Magma-univalent
```

## The boolean implication magma

```agda
open import Data.Bool
```

To give a somewhat natural example for a magma that is neither
associative, commutative, nor has a two-sided identity element,
consider `boolean implication`{.Agda imp}. Since the booleans form a
set, this obviously defines a magma: 

```agda
private 
  isMagma-imp : isMagma imp
  isMagma-imp .hasIsSet = isSet-Bool
```

We show it is not commutative or associative by giving counterexamples:

```agda
  imp-not-commutative : ((x y : Bool) → imp x y ≡ imp y x) → ⊥
  imp-not-commutative commutative = true≠false (commutative false true)

  imp-not-associative : ((x y z : Bool) → imp (imp x y) z ≡ imp x (imp y z)) → ⊥
  imp-not-associative associative = true≠false (sym (associative false false false))
```

It also has no two-sided unit, as can be shown by case-splitting 
on the candidates:

```agda
  imp-not-unital : (x : Bool) → ((y : Bool) → imp x y ≡ y) → ((y : Bool) → imp y x ≡ y) → ⊥
  imp-not-unital false left-unital right-unital = true≠false (right-unital false)
  imp-not-unital true left-unital right-unital = true≠false (right-unital false)
```
