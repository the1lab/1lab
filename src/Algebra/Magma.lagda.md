
```agda
open import 1Lab.Prelude

module Algebra.Magma where
```

<!--
```
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

Generalising magmas to ∞-magmas does not pose a problem because ∞-magmas
do not have any _paths_. However, when considering structures with
equalities, like semigroups, we must restrict ourselves to sets to get a
coherent object, hence the field `hasIsSet`{.Agda}. In order to properly set up
the algebraic hierarchy, we define general magmas anyways.

# Magmas
```agda
record isMagma {A : Type ℓ} (_⋆_ : A → A → A) : Type ℓ where
```

A **magma** is a `set`{.Agda ident=isSet} equipped with an arbitrary binary operation `⋆`.

```agda
  field
    hasIsSet : isSet A
    
open isMagma public
```
    
Note that we do not generally benefit from the set truncation of arbitrary magmas - however,
practically all structures built upon `isMagma`{.Agda} do, since they contain equality fields
which would require complicated if not outright undefinable coherence conditions.

It also allows us to show that being a magma is a _property_:

```agda
isProp-isMagma : {_⋆_ : A → A → A} → isProp (isMagma _⋆_)
isProp-isMagma x y i .hasIsSet = isProp-isHLevel 2 (x .hasIsSet) (y .hasIsSet) i
```

By turning the operation parameter into an additional piece of data, we get the notion of
a **magma structure** on a type.

```agda
record MagmaOn (A : Type ℓ) : Type ℓ where
  field
    _⋆_ : A → A → A

    hasIsMagma : isMagma _⋆_
    
  open isMagma hasIsMagma public

open MagmaOn

Magma : (ℓ : Level) → Type (lsuc ℓ)
Magma ℓ = Σ MagmaOn
```
STUB STUB STUB

```agda
record
  Magma≃ (A B : Σ (MagmaOn {ℓ = ℓ})) (e : A .fst ≃ B .fst) : Type ℓ where
  private
    module A = MagmaOn (A .snd)
    module B = MagmaOn (B .snd)

  field
    pres-⋆ : (x y : A .fst) → e .fst (x A.⋆ y) ≡ e .fst x B.⋆ e .fst y

open Magma≃
```

STUB STUB STUB

```agda
Magma-univalent : isUnivalent {ℓ = ℓ} (HomT→Str Magma≃)
Magma-univalent {ℓ = ℓ} = autoUnivalentRecord
  (autoRecord (MagmaOn {ℓ = ℓ}) Magma≃
  (record:
    field[ _⋆_ by pres-⋆ ]
    axiom[ hasIsMagma by (λ _ → isProp-isMagma) ]))

Magma≡ : {A B : Magma ℓ} → (A ≃[ HomT→Str Magma≃ ] B) ≃ (A ≡ B)
Magma≡ = SIP Magma-univalent
```
