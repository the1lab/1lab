<!--
```agda
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Diagram.Initial where
```

<!--
```agda
module _ {o h} (C : Precategory o h) where
  open Cat.Reasoning C
```
-->

# Initial objects {defines="initial-object initial"}

An object $\bot$ of a category $\mathcal{C}$ is said to be **initial**
if there exists a _unique_ map to any other object:

```agda
  record is-initial (bot : Ob) : Type (o ⊔ h) where
    no-eta-equality
    field
      ¡ : ∀ {x} → Hom bot x
      ¡-unique : ∀ {x} (h : Hom bot x) → h ≡ ¡

    ¡-unique₂ : ∀ {x} (f g : Hom bot x) → f ≡ g
    ¡-unique₂ f g = ¡-unique f ∙ sym (¡-unique g)

  record Initial : Type (o ⊔ h) where
    no-eta-equality
    field
      bot  : Ob
      has-is-init : is-initial bot

    open is-initial has-is-init public
```

<!--
```agda
  {-# INLINE is-initial.constructor #-}
  {-# INLINE Initial.constructor #-}

module _ {o ℓ} {C : Precategory o ℓ} where
  open Cat.Reasoning C

  is-initial-is-prop : ∀ {b} → is-prop (is-initial C b)
  is-initial-is-prop b-init b-init' = path where
    open is-initial

    ¡-path : ∀ {x} → b-init .¡ {x} ≡ b-init' .¡ {x}
    ¡-path = b-init' .¡-unique (b-init .¡)

    path : b-init ≡ b-init'
    path i .¡ = ¡-path i
    path i .¡-unique h =
      is-prop→pathp (λ i → Hom-set _ _ h (¡-path i))
        (¡-unique b-init h)
        (¡-unique b-init' h) i

  instance
    H-Level-is-initial : ∀ {n} {b} → H-Level (is-initial C b) (suc n)
    H-Level-is-initial = prop-instance is-initial-is-prop

  private unquoteDecl initial-Σ-iso = declare-record-iso initial-Σ-iso (quote Initial)

  Initial≃is-initial
    : Initial C ≃ (Σ[ coapex ∈ Ob ] is-initial C coapex)
  Initial≃is-initial = Iso→Equiv initial-Σ-iso

  instance
    Extensional-Initial
      : ∀ {ℓr}
      → ⦃ sa : Extensional Ob ℓr ⦄
      → Extensional (Initial C) ℓr
    Extensional-Initial ⦃ sa ⦄ =
      embedding→extensional
        (Equiv→Embedding Initial≃is-initial ∙emb (fst , Subset-proj-embedding λ _ → hlevel 1))
        sa

  -- Flattened record to make constructing terminal objects using
  -- 'record where' and 'record { Module }' easier.
  record make-initial : Type (o ⊔ ℓ) where
    field
      bot : Ob
      ¡ : ∀ {x} → Hom bot x
      ¡-unique : ∀ {x} (h : Hom bot x) → h ≡ ¡

  to-initial : make-initial → Initial C
  {-# INLINE to-initial #-}
  to-initial mk = record
    { bot = bot
    ; has-is-init = record
      { ¡ = ¡
      ; ¡-unique = ¡-unique
      }
    }
    where open make-initial mk


  open Initial
```
-->

## Intuition

The intuition here is that we ought to think about an initial object as
having "the least amount of structure possible", insofar that it can be
mapped _into_ any other object. For the category of `Sets`{.Agda}, this
is the empty set; there is no required structure beyond "being a set",
so the empty set suffices.

<!--
[TODO: Reed M, 15/02/2022] Link to the categories in question
(once they exist!)
-->

In more structured categories, the situation becomes a bit more
interesting. Once our category has enough structure that we can't build
maps from a totally trivial thing, the initial object begins to behave
like a notion of **Syntax** for our category.  The idea here is that we
have a _unique_ means of interpreting our syntax into any other object,
which is exhibited by the universal map `¡`{.Agda}

## Universal property

An object $b : \cC$ is initial if and only if the type of morphisms
$\cC(b, x)$ is [[contractible]] for every $x : \cC$.

```agda
  hom-contr→is-initial
    : ∀ {b}
    → (∀ x → is-contr (Hom b x))
    → is-initial C b
  {-# INLINE hom-contr→is-initial #-}
  hom-contr→is-initial hom-contr = record
    { ¡ = λ {x} → hom-contr x .centre
    ; ¡-unique = λ {x} h → sym (hom-contr x .paths h)
    }

  is-initial→hom-contr
    : ∀ {b}
    → is-initial C b
    → ∀ x → is-contr (Hom b x)
  is-initial→hom-contr b-init x = contr b.¡ λ h → sym (b.¡-unique h)
    where module b = is-initial b-init
```


## Uniqueness

One important fact about initial objects is that they are **unique** up
to isomorphism:

```agda
  ⊥-unique : (i i' : Initial C) → bot i ≅ bot i'
  ⊥-unique i i' = make-iso (¡ i) (¡ i') (¡-unique₂ i' _ _) (¡-unique₂ i _ _)
```

Additionally, if $C$ is a category, then the space of initial objects is
a proposition:

```agda
  ⊥-is-prop : is-category C → is-prop (Initial C)
  ⊥-is-prop ccat x1 x2 = ext (Univalent.iso→path ccat (⊥-unique x1 x2))
```
