```
open import 1Lab.Univalence
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

module 1Lab.Equiv.Embedding where
```

<!--
```
private variable
  ℓ : Level
  A B : Type ℓ
```
-->

# Embeddings

In HoTT, the notion of _injective map_ is not well-behaved for types
that are not sets. Thus, we strengthen the notion: Rather than using
`injective`{.Agda}, we use `isEmbedding`{.Agda}.

```
injective : (A → B) → Type _
injective f = {x y : _} → f x ≡ f y → x ≡ y

isEmbedding : (A → B) → Type _
isEmbedding f = {x y : _} → isEquiv (λ (p : x ≡ y) → ap f p)
```

One of the canonical sources of embeddings are the _subtype inclusions_.
A subtype of `A` is given by a predicate `B : A → Type`, such that `B x`
is always a proposition:

```
Subset-proj-embedding : {a b : _} {A : Type a} {B : A → Type b}
                      → ((x : A) → isProp (B x))
```

When this is the case, we have that the `first projection`{.Agda
ident=fst} is an embedding:

```
                      → isEmbedding (fst {A = A} {B = B})
```

<details>
<summary>
The argument is not enlightening, but the gist of it is that since the
second projection essentially does not matter (it is a map between
propositions), then we can always recover an equality of pairs from an
equality of their first components, in a uniform way.
</summary>
```
Subset-proj-embedding {A = A} {B = B} prop .isEqv path = contr cent contract where
  centreP : _ ≡ _
  centreP = Σ-PathP path (isProp→PathP (λ _ → prop _) _ _)

  cent : fibre (λ (p : _ ≡ _) → ap fst p) path
  cent = centreP , refl

  contract : (z : _) → cent ≡ z
  contract (z , p) = Σ-PathP ctrP≡ (ap (λ x → sym (snd x)) fzsingl) where
    fzsingl : Path (Singleton path) (path , refl) (ap fst z , sym p)
    fzsingl = isContr-Singleton _

    ctrSnd : SquareP (λ i j → B (fzsingl i .fst j)) (ap snd centreP) (ap snd z) _ _
    ctrSnd = isProp→SquareP (λ _ _ → prop _) _ _ _ _

    ctrP≡ : centreP ≡ z
    ctrP≡ i = Σ-PathP (fzsingl i .fst) (ctrSnd i)
```
</details>

It can be seen that embeddings are a generalisation of injective
functions (hence, of subset inclusions) by considering how embeddings
behave when applied to sets:

```
injective-sets→embedding : isSet A → isSet B → (f : A → B)
                         → injective f
                         → isEmbedding f
```

In this case, we have that both `f x ≡ f y` and `x ≡ y` are mere
propositions, so biimplication becomes equivalence:

```
injective-sets→embedding Aset Bset f injective =
  isIso→isEquiv (iso injective (λ _ → Bset _ _ _ _) (λ _ → Aset _ _ _ _))
```
