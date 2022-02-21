```agda
open import 1Lab.Type.Sigma
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
  ℓ ℓ₁ : Level
  A B : Type ℓ
  w x : A
```
-->

# Embeddings

In HoTT, the notion of _injective map_ is not well-behaved for types
that are not sets. Thus, we strengthen the notion: Rather than using
`injective`{.Agda}, we use `is-embedding`{.Agda}.

```agda
injective : (A → B) → Type _
injective f = {x y : _} → f x ≡ f y → x ≡ y

is-embedding : (A → B) → Type _
is-embedding f = {x y : _} → is-equiv (λ (p : x ≡ y) → ap f p)

_↪_ : Type ℓ → Type ℓ₁ → Type (ℓ ⊔ ℓ₁)
A ↪ B = Σ[ f ∈ (A → B) ] is-embedding f
```

One of the canonical sources of embeddings are the _subtype inclusions_.
A subtype of `A` is given by a predicate `B : A → Type`, such that `B x`
is always a proposition.  When this is the case, we have that the `first
projection`{.Agda ident=fst} is an embedding:

```agda
Subset-proj-embedding
  : ∀ {a b} {A : Type a} {B : A → Type b}
  → ((x : A) → is-prop (B x))
  → is-embedding (fst {A = A} {B = B})
Subset-proj-embedding bp =
  is-iso→is-equiv (is-iso.inverse (is-equiv→is-iso (Σ-prop-path-is-equiv bp)))
```

It can be seen that embeddings are a generalisation of injective
functions (hence, of subset inclusions) by considering how embeddings
behave when applied to sets:

```agda
injective-sets→embedding : is-set A → is-set B → (f : A → B)
                         → injective f
                         → is-embedding f
```

In this case, we have that both `f x ≡ f y` and `x ≡ y` are mere
propositions, so biimplication becomes equivalence:

```agda
injective-sets→embedding Aset Bset f injective =
  is-iso→is-equiv (iso injective (λ _ → Bset _ _ _ _) (λ _ → Aset _ _ _ _))
```

An equivalent characterisation of the embeddings is that they are the
types with `propositional`{.Agda ident=is-prop} `fibres`{.Agda
ident=fibre}.

<!--
```
private
  ap-fibre→PathP
    : {f : A → B}
    → (p : f w ≡ f x)
    → (fi : fibre (ap f) p)
    → PathP (λ i → fibre f (p i)) (w , refl) (x , refl)
  ap-fibre→PathP p (q , r) i = q i , λ j → r j i

  PathP→ap-fibre
    : {f : A → B}
    → (p : f w ≡ f x)
    → (pp : PathP (λ i → fibre f (p i)) (w , refl) (x , refl))
    → fibre (ap f) p
  PathP→ap-fibre p pp = (λ i → fst (pp i)) , (λ j i → snd (pp i) j)

PathP≡ap-fibre
  : {f : A → B}
  → (p : f w ≡ f x)
  → PathP (λ i → fibre f (p i)) (w , refl) (x , refl) ≡ fibre (ap f) p
PathP≡ap-fibre p
  = Iso→Path (PathP→ap-fibre p , iso (ap-fibre→PathP p) (λ _ → refl) (λ _ → refl))
```
-->

```agda
fibres-are-prop→is-embedding 
  : (f : A → B) → ((x : B) → is-prop (fibre f x))
  → is-embedding f
fibres-are-prop→is-embedding f prop-fib {w} {x} .is-eqv y =
  subst is-contr (PathP≡ap-fibre y)
    (is-prop→PathP-is-contr (λ i → prop-fib (y i)) (w , refl) (x , refl))
```
