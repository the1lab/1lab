---
description: |
  We formalise _embeddings_, a homotopically well-behaved generalisation
  of injective functions. It's immediate from our definition that every
  injective function between sets is an embedding, and that every
  equivalence is an embedding.
---
```agda
open import 1Lab.HLevel.Retracts
open import 1Lab.HLevel.Universe
open import 1Lab.Path.Groupoid
open import 1Lab.Type.Sigma
open import 1Lab.Univalence
open import 1Lab.Type.Pi
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

One of the most important observations leading to the development of
categorical set theory is that injective maps _into_ a set $S$
correspond to maps _from_ $S$ _into_ a universe of propositions,
normally denoted $\Omega$. Classically, this object is $\Omega = \{ 0 ,
1 \}$, but there are other settings in which this idea makes sense
([elementary topoi]) where the _subobject classifier_ is not a coproduct
$1 \coprod 1$.

[elementary topoi]: https://ncatlab.org/nlab/show/elementary+topos

To develop this correspondence, we note that, if a map is
`injective`{.Agda} and its codomain is a [set], then all the
`fibres`{.Agda} $f^*(x)$ of $f$ are [propositions].

[sets]: 1Lab.HLevel.html#is-set
[propositions]: 1Lab.HLevel.html#is-prop

```agda
injective : (A → B) → Type _
injective f = ∀ {x y} → f x ≡ f y → x ≡ y

injective-between-sets→has-prop-fibres
  : is-set B → (f : A → B) → injective f
  → ∀ x → is-prop (fibre f x)
injective-between-sets→has-prop-fibres bset f inj x (f*x , p) (f*x′ , q) =
  Σ-prop-path (λ x → bset _ _) (inj (p ∙ sym q))
```

In fact, this condition is not only necessary, it is also sufficient.
Thus, we conclude that, **for maps between sets**, these notions are
equivalent, and we could take either as the definition of "subset
inclusion".

```agda
has-prop-fibres→injective
  : (f : A → B) → (∀ x → is-prop (fibre f x))
  → injective f
has-prop-fibres→injective _ prop p = ap fst (prop _ (_ , p) (_ , refl))

between-sets-injective≃has-prop-fibres
  : is-set A → is-set B → (f : A → B)
  → injective f ≃ (∀ x → is-prop (fibre f x))
between-sets-injective≃has-prop-fibres aset bset f =
  prop-ext (λ p q i x → aset _ _ (p x) (q x) i)
           (Π-is-hlevel 1 λ _ → is-prop-is-prop)
           (injective-between-sets→has-prop-fibres bset f)
           (has-prop-fibres→injective f)
```

However, for more general types, like the circle, this fails: A function
can have propositional fibres in at most one way, but a function can be
injective in more than one. Consider the following two witnesses of
injectivity for the identity map of the circle, i.e., two functions $x =
y → x = y$.

```agda
module _ where private
  open import 1Lab.HIT.S1

  circle-id : S¹ → S¹
  circle-id p = p
```

The first is the boring option: it just gives back the same path,
unchanged. The second is more interesting: By doing circle induction, we
can consider the cases separately, and in the case where $y =
\id{base}$, we add an extra twist onto the path:

```agda
  circle-id-inj₁ circle-id-inj₂ : injective circle-id
  circle-id-inj₁ p = p
  circle-id-inj₂ {x} =
    S¹-elim {P = λ y → x ≡ y → x ≡ y} (_∙ loop)
      (funext-dep λ p → to-pathp (subst-path-right _ _ ∙ lemma p))
      _
    where
      lemma : ∀ {x} {p1 p2 : x ≡ base}
            → PathP (λ i → x ≡ loop i) p1 p2
            → (p1 ∙ loop) ∙ loop ≡ p2 ∙ loop
      lemma path = ap (_∙ loop) (from-pathp path)
```

These functions are _not the same_! When given `refl`{.Agda},
`circle-id-inj₁`{.Agda} will give `refl`{.Agda} (because it's boring),
but the exciting function will give `loop`{.Agda}. And that ain't
`refl`{.Agda}.

```agda
  circle-id-inj₁≠inj₂ : circle-id-inj₁ ≡ circle-id-inj₂ → ⊥
  circle-id-inj₁≠inj₂ p = refl≠loop (happly p refl ∙ ∙-id-l _)
```

Since we want "is a subtype inclusion" to be a property --- that is, we
really want to _not_ care about _how_ a function is a subtype inclusion,
only that it is, we define **embeddings** as those functions which have
propositional fibres:

```agda
is-embedding : (A → B) → Type _
is-embedding f = ∀ x → is-prop (fibre f x)

_↪_ : Type ℓ → Type ℓ₁ → Type _
A ↪ B = Σ[ f ∈ (A → B) ] is-embedding f
```

Univalence --- specifically, the existence of classifying objects for
maps with $P$-fibres --- tells us that the embeddings into $B$
correspond to the families of propositional types over $B$.

```agda
subtype-classifier
  : ∀ {ℓ} {B : Type ℓ}
  → (Σ[ A ∈ Type ℓ ] (A ↪ B)) ≃ (B → Σ[ T ∈ Type ℓ ] (is-prop T))
subtype-classifier {ℓ} = Map-classifier {ℓ = ℓ} is-prop
```

A canonical source of embedding, then, are the first projections from
total spaces of propositional families. This is because, as
`Fibre-equiv`{.Agda} tells us, the fibre of $\pi_1$ over $x$ is
equivalent to "the space of possible second coordinates", i.e., $B(x)$.
Since $B(x)$ was assumed to be a prop., then so are the fibres of
`fst`{.Agda}.

```agda
Subset-proj-embedding
  : ∀ {B : A → Type ℓ} → (∀ x → is-prop (B x))
  → is-embedding {A = Σ B} fst
Subset-proj-embedding {B = B} Bprop x = is-hlevel≃ 1 (Fibre-equiv B x e⁻¹) (Bprop _)
```

!--
```agda
embedding→monic
  : ∀ {ℓ ℓ′ ℓ′′} {A : Type ℓ} {B : Type ℓ′} {f : A → B}
  → is-embedding f
  → ∀ {C : Type ℓ′′} (g h : C → A) → f ∘ g ≡ f ∘ h → g ≡ h
embedding→monic {f = f} emb g h p =
  funext λ x → ap fst (emb _ (g x , refl) (h x , happly (sym p) x))

monic-between-sets→is-embedding
  : ∀ {ℓ ℓ′ ℓ′′} {A : Type ℓ} {B : Type ℓ′} {f : A → B}
  → is-set B
  → (∀ {C : Set ℓ′′} (g h : ∣ C ∣ → A) → f ∘ g ≡ f ∘ h → g ≡ h)
  → is-embedding f
monic-between-sets→is-embedding {f = f} bset monic =
  injective-between-sets→has-prop-fibres bset _ λ {x} {y} p →
    happly (monic {C = Lift _ ⊤ , λ _ _ _ _ i j → lift tt} (λ _ → x) (λ _ → y) (funext (λ _ → p))) _
```
--
