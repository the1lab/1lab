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
open import 1Lab.Equiv.Fibrewise
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

injective→is-embedding
  : is-set B → (f : A → B) → injective f
  → ∀ x → is-prop (fibre f x)
injective→is-embedding bset f inj x (f*x , p) (f*x′ , q) =
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
           (injective→is-embedding bset f)
           (has-prop-fibres→injective f)
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
module subtype-classifier {ℓ} {B : Type ℓ} = Equiv (subtype-classifier {B = B})
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
  → is-embedding {A = Σ A B} fst
Subset-proj-embedding {B = B} Bprop x = is-hlevel≃ 1 (Fibre-equiv B x e⁻¹) (Bprop _)
```

<!--
```agda
embedding→monic
  : ∀ {ℓ ℓ′ ℓ′′} {A : Type ℓ} {B : Type ℓ′} {f : A → B}
  → is-embedding f
  → ∀ {C : Type ℓ′′} (g h : C → A) → f ∘ g ≡ f ∘ h → g ≡ h
embedding→monic {f = f} emb g h p =
  funext λ x → ap fst (emb _ (g x , refl) (h x , happly (sym p) x))

monic→is-embedding
  : ∀ {ℓ ℓ′ ℓ′′} {A : Type ℓ} {B : Type ℓ′} {f : A → B}
  → is-set B
  → (∀ {C : Set ℓ′′} (g h : ∣ C ∣ → A) → f ∘ g ≡ f ∘ h → g ≡ h)
  → is-embedding f
monic→is-embedding {f = f} bset monic =
  injective→is-embedding bset _ λ {x} {y} p →
    happly (monic {C = el (Lift _ ⊤) (λ _ _ _ _ i j → lift tt)} (λ _ → x) (λ _ → y) (funext (λ _ → p))) _
```
-->

# As ff morphisms

A \r{fully faithful functor} is a functor whose action on morphisms is
an isomorphism everywhere. By the "types are higher groupoids" analogy,
functors are functions, so we're left to consider: what is a fully
faithful _function_? The answer turns out to be precisely "an
embedding", as long as we interpret "fully faithful" to mean "action on
morphisms is an _equivalence_" everywhere.

```agda
module _ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′} {f : A → B} where
  embedding-lemma : (∀ x → is-contr (fibre f (f x))) → is-embedding f
  embedding-lemma cffx y (x , p) q =
    is-contr→is-prop (subst is-contr (ap (fibre f) p) (cffx x)) (x , p) q

  cancellable→embedding : (∀ {x y} → (f x ≡ f y) ≃ (x ≡ y)) → is-embedding f
  cancellable→embedding eqv =
    embedding-lemma λ x → is-hlevel≃ 0 (Σ-ap-snd (λ _ → eqv e⁻¹)) $
      contr (x , refl) λ (y , p) i → p (~ i) , λ j → p (~ i ∨ j)

  embedding→cancellable : is-embedding f → ∀ {x y} → is-equiv {B = f x ≡ f y} (ap f)
  embedding→cancellable emb = total→equiv {f = λ y p → ap f {y = y} p}
    (is-contr→is-equiv
      (contr (_ , refl) λ (y , p) i → p i , λ j → p (i ∧ j))
      (contr (_ , refl) (is-hlevel≃ 1 (Σ-ap-snd λ _ → sym-equiv) (emb _) _)))
```
