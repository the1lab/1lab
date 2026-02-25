---
description: |
  We formalise _embeddings_, a homotopically well-behaved generalisation
  of injective functions. It's immediate from our definition that every
  injective function between sets is an embedding, and that every
  equivalence is an embedding.
---
<!--
```agda
open import 1Lab.Equiv.Fibrewise
open import 1Lab.HLevel.Universe
open import 1Lab.HLevel.Closure
open import 1Lab.Path.Reasoning
open import 1Lab.Path.Groupoid
open import 1Lab.Type.Sigma
open import 1Lab.Univalence
open import 1Lab.Type.Pi
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type
```
-->

```agda
module 1Lab.Function.Embedding where
```

<!--
```agda
private variable
  ℓ ℓ₁ : Level
  A B : Type ℓ
  w x : A
```
-->

# Embeddings {defines="embedding injective"}

One of the most important observations leading to the development of
categorical set theory is that injective maps _into_ a set $S$
correspond to maps _from_ $S$ _into_ a universe of propositions,
normally denoted $\Omega$. Classically, this object is $\Omega = \{ 0 ,
1 \}$, but there are other settings in which this idea makes sense
([elementary topoi]) where the _subobject classifier_ is not a coproduct
$1 \coprod 1$.

[elementary topoi]: https://ncatlab.org/nlab/show/elementary+topos

To develop this correspondence, we note that, if a map is
`injective`{.Agda} and its codomain is a [[set]], then all the
`fibres`{.Agda ident=fibre} $f^*(x)$ of $f$ are [[propositions]].

```agda
injective : (A → B) → Type _
injective f = ∀ {x y} → f x ≡ f y → x ≡ y

injective→is-embedding
  : is-set B → (f : A → B) → injective f
  → ∀ x → is-prop (fibre f x)
injective→is-embedding bset f inj x (f*x , p) (f*x' , q) =
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
has-prop-fibres→injective f prop {x} {y} p =
  ap fst (prop (f y) (x , p) (y , refl))

between-sets-injective≃has-prop-fibres
  : is-set A → is-set B → (f : A → B)
  → injective f ≃ (∀ x → is-prop (fibre f x))
between-sets-injective≃has-prop-fibres aset bset f = prop-ext
  (λ p q i x → aset _ _ (p x) (q x) i)
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
Subset-proj-embedding {B = B} Bprop x = Equiv→is-hlevel 1 (Fibre-equiv B x) (Bprop _)
```

<!--
```agda
∘-is-embedding : ∘-closed is-embedding
∘-is-embedding {A = A} {B = B} {f = f} {g = g} f-emb g-emb c = Equiv→is-hlevel 1
  (fibre-∘-≃ c)
  (Σ-is-hlevel 1 (f-emb c) (λ f-fib → g-emb (f-fib .fst)))

_∙emb_
  : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
  → A ↪ B → B ↪ C → A ↪ C
(f ∙emb g) .fst = g .fst ∘ f .fst
(f ∙emb g) .snd = ∘-is-embedding (g .snd) (f .snd)

infixr 30 _∙emb_

embedding→monic
  : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {f : A → B}
  → is-embedding f
  → ∀ {C : Type ℓ''} (g h : C → A) → f ∘ g ≡ f ∘ h → g ≡ h
embedding→monic {f = f} emb g h p =
  funext λ x → ap fst (emb _ (g x , refl) (h x , happly (sym p) x))

is-equiv→is-embedding
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f : A → B}
  → is-equiv f
  → is-embedding f
is-equiv→is-embedding eqv x = is-contr→is-prop (eqv .is-eqv x)

Equiv→Embedding
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → A ≃ B
  → A ↪ B
Equiv→Embedding e .fst = e .fst
Equiv→Embedding e .snd = is-equiv→is-embedding (e .snd)

Iso→Embedding
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → Iso A B
  → A ↪ B
Iso→Embedding f = Equiv→Embedding (Iso→Equiv f)

monic→is-embedding
  : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {f : A → B}
  → is-set B
  → (∀ {C : Set ℓ''} (g h : ∣ C ∣ → A) → f ∘ g ≡ f ∘ h → g ≡ h)
  → is-embedding f
monic→is-embedding {f = f} bset monic =
  injective→is-embedding bset _ λ {x} {y} p →
    happly (monic {C = el (Lift _ ⊤) (λ _ _ _ _ i j → lift tt)} (λ _ → x) (λ _ → y) (funext (λ _ → p))) _

right-inverse→injective
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → {f : A → B} (g : B → A)
  → is-right-inverse f g → injective f
right-inverse→injective g rinv {x} {y} p = sym (rinv x) ∙ ap g p ∙ rinv y
```
-->

## As fully faithful morphisms

A [[fully faithful functor]] is a functor whose action on morphisms is
an isomorphism everywhere. By the "types are higher groupoids" analogy,
functors are functions, so we're left to consider: what is a fully
faithful _function_? The answer turns out to be precisely "an
embedding", as long as we interpret "fully faithful" to mean "action on
morphisms is an _equivalence_" everywhere.

```agda
module _ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f : A → B} where
  embedding-lemma : (∀ x → is-contr (fibre f (f x))) → is-embedding f
  embedding-lemma cffx y (x , p) q =
    is-contr→is-prop (subst is-contr (ap (fibre f) p) (cffx x)) (x , p) q

  cancellable→embedding : (∀ {x y} → (f x ≡ f y) ≃ (x ≡ y)) → is-embedding f
  cancellable→embedding eqv =
    embedding-lemma λ x → Equiv→is-hlevel 0 (Σ-ap-snd (λ _ → eqv)) $
      contr (x , refl) λ (y , p) i → p (~ i) , λ j → p (~ i ∨ j)

  embedding→cancellable : is-embedding f → ∀ {x y} → is-equiv {B = f x ≡ f y} (ap f)
  embedding→cancellable emb {x} {y} = is-iso→is-equiv λ where
    .is-iso.from p → ap fst (emb (f y) (x , p) (y , refl))
    .is-iso.rinv p → flatten-∨-square (ap snd (emb (f y) (x , p) (y , refl)))
    .is-iso.linv → J (λ y p → ap fst (emb (f y) (x , ap f p) (y , refl)) ≡ p)
      (ap-square fst (is-prop→is-set (emb (f x)) _ _ (emb (f x) (x , refl) (x , refl)) refl))

  equiv→cancellable : is-equiv f → ∀ {x y} → is-equiv {B = f x ≡ f y} (ap f)
  equiv→cancellable eqv {x} {y} =
    is-iso→is-equiv λ where
      .is-iso.from p → sym (f.η _) ∙∙ ap f.from p ∙∙ f.η _
      .is-iso.rinv α →
          ap-∙∙ f _ _ _
        ∙ ap₂ (λ a b → _∙∙_∙∙_ {z = f y} a (ap f (ap f.from α)) b) (ap sym (f.zig _)) (f.zig y)
        ∙ double-composite _ _ _ ∙ ap₂ _∙_ refl (sym (homotopy-natural f.ε α))
        ∙ ∙-cancell _ _
      .is-iso.linv α → double-composite _ _ _
        ∙ ap₂ _∙_ refl (sym (homotopy-natural f.η α))
        ∙ ∙-cancell _ _
    where module f = Equiv (_ , eqv)
```

Note that, while `equiv→cancellable`{.Agda} immediately follows by
composing `is-equiv→is-embedding`{.Agda} and `embedding→cancellable`{.Agda},
the inverse map we get from that isn't so good, so we define it explicitly
instead.

<!--
```agda
  cancellable→embedding'
    : (inj : injective f) → (∀ {x y} (p : f x ≡ f y) → ap f (inj p) ≡ p)
    → is-embedding f
  cancellable→embedding' i p = embedding-lemma λ x → contr (x , refl) λ where
    (x , q) → Σ-pathp (i (sym q)) (commutes→square (ap (_∙ q) (p _) ∙∙ ∙-invl _ ∙∙ sym (∙-idr _)))

  embedding-lemma' : (∀ x y → Path (fibre f (f x)) (x , refl) y) → is-embedding f
  embedding-lemma' cffx = embedding-lemma λ x → contr (x , refl) (cffx x)

  abstract
    embedding→is-hlevel
      : ∀ n → is-embedding f
      → is-hlevel B (suc n)
      → is-hlevel A (suc n)
    embedding→is-hlevel n emb a-hl = Equiv→is-hlevel (suc n) (Total-equiv f) $
      Σ-is-hlevel (suc n) a-hl λ x → is-prop→is-hlevel-suc (emb x)

ap-equiv
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (e : A ≃ B) {x y : A}
  → (x ≡ y) ≃ (e .fst x ≡ e .fst y)
ap-equiv e = _ , equiv→cancellable (e .snd)

embedding→cancellableP
  : ∀ {ℓ ℓ'} {A : I → Type ℓ} {B : I → Type ℓ'}
  → (f : ∀ i → A i → B i) → (∀ i → is-embedding (f i))
  → ∀ {x y} → is-equiv {A = PathP A x y} (apd f)
embedding→cancellableP f emb {x} {y} = is-iso→is-equiv record where
  from p i = is-prop→pathp (λ i → emb i (p i)) (x , refl) (y , refl) i .fst
  rinv p j i = is-prop→pathp (λ i → emb i (p i)) (x , refl) (y , refl) i .snd j
  linv p j i = is-prop→squarep (λ _ i → emb i (apd f p i)) refl
    (is-prop→pathp (λ i → emb i (apd f p i)) (x , refl) (y , refl))
    (p ,ₚ λ i → refl)
    refl j i .fst

-- Same as above, this follows from the previous lemmas but we get a
-- better inverse this way.
equiv→cancellableP
  : ∀ {ℓ ℓ'} {A : I → Type ℓ} {B : I → Type ℓ'}
  → (f : ∀ i → A i → B i) → (∀ i → is-equiv (f i))
  → ∀ {x y} → is-equiv {A = PathP A x y} (apd f)
equiv→cancellableP f f-eqv {x} {y} = is-iso→is-equiv record where
  module f i = Equiv (_ , f-eqv i)

  sides : ∀ p i j → Partial (∂ i ∨ ~ j) _
  sides p i = λ where
    j (j = i0) → f.from i (p i)
    j (i = i0) → f.η i0 x j
    j (i = i1) → f.η i1 y j

  from p i = hcomp (∂ i) (sides p i)
  linv p j i = hcomp-unique (∂ i) (sides (apd f.to p) i)
    (λ j → inS (f.η i (p i) j)) j
  rinv p j i = hcomp (∂ i ∨ ∂ j) λ where
    k (k = i0) → f.to i (f.from i (p i))
    k (i = i0) → f.zig i0 x j k
    k (i = i1) → f.zig i1 y j k
    k (j = i0) → f.to i (hfill (∂ i) k (sides p i))
    k (j = i1) → f.ε i (p i) k

apd-equiv
  : ∀ {ℓ ℓ'} {A : I → Type ℓ} {B : I → Type ℓ'}
  → (e : ∀ i → A i ≃ B i)
  → ∀ {x y} → PathP A x y ≃ PathP B (e i0 .fst x) (e i1 .fst y)
apd-equiv e = apd (λ i → e i .fst) , equiv→cancellableP _ (λ i → e i .snd)

Lift-is-embedding : ∀ {ℓ} ℓ' → is-embedding {A = Type ℓ} (Lift ℓ')
Lift-is-embedding ℓ' = cancellable→embedding λ {x} {y} →
  Lift ℓ' x ≡ Lift ℓ' y ≃⟨ _ , univalence ⟩
  Lift ℓ' x ≃ Lift ℓ' y ≃⟨ ≃-ap Lift-≃ Lift-≃ ⟩
  x ≃ y                 ≃⟨ _ , univalence⁻¹ ⟩
  x ≡ y                 ≃∎
```
-->
