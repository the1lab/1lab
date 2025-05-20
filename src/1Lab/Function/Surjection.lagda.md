<!--
```agda
open import 1Lab.Function.Embedding
open import 1Lab.Reflection.HLevel
open import 1Lab.HIT.Truncation
open import 1Lab.HLevel.Closure
open import 1Lab.Type.Sigma
open import 1Lab.Univalence
open import 1Lab.Inductive
open import 1Lab.Type.Pi
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

open import Meta.Idiom
open import Meta.Bind
```
-->

```agda
module 1Lab.Function.Surjection where
```

<!--
```agda
private variable
  ℓ ℓ' ℓ'' : Level
  A B C : Type ℓ
  P Q : A → Type ℓ'
  f g : A → B
```
-->

# Surjections {defines=surjection}

A function $f : A \to B$ is a **surjection** if, for each $b : B$, we
have $\| f^*b \|$: that is, all of its [[fibres]] are inhabited. Using
the notation for [[mere existence|merely]], we may write this as

$$
\forall (b : B),\ \exists (a : A),\ f(a) = b
$$.

which is evidently the familiar notion of surjection.

```agda
is-surjective : (A → B) → Type _
is-surjective f = ∀ b → ∥ fibre f b ∥
```

To abbreviate talking about surjections, we will use the notation $A
\epi B$, pronounced "$A$ **covers** $B$".

```agda
_↠_ : Type ℓ → Type ℓ' → Type (ℓ ⊔ ℓ')
A ↠ B = Σ[ f ∈ (A → B) ] is-surjective f
```

The notion of surjection is intimately connected with that of
[[quotient]], and in particular with the elimination principle into
[[propositions]]. We think of a surjection $A \to B$ as expressing that $B$
can be "glued together" by [[introducing paths between|path]] the
elements of $A$. Since any family of propositions respects these new
paths, we can prove a property of $B$ by showing it for the "generators"
coming from $A$:

```agda
is-surjective→elim-prop
  : (f : A ↠ B)
  → ∀ {ℓ} (P : B → Type ℓ)
  → (∀ x → is-prop (P x))
  → (∀ a → P (f .fst a))
  → ∀ x → P x
is-surjective→elim-prop (f , surj) P pprop pfa x =
  ∥-∥-rec (pprop _) (λ (x , p) → subst P p (pfa x)) (surj x)
```

When the type $B$ is a set, we can actually take this analogy all the
way to its conclusion: Given any cover $f : A \epi B$, we can produce an
equivalence between $B$ and the quotient of $A$ under the [[congruence]]
induced by $f$. See [[surjections are quotient maps]].

## Closure properties

The class of surjections contains the identity --- and thus every
equivalence --- and is closed under composition.

```agda
∘-is-surjective
  : {f : B → C} {g : A → B}
  → is-surjective f
  → is-surjective g
  → is-surjective (f ∘ g)
∘-is-surjective {f = f} fs gs x = do
  (f*x , p) ← fs x
  (g*fx , q) ← gs f*x
  pure (g*fx , ap f q ∙ p)

id-is-surjective : is-surjective {A = A} id
id-is-surjective x = inc (x , refl)

is-equiv→is-surjective : {f : A → B} → is-equiv f → is-surjective f
is-equiv→is-surjective eqv x = inc (eqv .is-eqv x .centre)
```

Surjections also are closed under a weaker form of [[two-out-of-three]]:
if $f \circ g$ is surjective, then $f$ must also be surjective.

```agda
is-surjective-cancelr
  : {f : B → C} {g : A → B}
  → is-surjective (f ∘ g)
  → is-surjective f
is-surjective-cancelr {g = g} fgs c = do
  (fg*x , p) ← fgs c
  pure (g fg*x , p)
```

<!--
```agda
Equiv→Cover : A ≃ B → A ↠ B
Equiv→Cover f = f .fst , is-equiv→is-surjective (f .snd)
```
-->

## Relationship with equivalences

We have defined [[equivalences]] to be the maps with [[contractible]]
fibres; and surjections to be the maps with _inhabited_ fibres. It
follows that a surjection is an equivalence _precisely if_ its fibres
are also [[propositions]]; in other words, if it is an [[embedding]].

```agda
embedding-surjective→is-equiv
  : {f : A → B}
  → is-embedding f
  → is-surjective f
  → is-equiv f
embedding-surjective→is-equiv f-emb f-surj .is-eqv x = ∥-∥-out! do
  pt ← f-surj x
  pure $ is-prop∙→is-contr (f-emb x) pt
```

<!--
```agda
injective-surjective→is-equiv
  : {f : A → B}
  → is-set B
  → injective f
  → is-surjective f
  → is-equiv f
injective-surjective→is-equiv b-set f-inj =
  embedding-surjective→is-equiv (injective→is-embedding b-set _ f-inj)

injective-surjective→is-equiv!
  : {f : A → B} ⦃ b-set : H-Level B 2 ⦄
  → injective f
  → is-surjective f
  → is-equiv f
injective-surjective→is-equiv! =
  injective-surjective→is-equiv (hlevel 2)
```
-->

## Surjectivity and images

A map $f : A \to B$ is surjective if and only if the inclusion of the
image of $f$ into $B$ is an [[equivalence]].

```agda
surjective-iff-image-equiv
  : ∀ {f : A → B}
  → is-surjective f ≃ is-equiv {A = image f} fst
```

First, note that the fibre of the inclusion of the image of $f$ at $b$
is the [[propositional truncation]] of the fibre of $f$ at $b$, by
construction. Asking for this inclusion to be an equivalence is the same as
asking for those fibres to be [[contractible]], which thus amounts to
asking for the fibres of $f$ to be [[merely]] inhabited, which is the
definition of $f$ being surjective.

```agda
surjective-iff-image-equiv {A = A} {B = B} {f = f} =
  begin-≃⁻¹
    is-equiv fst                            ≃⟨ is-equiv≃fibre-is-contr ⟩
    (∀ b → is-contr (fibre fst b))          ≃⟨ Π-cod≃ (λ b → is-hlevel-ap 0 (Fibre-equiv _ _)) ⟩
    (∀ b → is-contr (∃[ a ∈ A ] (f a ≡ b))) ≃⟨ Π-cod≃ (λ b → is-prop→is-contr-iff-inhabited (hlevel 1)) ⟩
    (∀ b → ∃[ a ∈ A ] (f a ≡ b))            ≃⟨⟩
    is-surjective f                         ≃∎
```

# Split surjective functions

:::{.definition #surjective-splitting}
A **surjective splitting** of a function $f : A \to B$ consists of a designated
element of the fibre $f^*b$ for each $b : B$.
:::

```agda
surjective-splitting : (A → B) → Type _
surjective-splitting f = ∀ b → fibre f b
```

Note that unlike "being surjective", a surjective splitting of $f$ is a *structure*
on $f$, not a property. This difference becomes particularly striking when we
look at functions into [[contractible]] types: if $B$ is contractible,
then the type of surjective splittings of a function $f : A \to B$ is equivalent to $A$.

```agda
cod-contr→surjective-splitting≃dom
  : (f : A → B)
  → is-contr B
  → surjective-splitting f ≃ A
```

First, recall that dependent functions $(a : A) \to B(a)$ out of a contractible type are
equivalent to an element of $B$ at the centre of contraction, so $(b : B) \to f^*(b)$ is
equivalent to an element of the fibre of $f$ at the centre of contraction of $B$. Moreover,
the type of paths in $B$ is also contractible, so that fibre is equivalent to $A$.

```agda
cod-contr→surjective-splitting≃dom {A = A} f B-contr =
  (∀ b → fibre f b)         ≃⟨ Π-contr-eqv B-contr ⟩
  fibre f (B-contr .centre) ≃⟨ Σ-contract (λ _ → Path-is-hlevel 0 B-contr) ⟩
  A                         ≃∎
```

In contrast, if $B$ is contractible, then $f : A \to B$ is surjective if and only
if $A$ is merely inhabited.

```agda
cod-contr→is-surjective-iff-dom-inhab
  : (f : A → B)
  → is-contr B
  → is-surjective f ≃ ∥ A ∥
cod-contr→is-surjective-iff-dom-inhab {A = A} f B-contr =
  (∀ b → ∥ fibre f b ∥) ≃⟨ unique-choice B-contr ⟩
  ∥ (∀ b → fibre f b) ∥ ≃⟨ ∥-∥-ap (cod-contr→surjective-splitting≃dom f B-contr) ⟩
  ∥ A ∥                 ≃∎
```

In light of this, we provide the following definition.

:::{.definition #split-surjective}
A function $f : A \to B$ is **split surjective** if there merely exists a
surjective splitting of $f$.
:::

```agda
is-split-surjective : (A → B) → Type _
is-split-surjective f = ∥ surjective-splitting f ∥
```

Every split surjective map is surjective.

```agda
is-split-surjective→is-surjective : is-split-surjective f → is-surjective f
is-split-surjective→is-surjective f-split-surj b = do
  f-splitting ← f-split-surj
  pure (f-splitting b)
```

Note that we do not have a converse to this constructively: the statement that
every surjective function between [[sets]] splits is [[equivalent to the axiom of choice|axiom-of-choice]]!


## Split surjective functions and sections

The type of surjective splittings of a function $f : A \to B$ is equivalent
to the type of sections of $f$, i.e. functions $s : B \to A$ with $f \circ s = \id$.

```agda
section≃surjective-splitting
  : (f : A → B)
  → (Σ[ s ∈ (B → A) ] is-right-inverse s f) ≃ surjective-splitting f
```

Somewhat surprisingly, this is an immediate consequence of the fact that
sigma types distribute over pi types!

```agda
section≃surjective-splitting {A = A} {B = B} f =
  (Σ[ s ∈ (B → A) ] ((x : B) → f (s x) ≡ x)) ≃˘⟨ Σ-Π-distrib ⟩
  ((b : B) → Σ[ a ∈ A ] f a ≡ b)             ≃⟨⟩
  surjective-splitting f                     ≃∎
```

This means that a function $f$ is split surjective if and only if there
[[merely]] exists some section of $f$.

```agda
exists-section-iff-split-surjective
  : (f : A → B)
  → (∃[ s ∈ (B → A) ] is-right-inverse s f) ≃ is-split-surjective f
exists-section-iff-split-surjective f =
  ∥-∥-ap (section≃surjective-splitting f)
```

## Closure properties of split surjective functions

Like their non-split counterparts, split surjective functions are closed under composition.

```agda
∘-surjective-splitting
  : surjective-splitting f
  → surjective-splitting g
  → surjective-splitting (f ∘ g)

∘-is-split-surjective
  : is-split-surjective f
  → is-split-surjective g
  → is-split-surjective (f ∘ g)
```

<details>
<summary> The proof is essentially identical to the non-split case.
</summary>
```agda
∘-surjective-splitting {f = f} f-split g-split c =
  let (f*c , p) = f-split c
      (g*f*c , q) = g-split f*c
  in g*f*c , ap f q ∙ p

∘-is-split-surjective fs gs = ⦇ ∘-surjective-splitting fs gs ⦈
```
</details>

Every equivalence can be equipped with a surjective splitting, and
is thus split surjective.

```agda
is-equiv→surjective-splitting
  : is-equiv f
  → surjective-splitting f

is-equiv→is-split-surjective
  : is-equiv f
  → is-split-surjective f
```

This follows immediately from the definition of equivalences: if the
type of fibres is contractible, then we can pluck the element we need
out of the centre of contraction!

```agda
is-equiv→surjective-splitting f-equiv b =
  f-equiv .is-eqv b .centre

is-equiv→is-split-surjective f-equiv =
  pure (is-equiv→surjective-splitting f-equiv)
```

Split surjective functions also satisfy left two-out-of-three.

```agda
surjective-splitting-cancelr
  : surjective-splitting (f ∘ g)
  → surjective-splitting f

is-split-surjective-cancelr
  : is-split-surjective (f ∘ g)
  → is-split-surjective f
```

<details>
<summary>These proofs are also essentially identical to the non-split versions.
</summary>
```agda
surjective-splitting-cancelr {g = g} fg-split c =
  let (fg*c , p) = fg-split c
  in g fg*c , p

is-split-surjective-cancelr fg-split =
  map surjective-splitting-cancelr fg-split
```
</details>

A function is an equivalence if and only if it is a split-surjective
[[embedding]].

```agda
embedding-split-surjective≃is-equiv
  : {f : A → B}
  → (is-embedding f × is-split-surjective f) ≃ is-equiv f
embedding-split-surjective≃is-equiv {f = f} =
  prop-ext!
    (λ (f-emb , f-split-surj) →
      embedding-surjective→is-equiv
        f-emb
        (is-split-surjective→is-surjective f-split-surj))
    (λ f-equiv → is-equiv→is-embedding f-equiv , is-equiv→is-split-surjective f-equiv)
```

# Surjectivity and connectedness

If $f : A \to B$ is a function out of a [[contractible]] type $A$,
then $f$ is surjective if and only if $B$ is a [[pointed connected type]], where
the basepoint of $B$ is given by $f$ applied to the centre of contraction of $A$.

```agda
contr-dom-surjective-iff-connected-cod
  : ∀ {f : A → B}
  → (A-contr : is-contr A)
  → is-surjective f ≃ ((x : B) → ∥ x ≡ f (A-contr .centre) ∥)
```

To see this, note that the fibre of $f$ over $x$ is equivalent
to the type of paths $x = f(a_{\bullet})$, where $a_{\bullet}$ is the centre
of contraction of $A$.

```agda
contr-dom-surjective-iff-connected-cod {A = A} {B = B} {f = f} A-contr =
  Π-cod≃ (λ b → ∥-∥-ap (Σ-contr-eqv A-contr ∙e sym-equiv))
```

This correspondence is not a coincidence: surjective maps fit into
a larger family of maps known as [[connected maps]]. In particular,
a map is surjective exactly when it is (-1)-connected, and this lemma is
a special case of `is-n-connected-point`{.Agda}.
