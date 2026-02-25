<!--
```agda
open import 1Lab.Function.Surjection
open import 1Lab.Function.Embedding
open import 1Lab.Equiv.Fibrewise using (_≃[_]_)
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type
```
-->

```agda
module 1Lab.Function.Fibrewise where
```

# Function over {defines="function-over"}

In the same way that an [[equivalence over]] generalises a [[fibrewise
equivalence]], we can generalise a [[fibrewise map]] to type families
with different base types.

Let $A$ and $B$ be types, $a : A \vdash P(a)$ and $b : B \vdash Q(b)$ be
type families, and $f : A \to B$ be a function. A **function over** $f$
consists of a function $f'_{a, b, p} : P(a) \to P(b)$ for every pair of
points $a : A, b : B$ with a path $p : f(a) =_B b$.

<!--
```agda
private variable
  ℓ ℓ' : Level
  A B : Type ℓ
  P Q : A → Type ℓ
```
-->

```agda
_-[_]→_
  : ∀ (P : A → Type ℓ) (f : A → B) (Q : B → Type ℓ') → Type _
_-[_]→_ {A = A} {B = B} P f Q = ∀ (a : A) (b : B) → f a ≡ b → (P a → Q b)
```

<!--
```agda
module _ {P : A → Type ℓ}  {Q : B → Type ℓ'} where
  private variable f : A → B
```
-->

A function over $f$ induces a function between total spaces

```agda
  over→total : P -[ f ]→ Q → Σ A P → Σ B Q
  over→total {f = f} f' (a , a') = (f a) , f' a (f a) refl a'
```

Here, conceptual meaning of `P -[ f ]→ Q`{.Agda ident="_-[_]→_"} is made
more clear by the commutativity of the diagram

~~~{.quiver .attach-around}
\begin{tikzcd}
	{\sum_{a:A}P(a)} && {\sum_{b:B}Q(b)} \\
	\\
	A && B
	\arrow["{\sum f'}", from=1-1, to=1-3]
	\arrow["{\text{fst}}"', two heads, from=1-1, to=3-1]
	\arrow["{\text{fst}}", two heads, from=1-3, to=3-3]
	\arrow["f"', from=3-1, to=3-3]
\end{tikzcd}
~~~

where $\sum f'$ denotes `over→total f'`{.Agda ident="over→total"}.

<!--
```agda
  module _ {f' : P -[ f ]→ Q} where
```
-->

```agda
    _ : f ∘ fst ≡ fst ∘ over→total f'
    _ = refl
```

In the simplest cases we can construct a map over using the following
helper function:

```agda
  over-left→over : (∀ (a : A) → P a → Q (f a)) → P -[ f ]→ Q
  over-left→over f' a b p a' = subst  Q  p (f' a a')
```

## Properties

We can generalise the properties of being [[injective]], [[surjective]], 
or an [equivalence] to functions over:

[equivalence]: 1Lab.Equiv.html

```agda
  injective[] : P -[ f ]→ Q → Type _
  injective[] f' = ∀ a b p → injective (f' a b p)

  is-surjective[] : P -[ f ]→ Q → Type _
  is-surjective[] f' = ∀ a b p → is-surjective (f' a b p)

  is-equiv[] : P -[ f ]→ Q → Type _
  is-equiv[] f' = ∀ a b p → is-equiv (f' a b p)
```

When we are dealing with a map over an equivalence, having the property
 `is-equiv[]`{.Agda} amounts to being an [[equivalence over]]:

```agda
  module _ {e : A ≃ B} where
    private module e = Equiv e
    private map-over+equiv = Σ (P -[ e.to ]→ Q) λ e' → is-equiv[] e'

    map-over→equiv-over : map-over+equiv → P ≃[ e ] Q
    map-over→equiv-over (e' , e'-eqv) a b p = e' a b p , e'-eqv a b p

    equiv-over→map-over : P ≃[ e ] Q → map-over+equiv
    equiv-over→map-over e' = (λ a b p → e' a b p .fst) , λ a b p → e' a b p .snd

    map-over≃equiv=over : map-over+equiv ≃ (P ≃[ e ] Q)
    map-over≃equiv=over = Iso→Equiv
      (map-over→equiv-over , iso equiv-over→map-over (λ _ → refl) λ _ → refl)

    module map-over≃equiv=over = Equiv map-over≃equiv=over
```
