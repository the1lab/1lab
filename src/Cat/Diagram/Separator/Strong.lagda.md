---
description: |
  Strong separators.
---
<!--
```agda
open import Cat.Diagram.Coequaliser.RegularEpi
open import Cat.Diagram.Coproduct.Copower
open import Cat.Diagram.Coproduct.Indexed
open import Cat.Diagram.Limit.Finite
open import Cat.Functor.Conservative
open import Cat.Instances.Sets
open import Cat.Functor.Joint
open import Cat.Functor.Hom
open import Cat.Prelude

import Cat.Morphism.Strong.Epi
import Cat.Diagram.Separator
import Cat.Reasoning
```
-->
```agda
module Cat.Diagram.Separator.Strong
  {o ℓ}
  (C : Precategory o ℓ)
  (coprods : (I : Set ℓ) → has-coproducts-indexed-by C ∣ I ∣)
  where
```

<!--
```agda
open Cat.Morphism.Strong.Epi C
open Cat.Diagram.Separator C
open Cat.Reasoning C
open Copowers coprods

private variable
  s : Ob
```
-->

# Strong separators

Recall that a [[separating object]] $S$ lets us determine equality of
morphisms solely by examining $S$-generalized objects. This leads to
a natural question: what other properties of morphisms can we compute
like this? In our case: can we determine if a map $f : \cC(X,Y)$ is
[[invertible]] by restricting to generalized objects? Generally speaking,
the answer is no, but it is possible if we strengthen our notion of
separating object.

:::{.definition #strong-separator}
Let $\cC$ be a category with [[set-indexed coproducts|indexed-coproduct]].
An object $S$ is a **strong separator** if the canonical map $\coprod_{\cC(S,X)} S \to X$
is a [[strong epi]].
:::

```agda
is-strong-separator : Ob → Type (o ⊔ ℓ)
is-strong-separator s = ∀ {x} → is-strong-epi (⊗!.match (Hom s x) s λ e → e)
```

We can also weaken this definition to a family of objects.

:::{.definition #strong-separating-family}
A family of objects $S_i$ is a **strong separating family** if the
canonical map $\coprod_{\Sigma(i : I), \cC(S_i, X)} S_i \to X$
is a [[strong epi]].
:::

```agda
is-strong-separating-family
  : ∀ (Idx : Set ℓ)
  → (sᵢ : ∣ Idx ∣ → Ob)
  → Type (o ⊔ ℓ)
is-strong-separating-family Idx sᵢ =
  ∀ {x} → is-strong-epi (∐!.match (Σ[ i ∈ ∣ Idx ∣ ] (Hom (sᵢ i) x)) (sᵢ ⊙ fst) snd)
```

Strong separators are [[separators]]. This follows from the fact
that an object $S$ is a separator if and only if the canonical map
$\coprod_{\cC(S,X)} S \to X$ is an epi.

```agda
strong-separator→separator
  : is-strong-separator s
  → is-separator s
strong-separator→separator strong =
  epi→separator coprods (strong .fst)
```

A similar line of reasoning shows that strong separating families are
separating families.

```agda
strong-separating-family→separating-family
  : ∀ (Idx : Set ℓ) (sᵢ : ∣ Idx ∣ → Ob)
  → is-strong-separating-family Idx sᵢ
  → is-separating-family sᵢ
strong-separating-family→separating-family Idx sᵢ strong =
  epi→separating-family coprods Idx sᵢ (strong .fst)
```

# Extremal separators

For reasons that we will see shortly, it is useful to weaken the notion
of strong separators to [[extremal epimorphisms]].

:::{.definition #extremal-separator}
Let $\cC$ be a category with [[set-indexed coproducts|indexed-coproduct]].
An object $S$ is a **strong separator** if the canonical map $\coprod_{\cC(S,X)} S \to X$
is an [[extremal epi]].
:::

```agda
is-extremal-separator : Ob → Type (o ⊔ ℓ)
is-extremal-separator s = ∀ {x} → is-extremal-epi (⊗!.match (Hom s x) s λ e → e)
```

:::{.definition #extremal-separating-family}
A family of objects $S_i$ is a **extremal separating family** if the
canonical map $\coprod_{\Sigma(i : I), \cC(S_i, X)} S_i \to X$
is a [[strong epi]].
:::

```agda
is-extremal-separating-family
  : ∀ (Idx : Set ℓ)
  → (sᵢ : ∣ Idx ∣ → Ob)
  → Type (o ⊔ ℓ)
is-extremal-separating-family Idx sᵢ =
  ∀ {x} → is-extremal-epi (∐!.match (Σ[ i ∈ ∣ Idx ∣ ] (Hom (sᵢ i) x)) (sᵢ ⊙ fst) snd)
```

Via a general result involving strong and extremal epis, strong separators
are extremal.

```agda
strong-separator→extremal-separator
  : is-strong-separator s
  → is-extremal-separator s
strong-separator→extremal-separator strong =
  is-strong-epi→is-extremal-epi strong

strong-separating-family→extremal-separating-family
  : ∀ (Idx : Set ℓ)
  → (sᵢ : ∣ Idx ∣ → Ob)
  → is-strong-separating-family Idx sᵢ
  → is-extremal-separating-family Idx sᵢ
strong-separating-family→extremal-separating-family Idx sᵢ strong =
  is-strong-epi→is-extremal-epi strong
```

Moreover, if $\cC$ has all [[finite limits]], then extremal separators
are strong.

```agda
lex+extremal-separator→strong-separator
  : Finitely-complete C
  → is-extremal-separator s
  → is-strong-separator s
lex+extremal-separator→strong-separator lex extremal =
  is-extremal-epi→is-strong-epi lex extremal

lex+extremal-separating-family→strong-separating-family
  : ∀ (Idx : Set ℓ)
  → (sᵢ : ∣ Idx ∣ → Ob)
  → Finitely-complete C
  → is-extremal-separating-family Idx sᵢ
  → is-strong-separating-family Idx sᵢ
lex+extremal-separating-family→strong-separating-family Idx sᵢ lex extremal =
  is-extremal-epi→is-strong-epi lex extremal
```

## Functorial definitions

We shall now prove our claim that a strong separator $S$ allows us to
distinguish invertible morphisms purely by checking invertibility at
$S$-generalized elements. More precisely, if $S$ is a strong separator,
then $\cC(S,-)$ is [[conservative]].

```agda
strong-separator→conservative
  : ∀ {s}
  → is-strong-separator s
  → is-conservative (Hom-from C s)
```

Suppose that $f : \cC(X,Y)$ is a morphism such that $f \circ e$ is invertible
for every $e : \cC(S,X)$. We shall show that $f$ itself is invertible
by showing that it is both a strong epi and a monomorphism.

```agda
strong-separator→conservative {s = s} strong {A = a} {B = b} {f = f} f∘-inv =
  strong-epi+mono→invertible
    f-strong-epi
    f-mono
  where
    module f∘- = Equiv (f ∘_ , is-invertible→is-equiv f∘-inv)
```

Showing that $f$ is monic is pretty straightforward. Suppose that
we have $u, v : \cC(X, A)$ such that $f \circ u = f \circ v$.
Because $S$ is a separator, we can show that $u = v$ by showing
that $u \circ e = v \circ e$ for some $S$-generalized element $e$.
Moreover, postcomposition with $f$ is injective on morphisms with domain
$S$ so it suffices to prove that $f \circ u \circ e = f \circ v \circ e$;
this follows directly from our hypothesis.

```agda
    f-mono : is-monic f
    f-mono u v p =
      strong-separator→separator strong λ e →
      f∘-.injective (extendl p)
```

Proving that $f$ is a strong epi is a bit more work. First, note that
we can construct a map $f^* : \coprod_{\cC(S,B)} \to A$ by applying
the inverse of $f \circ - : \cC(S,A) \to \cC(S,B)$; moreover, this
map factorizes the canonical map $\coprod_{\cC(S,B)} S \to B$.

```agda
    f* : Hom ((Hom s b) ⊗! s) a
    f* = ⊗!.match (Hom s b) s λ e → f∘-.from e

    f*-factors : f ∘ f* ≡ ⊗!.match (Hom s b) s (λ e → e)
    f*-factors = ⊗!.unique _ _ _ λ e →
      (f ∘ f*) ∘ ⊗!.ι (Hom s b) s e ≡⟨ pullr (⊗!.commute (Hom s b) s) ⟩
      f ∘ f∘-.from e                ≡⟨ f∘-.ε e ⟩
      e                             ∎
```

By definition, the canonical map $\coprod_{\cC(S,B)} S \to B$ is a strong
epi. Moreover, if a composite $f \circ g$ is a strong epi, then $f$
is a strong epi. If we apply this observation to our factorization, we
immediately see that $f$ is a strong epi.

```agda
    f-strong-epi : is-strong-epi f
    f-strong-epi =
      strong-epi-cancelr f f* $
      subst is-strong-epi (sym f*-factors) strong
```

Conversely, if $\cC(S,-)$ is conservative, then $S$ is an extremal
separator. The proof here is some basic data manipulation, so we
do not dwell on it too deeply.

```agda
conservative→extremal-separator
  : ∀ {s}
  → is-conservative (Hom-from C s)
  → is-extremal-separator s
conservative→extremal-separator f∘-conservative m f p =
  f∘-conservative $
  is-equiv→is-invertible $
  is-iso→is-equiv $ iso
    (λ e → f ∘ ⊗!.ι _ _ e)
    (λ f* → pulll (sym p) ∙ ⊗!.commute _ _)
    (λ e → m .monic _ _ (pulll (sym p) ∙ ⊗!.commute _ _))
```

In particular, if $\cC$ is finitely complete, then conservativity
of $\cC(S,-)$ implies that $S$ is a strong separator.

```agda
lex+conservative→strong-separator
  : ∀ {s}
  → Finitely-complete C
  → is-conservative (Hom-from C s)
  → is-strong-separator s
lex+conservative→strong-separator lex f∘-conservative =
  is-extremal-epi→is-strong-epi lex $
  conservative→extremal-separator f∘-conservative
```

We can generalize these results to separating families by considering
[[jointly conservative functors]].

```agda
strong-separating-family→jointly-conservative
  : ∀ (Idx : Set ℓ) (sᵢ : ∣ Idx ∣ → Ob)
  → is-strong-separating-family Idx sᵢ
  → is-jointly-conservative (λ i → Hom-from C (sᵢ i))

jointly-conservative→extremal-separating-family
  : ∀ (Idx : Set ℓ) (sᵢ : ∣ Idx ∣ → Ob)
  → Finitely-complete C
  → is-jointly-conservative (λ i → Hom-from C (sᵢ i))
  → is-extremal-separating-family Idx sᵢ

lex+jointly-conservative→strong-separating-family
  : ∀ (Idx : Set ℓ) (sᵢ : ∣ Idx ∣ → Ob)
  → Finitely-complete C
  → is-jointly-conservative (λ i → Hom-from C (sᵢ i))
  → is-strong-separating-family Idx sᵢ
```

<details>
<summary>The proofs are identical to their non-familial counterparts,
so we omit the details.
</summary>
```agda
strong-separating-family→jointly-conservative Idx sᵢ strong {x = a} {y = b} {f = f} f∘ᵢ-inv =
  strong-epi+mono→invertible
    f-strong-epi
    f-mono
  where
    module f∘- {i : ∣ Idx ∣} = Equiv (_ , is-invertible→is-equiv (f∘ᵢ-inv i))

    f-mono : is-monic f
    f-mono u v p =
      strong-separating-family→separating-family Idx sᵢ strong λ eᵢ →
      f∘-.injective (extendl p)

    f* : Hom (∐! (Σ[ i ∈ ∣ Idx ∣ ] (Hom (sᵢ i) b)) (sᵢ ⊙ fst)) a
    f* = ∐!.match _ _ (f∘-.from ⊙ snd)

    f*-factors : f ∘ f* ≡ ∐!.match (Σ[ i ∈ ∣ Idx ∣ ] (Hom (sᵢ i) b)) (sᵢ ⊙ fst) snd
    f*-factors =
      ∐!.unique _ _ _ λ (i , eᵢ) →
      (f ∘ f*) ∘ ∐!.ι _ _ (i , eᵢ) ≡⟨ pullr (∐!.commute _ _) ⟩
      f ∘ f∘-.from eᵢ              ≡⟨ f∘-.ε eᵢ ⟩
      eᵢ                           ∎

    f-strong-epi : is-strong-epi f
    f-strong-epi =
      strong-epi-cancelr f f* $
      subst is-strong-epi (sym f*-factors) strong

jointly-conservative→extremal-separating-family Idx sᵢ lex f∘-conservative m f p =
  f∘-conservative $ λ i →
  is-equiv→is-invertible $
  is-iso→is-equiv $ iso
    (λ eᵢ → f ∘ ∐!.ι _ _ (i , eᵢ))
    (λ f* → pulll (sym p) ∙ ∐!.commute _ _)
    (λ eᵢ → m .monic _ _ (pulll (sym p) ∙ ∐!.commute _ _))

lex+jointly-conservative→strong-separating-family Idx sᵢ lex f∘-conservative =
  is-extremal-epi→is-strong-epi lex $
  jointly-conservative→extremal-separating-family Idx sᵢ lex f∘-conservative
```
</details>
