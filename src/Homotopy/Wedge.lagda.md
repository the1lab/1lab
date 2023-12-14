<!--
```agda
open import 1Lab.Prelude

open import Data.Nat.Properties

open import Homotopy.Connectedness
```
-->

```agda
module Homotopy.Wedge where
```

# Wedge connectivity

The **wedge connectivity** lemma gives a set of sufficient conditions
for constructing a section

$$
e : (x : A)\ (y : B) \to P(x, y)\text{,}
$$

of a type family $P$ over pointed, [[connected]] types $A$ and $B$.
While the actual statement and the proof are highly technical, it
specialises to a fairly straightforward construction: to give a map $e :
A \to B \to C$, it suffices to specify how it varies in each coordinate,
and to show that these descriptions agree on the basepoints.

<!--
```agda
module
  Wedge
    {ℓ ℓ' ℓ''} {A∙@(A , a₀) : Type∙ ℓ} {B∙@(B , b₀) : Type∙ ℓ'} {P : A → B → Type ℓ''}
```
-->

In addition to generalising to dependent functions, the actual statement
of the lemma includes the conditions of [[connectedness]] on the two
argument types, and [[truncation]] on the codomain. If $A$ is
$n$-connected and $B$ is $m$-connected ($n, m \ge 2$), then each
$P(-,-)$ must be $(n+m)$-truncated.

```agda
    (n m : Nat)
    (a-conn : is-n-connected A (2 + n))
    (b-conn : is-n-connected B (2 + m))
    (p-hl : ∀ x y → is-hlevel (P x y) (2 + n + m))
```

Provided that everything fits together, we can actually give the data of
interest: A function $f : (a : A) \to P(a,*)$, a function $g : (b : B)
\to P(*,b)$, and a coherence path $f(*) = g(*)$.

```agda
    (f : ∀ a → P a b₀) (g : ∀ b → P a₀ b) (coh : f a₀ ≡ g b₀)
  where
```

<details>

<summary>As mentioned above, the construction is highly technical. It's
a direct transcription of the proof in [@HoTT, §8.6.2].</summary>

```agda
  private
    Q : A → Type (ℓ' ⊔ ℓ'')
    Q a = Σ ((b : B) → P a b) (λ k → k b₀ ≡ f a)

    rem₂' : (x : A) → is-hlevel (fibre (_∘ (λ _ → b₀)) (λ _ → f x)) (1 + n)
    rem₂' a = relative-n-type-const-plus {A = ⊤} (P a) (λ _ → b₀) (suc m) (suc n)
      (point-is-n-connected b₀ m b-conn)
      (λ b → subst (is-hlevel (P a b)) (sym (ap suc (+-sucr n m))) (p-hl a b))
      (λ _ → f a)

    opaque
      worker : Σ ((b : A) → Q b) (λ h → Path (⊤ → Q a₀) (λ _ → h a₀) (λ _ → g , sym coh))
      worker = connected-elimination-principle (suc n) Q hl (g , sym coh) a-conn where
        hl : (x : A) → is-hlevel (Q x) (suc n)
        hl x = retract→is-hlevel (suc n)
          (λ (p , q) → p , happly q tt)
          (λ (p , q) → p , funext λ _ → q)
          (λ _ → refl) (rem₂' x)
```

</details>

If everything fits together, then we end up with the following data, in
addition to the section $e$: A proof $\beta_1 : e(a,*) = f(a)$; a proof that
$\beta_2 : e(*,b) = g(b)$; and a proof that, at $e(*,*)$, these differ
by the specified coherence $f(*) = g(*)$.

```agda
  opaque
    elim : ∀ x y → P x y
    elim x y = worker .fst x .fst y

    β₁ : ∀ a → elim a b₀ ≡ f a
    β₁ a = worker .fst a .snd

    β₂ : ∀ b → elim a₀ b ≡ g b
    β₂ b = ap fst (worker .snd $ₚ tt) $ₚ b

    β-path : β₂ b₀ ∙ sym coh ≡ β₁ a₀
    β-path = square→commutes (ap snd (worker .snd $ₚ tt)) ∙ ∙-idr _
```
