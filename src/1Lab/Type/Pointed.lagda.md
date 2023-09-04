<!--
```agda
open import 1Lab.Path
open import 1Lab.Type
```
-->

```agda
module 1Lab.Type.Pointed where
```

## Pointed types {defines="pointed pointed-type pointed-map pointed-homotopy"}

A **pointed type** is a type $A$ equipped with a choice of base point $\point{A}$.

```agda
Type∙ : ∀ ℓ → Type (lsuc ℓ)
Type∙ ℓ = Σ (Type ℓ) (λ A → A)
```

<!--
```agda
private variable
  ℓ ℓ′ : Level
  A B : Type∙ ℓ
```
-->

If we have pointed types $(A, a)$ and $(B, b)$, the most natural notion
of function between them is not simply the type of functions $A \to B$,
but rather those functions $A \to B$ which _preserve the basepoint_,
i.e. the functions $f : A \to B$ equipped with paths $f(a) \equiv b$.

```agda
_→∙_ : Type∙ ℓ → Type∙ ℓ′ → Type _
(A , a) →∙ (B , b) = Σ[ f ∈ (A → B) ] (f a ≡ b)
```

Paths between pointed maps are characterised as **pointed homotopies**:

```agda
funext∙ : {f g : A →∙ B}
        → (h : ∀ x → f .fst x ≡ g .fst x)
        → Square (h (A .snd)) (f .snd) (g .snd) refl
        → f ≡ g
funext∙ h pth i = funext h i , pth i
```
