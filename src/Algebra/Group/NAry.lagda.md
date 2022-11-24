```agda
open import Algebra.Group

open import Cat.Prelude

open import Data.Fin

module Algebra.Group.NAry where
```

# n-Ary Sums

An important property of abelian groups (really, of abelian _monoids_,
but we will only need them for groups) is that their binary operation
extends cleanly to an "n-ary" operation, where the niceness of the
extension is guaranteed by associativity. For a group $G$, we define the
sum of an $n$-ary sequence of $G$'s elements to be the sum "from the
left": add the first element then keep going.

```agda
∑ : ∀ {n} {ℓ} {T : Type ℓ} (G : Group-on T) → (Fin n → T) → T
∑ {n = zero} G x  = Group-on.unit G
∑ {n = suc n} G x = Group-on._⋆_ G (x fzero) (∑ G λ e → x (fsuc e))

∑-path : ∀ {n} {ℓ} {T : Type ℓ} (G : Group-on T) {f g : Fin n → T}
  → (∀ i → f i ≡ g i)
  → ∑ G f ≡ ∑ G g
∑-path G p = ap (∑ G) (funext p)

∑-zero
  : ∀ {n} {ℓ} {T : Type ℓ} (G : Group-on T)
  → ∑ {n} G (λ e → Group-on.unit G) ≡ Group-on.unit G
∑-zero {n = zero} G = refl
∑-zero {n = suc n} G = Group-on.idl G ∙ ∑-zero {n} G
```

<!--
```agda
module _ {ℓ} {T : Type ℓ} (G : Group-on T) (ab : is-abelian-group G) where
  private module G = Group-on G
```
-->

Our assumption that $G$ is abelian comes in when we want to prove that
$(\sum f) + (\sum g) = \sum (f + g)$:

```agda
  ∑-split : ∀ {n} (f : Fin n → T) (g : Fin n → T)
          → ∑ G (λ i → f i G.⋆ g i) ≡ (∑ G f G.⋆ ∑ G g)
  ∑-split {zero} f g = sym G.idl
  ∑-split {suc n} f g =
    (f fzero G.⋆ g fzero) G.⋆ ∑ G (λ i → f (fsuc i) G.⋆ g (fsuc i))             ≡⟨ ap₂ G._⋆_ refl (∑-split (λ e → f (fsuc e)) (λ e → g (fsuc e))) ⟩
    (f fzero G.⋆ g fzero) G.⋆ ∑ G (λ e → f (fsuc e)) G.⋆ ∑ G (λ e → g (fsuc e)) ≡⟨ G.pullr (G.extendl (ab _ _)) ⟩
    f fzero G.⋆ ∑ G (λ e → f (fsuc e)) G.⋆ g fzero G.⋆ ∑ G (λ e → g (fsuc e))   ≡⟨ G.associative ⟩
    (f fzero G.⋆ ∑ G (λ e → f (fsuc e))) G.⋆ g fzero G.⋆ ∑ G (λ e → g (fsuc e)) ∎
```
