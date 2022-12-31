```agda
open import Cat.Prelude

open import Order.Instances.Pointwise
open import Order.Instances.Lower
open import Order.Diagram.Glb
open import Order.Diagram.Lub
open import Order.Base

import Order.Reasoning as Poset

module Order.Instances.Lower.Cocompletion where
```

# Lower sets as cocompletions

In this module we prove the universal property of $DA$, the [poset] of
[lower sets] of a poset $A$: $DA$ is the free cocomplete poset on $A$,
meaning that every map $A \to B$ into a cocomplete poset $B$ admits a
unique **cocontinuous extension** $\widehate{f} : DA \to B$.

[poset]: Order.Base.html
[lower sets]: Order.Instances.Lower.html

As an intermediate step, we establish the posetal analogue of the
[coyoneda lemma], saying that every lower set $L$ is the join of all
$\darr a$ for $a : A, a \in L$.

[coyoneda lemma]: Cat.Functor.Hom.html#the-coyoneda-lemma

```agda
module ↓Coyoneda {o ℓ} (P : Poset o ℓ) (Ls : Lower-set P) where
  private
    module P  = Poset P
    module P↓ = Poset (Lower-sets P)

  shape : Type o
  shape = Σ ⌞ P ⌟ λ i → i ∈ Ls .fst

  diagram : shape → Lower-set P
  diagram (i , i∈P) = ↓ P i
```

This result is _much_ easier to establish in the posetal case than it is
in the case of proper categories, so we do not comment on the
construction too much. The curious reader is invited to load this file
in Agda and play with it themselves!

```agda
  lower-set-is-lub : is-lub (Lower-sets P) diagram Ls
  lower-set-is-lub .is-lub.fam≤lub (j , j∈Ls) =
    (λ i □i≤j → Ls .snd _ _ (out! □i≤j) j∈Ls) , tt
  lower-set-is-lub .is-lub.least ub′ fam≤ub′ =
    (λ i i∈Ls → fam≤ub′ (i , i∈Ls) .fst i (inc P.≤-refl)) , tt
```

A quick note on notation: The result saying that $L$ is the lub of the
down-sets of its elements is called `lower-set-∫`{.Agda}. The integral symbol is
because (in the categorical case) we can think of the coyoneda lemma as
saying that presheaves are computed as certain [coends].

[coends]: Cat.Diagram.Coend.html

```agda
  lower-set-∫ : Ls ≡ Lower-sets-cocomplete P diagram .fst
  lower-set-∫ = ap fst $ lub-unique (Lower-sets P)
    (Ls , lower-set-is-lub)
    (Lower-sets-cocomplete P diagram)
```

<!--
```agda
module
  _ {o ℓ ℓ′} (A : Poset o ℓ) (B : Poset o ℓ′)
    (B-cocomplete
      : ∀ {I : Type o} (F : I → ⌞ B ⌟) → Σ _ (is-lub B F))
    (f : ⌞ Monotone A B ⌟)
  where
  private
    module A  = Poset A
    module DA = Poset (Lower-sets A)
    module B  = Poset B
```
-->

The cocontinuous extension sends a lower set $S : DA$ to the join (in
$B$) of $\{ f i | i \in S \}$, which is expressed familially as the
composition

$$
(\sum_{i : A} i \in S) \xto{\pi_1} A \to B\text{.}
$$

It is readily computed that this procedure results in a monotone map.

```agda
  Lan↓₀ : Lower-set A → ⌞ B ⌟
  Lan↓₀ (S , is-lower) = B-cocomplete {I = Σ ⌞ A ⌟ λ i → i ∈ S} (λ i → f .fst (i .fst)) .fst

  Lan↓₁ : ∀ x y → x DA.≤ y → Lan↓₀ x B.≤ Lan↓₀ y
  Lan↓₁ (S , s-lower) (T , t-lower) (S⊆T , _) = B-cocomplete _ .snd .is-lub.least _ λ {
    (i , i∈S) → B-cocomplete _ .snd .is-lub.fam≤lub (i , S⊆T i i∈S) }
```

A further short computation reveals that the least upper bound of all
elements under $x$ is $x$. Put like that, it seems trivial, but it says
that our cocontinuous extension commutes with the "unit map" $A \to DA$.

```agda
  Lan↓-commutes : ∀ x → Lan↓₀ (↓ A x) ≡ f .fst x
  Lan↓-commutes x = B.≤-antisym
    (B-cocomplete _ .snd .is-lub.least _ λ { (i , □i≤x) → f .snd i x (out! □i≤x) })
    (B-cocomplete _ .snd .is-lub.fam≤lub (x , inc A.≤-refl))
```

A short argument whose essence is the commutativity of joins with joins
establishes that the cocontinuous extension does live up to its name:

```agda
  Lan↓-cocontinuous
    : ∀ {I : Type o} (F : I → Lower-set A)
    → Lan↓₀ (Lower-sets-cocomplete A F .fst) ≡ B-cocomplete (λ i → Lan↓₀ (F i)) .fst
  Lan↓-cocontinuous F = B.≤-antisym
    (B-cocomplete _ .snd .is-lub.least _ λ { (i , i∈⋃F) → □-rec! (λ { (j , i∈Fj) →
      B.≤-trans (B-cocomplete _ .snd .is-lub.fam≤lub (i , i∈Fj))
                (B-cocomplete _ .snd .is-lub.fam≤lub j) })
      i∈⋃F })
    (B-cocomplete _ .snd .is-lub.least _ λ i → B-cocomplete _ .snd .is-lub.least _ λ { (j , j∈Fi) →
      B-cocomplete _ .snd .is-lub.fam≤lub (j , inc (i , j∈Fi)) })
```

And the coyoneda lemma comes in to show that the cocontinuous extension
is unique, for if $f' : DA \to B$ is any other cocontinuous map sending
$\darr a$ to $f(a)$, then expressing a lower set $L$ as

$$
\bigcup \{ \darr i | i \in L \}
$$

reveals that $f'$ must agree with $\widehat{f}$.

```agda
  Lan↓-unique
    : (f~ : ⌞ Monotone (Lower-sets A) B ⌟)
    → ( ∀ {I : Type o} (F : I → Lower-set A)
      → f~ .fst (Lower-sets-cocomplete A F .fst) ≡ B-cocomplete (λ i → f~ .fst (F i)) .fst )
    → (∀ x → f~ .fst (↓ A x) ≡ f .fst x)
    → f~ ≡ (Lan↓₀ , Lan↓₁)
  Lan↓-unique (f~ , f~-mon) f~-cocont f~-comm = Σ-prop-path! $ funext λ i →
    f~ i                                                         ≡⟨ ap f~ (↓Coyoneda.lower-set-∫ A i) ⟩
    f~ (Lower-sets-cocomplete A (↓Coyoneda.diagram A i) .fst)    ≡⟨ f~-cocont (↓Coyoneda.diagram A i) ⟩
    B-cocomplete (λ j → f~ (↓Coyoneda.diagram A i j)) .fst       ≡⟨ ap (λ e → B-cocomplete e .fst) (funext λ j → f~-comm (j .fst) ∙ sym (Lan↓-commutes (j .fst))) ⟩
    B-cocomplete (λ j → Lan↓₀ (↓ A (j .fst))) .fst               ≡˘⟨ Lan↓-cocontinuous (↓Coyoneda.diagram A i) ⟩
    Lan↓₀ (Lower-sets-cocomplete A (↓Coyoneda.diagram A i) .fst) ≡˘⟨ ap Lan↓₀ (↓Coyoneda.lower-set-∫ A i) ⟩
    Lan↓₀ i                                                      ∎
```
