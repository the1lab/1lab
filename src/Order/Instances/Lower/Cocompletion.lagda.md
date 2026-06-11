<!--
```agda
open import Cat.Prelude

open import Order.Diagram.Lub.Reasoning
open import Order.Instances.Pointwise
open import Order.Instances.Lower
open import Order.Diagram.Glb
open import Order.Diagram.Lub
open import Order.Base

import Order.Reasoning
```
-->

```agda
module Order.Instances.Lower.Cocompletion where
```

# Lower sets as cocompletions

In this module we prove the universal property of $DA$, the [[poset]] of
[lower sets] of a poset $A$: $DA$ is the free cocomplete poset on $A$,
meaning that every map $A \to B$ into a cocomplete poset $B$ admits a
unique **cocontinuous extension** $\widehat{f} : DA \to B$.

[poset]: Order.Base.html
[lower sets]: Order.Instances.Lower.html

As an intermediate step, we establish the posetal analogue of the
[coyoneda lemma], saying that every lower set $L$ is the join of all
$\darr a$ for $a : A, a \in L$.

[coyoneda lemma]: Cat.Functor.Hom.Coyoneda.html

```agda
module ↓Coyoneda {o ℓ} (P : Poset o ℓ) (Ls : Lower-set P) where
  private
    module P  = Order.Reasoning P
    module P↓ = Order.Reasoning (Lower-sets P)

  diagram : ∫ₚ Ls → Lower-set P
  diagram (i , i∈P) = ↓ P i
```

This result is _much_ easier to establish in the posetal case than it is
in the case of proper categories, so we do not comment on the
construction too much. The curious reader is invited to load this file
in Mikan and play with it themselves!

```agda
  lower-set-is-lub : is-lub (Lower-sets P) diagram Ls
  lower-set-is-lub .is-lub.fam≤lub (j , j∈Ls) i □i≤j =
    Ls .pres-≤ (□-out! □i≤j) j∈Ls
  lower-set-is-lub .is-lub.least ub' fam≤ub' i i∈Ls =
    fam≤ub' (i , i∈Ls) i (inc (P.≤-refl))
```

A quick note on notation: The result saying that $L$ is the lub of the
down-sets of its elements is called `lower-set-∫`{.Agda}. The integral symbol is
because (in the categorical case) we can think of the coyoneda lemma as
saying that presheaves are computed as certain [coends].

[coends]: Cat.Diagram.Coend.html

```agda
  lower-set-∫ : Ls ≡ Lub.lub (Lower-sets-cocomplete P diagram)
  lower-set-∫ = lub-unique (lower-set-is-lub)
    (Lub.has-lub $ Lower-sets-cocomplete P diagram)
```

<!--
```agda
module
  _ {o ℓ ℓ'} {A : Poset o ℓ} {B : Poset o ℓ'}
    {⋃ : {I : Type o} (F : I → ⌞ B ⌟) → ⌞ B ⌟}
    (⋃-lubs : ∀ {I : Type o} (F : I → ⌞ B ⌟) → is-lub B F (⋃ F))
    (f : Monotone A B)
  where
  private
    module A  = Poset A
    module DA = Poset (Lower-sets A)
    module B  = Poset B
    module B-cocomplete = Lubs B ⋃-lubs
```
-->

The cocontinuous extension sends a lower set $S : DA$ to the join (in
$B$) of $\{ f i | i \in S \}$, which is expressed familially as the
composition

$$
(\sum_{i : A} i \in S) \xto{\pi_1} A \to B
$$.

It is readily computed that this procedure results in a monotone map.

```agda
  Lan↓ : Monotone (Lower-sets A) B
  Lan↓ .hom S = ⋃ {I = Σ[ i ∈ A ] (i ∈ S)} (λ i → f · i .fst)
  Lan↓ .pres-≤ {S} {T} S⊆T = B-cocomplete.⋃-universal _ λ where
    (i , i∈S) → B-cocomplete.⋃-inj (i , S⊆T i i∈S)
```

A further short computation reveals that the least upper bound of all
elements under $x$ is $x$. Put like that, it seems trivial, but it says
that our cocontinuous extension commutes with the "unit map" $A \to DA$.

```agda
  Lan↓-commutes : ∀ x → Lan↓ · ↓ A x ≡ f · x
  Lan↓-commutes x = B.≤-antisym
    (B-cocomplete.⋃-universal _ (λ { (i , □i≤x) → f .pres-≤ (□-out! □i≤x) }))
    (B-cocomplete.⋃-inj (x , inc A.≤-refl))
```

A short argument whose essence is the commutativity of joins with joins
establishes that the cocontinuous extension does live up to its name:

```agda
  Lan↓-cocontinuous
    : ∀ {I : Type o} (F : I → Lower-set A)
    → Lan↓ · Lub.lub (Lower-sets-cocomplete A F) ≡ ⋃ (λ i → Lan↓ · F i)
  Lan↓-cocontinuous F = B.≤-antisym
    (B-cocomplete.⋃-universal _ (elim! λ x i fi≤x →
      B.≤-trans (B-cocomplete.⋃-inj (x , fi≤x)) (B-cocomplete.⋃-inj i)))
    (B-cocomplete.⋃-universal _ λ i →
     B-cocomplete.⋃-universal _ λ where
       (j , j∈Fi) → B-cocomplete.⋃-inj (j , inc (i , j∈Fi)))
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
      → f~ · Lub.lub (Lower-sets-cocomplete A F) ≡ ⋃ (λ i → f~ · (F i)) )
    → (∀ x → f~ · ↓ A x ≡ f · x)
    → f~ ≡ Lan↓
  Lan↓-unique f~ f~-cocont f~-comm = ext λ i →
    f~ · i                                                           ≡⟨ ap· f~ (↓Coyoneda.lower-set-∫ A i) ⟩
    f~ · Lub.lub (Lower-sets-cocomplete A (↓Coyoneda.diagram A i))   ≡⟨ f~-cocont (↓Coyoneda.diagram A i) ⟩
    ⋃ (λ j → f~ · (↓Coyoneda.diagram A i j))                         ≡⟨ ap ⋃ (funext λ j → f~-comm (j .fst) ∙ sym (Lan↓-commutes (j .fst))) ⟩
    ⋃ (λ j → Lan↓ · (↓ A (j .fst)))                                  ≡˘⟨ Lan↓-cocontinuous (↓Coyoneda.diagram A i) ⟩
    Lan↓ · Lub.lub (Lower-sets-cocomplete A (↓Coyoneda.diagram A i)) ≡˘⟨ ap· Lan↓ (↓Coyoneda.lower-set-∫ A i) ⟩
    Lan↓ · i                                                         ∎
```
