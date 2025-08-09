<!--
```agda
open import 1Lab.Prelude

open import Data.Set.Coequaliser
```
-->

```agda
module Data.Set.Coequaliser.Split where
```

# Split quotients {defines="split-quotient"}

Recall that a [[quotient]] of a set $A$ by an equivalence relation $x
\sim y$ allows us to "replace" the identity type of $A$ by the relation
$R$, by means of a [[surjection]] $[-] : A \epi A/{\sim}$ having $[x] =
[y]$ equivalent to $x \sim y$. However, depending on the specifics of
$R$, we may not need to actually take a quotient after all! It may be
the case that $A/{\sim}$ is equivalent to a particular *subset* of $A$.
When this is the case, we say that the quotient is **split**. This
module outlines sufficient conditions for a quotient to split, by
appealing to our intuition about *normal forms*.

<!--
```agda
private variable
  ℓ ℓ' : Level
  A : Type ℓ
```
-->

```agda
record is-split-congruence (R : Congruence A ℓ') : Type (level-of A ⊔ ℓ') where
  open Congruence R

  field
    has-is-set : is-set A
```

A normalisation function $n : A \to A$, for an equivalence relation $x
\sim y$, is one that is the identity "up to $\sim$", i.e., we have $x
\sim n(x)$, and which respects the relation, in that, if we have $x \sim
y$, then $n(x) = n(y)$.

```agda
    normalise : A → A

    represents : ∀ x → x ∼ normalise x
    respects   : ∀ x y → x ∼ y → normalise x ≡ normalise y
```

<!--
```agda
  private instance
    hl-a : ∀ {n} → H-Level A (2 + n)
    hl-a = basic-instance 2 has-is-set
```
-->

It turns out that this is just enough to ask for a splitting of the
quotient map $[-]$: We can define a function sending each $x : A/{\sim}$
to a fibre of the quotient map over it, by induction. At the points of
$A$, we take the fibre over $[x]$ to be $n(x)$, and we have $[n(x)] =
[x]$ by the first assumption. By the second assumption, this procedure
respects the quotient.

```agda
  splitting : (x : Congruence.quotient R) → fibre inc x
  splitting (inc x) = record { fst = normalise x ; snd = quot (symᶜ (represents x)) }
  splitting (glue (x , y , r) i) = record
    { fst = respects x y r i
    ; snd = is-prop→pathp (λ i → Coeq.squash (inc (respects x y r i)) (quot r i))
      (quot (symᶜ (represents x))) (quot (symᶜ (represents y))) i
    }
  splitting (squash x y p q i j) = is-set→squarep
    (λ i j → hlevel {T = fibre inc (squash x y p q i j)} 2)
    (λ i → splitting x) (λ i → splitting (p i)) (λ i → splitting (q i)) (λ i → splitting y) i j
```

<!--
```agda
  choose : Congruence.quotient R → A
  choose x = splitting x .fst
```
-->

Two other consequences of these assumptions are that the normalisation
function is literally idempotent, and that it additionally *reflects*
the quotient relation, in that $x \sim y$ is *equivalent to* $n(x) =
n(y)$.

```agda
  normalises : ∀ x → normalise (normalise x) ≡ normalise x
  normalises x = respects (normalise x) x (symᶜ (represents x))

  reflects : ∀ x y → normalise x ≡ normalise y → x ∼ y
  reflects x y p = represents x ∙ᶜ reflᶜ' p ∙ᶜ symᶜ (represents y)
```

Finally, we show that any splitting of the quotient map generates a
normalisation procedure in the above sense: if we have a map $c : A/{\sim}
\to A$, we define the normalisation procedure to be $n(x) = c[x]$.

```agda
split-surjection→is-split-congruence
  : ⦃ _ : H-Level A 2 ⦄ (R : Congruence A ℓ)
  → surjective-splitting {B = Congruence.quotient R} inc
  → is-split-congruence R
split-surjection→is-split-congruence R split = record
  { has-is-set = hlevel 2
  ; normalise  = λ x → split (inc x) .fst
  ; represents = λ x → effective (sym (split (inc x) .snd))
  ; respects   = λ x y p → ap (fst ∘ split) (quot p)
  } where open Congruence R
```
