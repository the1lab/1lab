```agda
open import 1Lab.Prelude

open import Data.Int

module Data.Int.Universal where
```

# Universal property of the integers

We define and prove a type-theoretic universal property of the integers,
which characterises them as the initial pointed set equipped with an
auto-equivalence, in much the same way that the natural numbers are
characterised as being the initial pointed type equipped with an
endomorphism.

```agda
record Integers (ℤ : Type) : Typeω where
  no-eta-equality
  field
    ℤ-is-set : is-set ℤ
    point  : ℤ
    rotate : ℤ ≃ ℤ
```

We start by giving $\bb{Z}$ a _mapping-out_ property: If $X$ is any
other type with $p : X$ and $e : X \simeq X$, then there is a map
$\bb{Z} \to X$ which sends our point (which may as well be called
_zero_) to $p$, and commutes with our equivalence. Note that commuting
with the equivalence implies commuting with its inverse, too.

```agda
    map-out       : ∀ {ℓ} {X : Type ℓ} → X → X ≃ X → ℤ → X
    map-out-point : ∀ {ℓ} {X : Type ℓ} (p : X) (r : X ≃ X) → map-out p r point ≡ p
    map-out-rotate
      : ∀ {ℓ} {X : Type ℓ} (p : X) (r : X ≃ X) (i : ℤ)
      → map-out p r (rotate .fst i) ≡ r .fst (map-out p r i)
```

We obtain a sort of initiality by requiring that `map-out`{.Agda} be
unique among functions with these properties.

```agda
    map-out-unique
      : ∀ {ℓ} {X : Type ℓ} (f : ℤ → X) {p : X} {r : X ≃ X}
      → f point ≡ p
      → (∀ x → f (rotate .fst x) ≡ r .fst (f x))
      → ∀ x → f x ≡ map-out p r x
```

<!--
```agda
  map-out-rotate-inv
    : ∀ {ℓ} {X : Type ℓ} (p : X) (r : X ≃ X) (i : ℤ)
    → map-out p r (Equiv.from rotate i)
    ≡ Equiv.from r (map-out p r i)
  map-out-rotate-inv p r i =
      sym (Equiv.η r _)
    ·· ap (Equiv.from r) (sym (map-out-rotate p r _))
    ·· ap (Equiv.from r ∘ map-out p r) (Equiv.ε rotate i)
```
-->

We now prove that the integers are a set of integers. This isn't as
tautological as it sounds, sadly, because our integers were designed to
be convenient for _algebra_, and this specific universal property is
rather divorced from algebra. Fortunately, it's still not too hard, so
join me.

```agda
open Integers

Int-integers : Integers Int
Int-integers = r where
  module map-out {ℓ} {X : Type ℓ} (l : X ≃ X) where
```

We start by making a simple observation: Exponentiation commutes with
difference, where by exponentiation we mean iterated composition of
equivalences. That is: if $n$ is an integer expressed as a formal
difference of naturals $x - y$, then we can compute the power $f^n : X
\simeq X$ as the difference of equivalences $(f^y)^{-1} \circ f^x$.

```agda
    n-power : Nat → X ≃ X
    n-power zero    = (λ x → x) , id-equiv
    n-power (suc x) = n-power x ∙e l

    private
      lemma : ∀ m n x
        → (n-power n e⁻¹) .fst (n-power m .fst x)
        ≡ (n-power n e⁻¹) .fst (Equiv.from (l) (l .fst (n-power m .fst x)))
      lemma m n x = ap ((n-power n e⁻¹) .fst) (sym (Equiv.η l _))

    map : Int → X ≃ X
    map (diff x y) = n-power x ∙e (n-power y e⁻¹)
    map (quot m n i) = Σ-prop-path is-equiv-is-prop
      {x = n-power m ∙e (n-power n e⁻¹)}
      {y = n-power (suc m) ∙e (n-power (suc n) e⁻¹)}
      (funext (lemma m n)) i
```

To show that this computation respects the quotient, we must calculate
that $(f^y)^{-1} \circ f^{-1}f \circ f^x$ is $(f^y)^{-1} \circ f^x$,
which follows almost immediately from the properties of equivalences,
cancelling the $f^{-1}f$ critical pair in the middle.

<!--
```agda
    negatives   : ∀ k x → Equiv.from (n-power k) (l .fst x) ≡ l .fst (Equiv.from (n-power k) x)
    negatives⁻¹ : ∀ k x → Equiv.from (n-power k) (Equiv.from l x) ≡ Equiv.from l (Equiv.from (n-power k) x)

    negatives zero x = refl
    negatives (suc k) x =
        ap (Equiv.from (n-power k)) (Equiv.η l x)
      ∙ sym (ap (l .fst) (negatives⁻¹ k x) ∙ Equiv.ε l _)

    negatives⁻¹ zero x = refl
    negatives⁻¹ (suc k) x = negatives⁻¹ k _

    abstract
      map-suc : ∀ i x → map (sucℤ i) .fst x ≡ l .fst (map i .fst x)
      map-suc = Int-elim-by-sign
        (λ i → ∀ x → map (sucℤ i) .fst x ≡ l .fst (map i .fst x))
        (λ _ _ → refl)
        negatives
        (λ _ → refl)
```
-->

```agda
  r : Integers Int
  r .ℤ-is-set = hlevel 2
  r .point = 0
  r .rotate = sucℤ , sucℤ-is-equiv
  r .map-out point rot int = map-out.map rot int .fst point
  r .map-out-point p _ = refl
  r .map-out-rotate p rot i = map-out.map-suc rot i _
```

Using elimination by _sign_, we can divide the proof of uniqueness to
the case where $n$ is a positive natural number, where $n$ is a negated
natural number, and when $n$ is zero. The case $n = 0$ is one of the
assumptions, the other cases follow by induction (on naturals).

```agda
  r .map-out-unique {X = X} f {point} {rot} path htpy =
    Int-elim-by-sign (λ z → f z ≡ r .map-out _ _ z) unique-pos unique-neg path
    where abstract
      unique-pos : ∀ k → f (diff k 0) ≡ map-out.n-power rot k .fst point
      unique-pos zero = path
      unique-pos (suc k) = htpy (diff k 0) ∙ ap (rot .fst) (unique-pos k)

      unique-neg : ∀ k → f (diff 0 k) ≡ Equiv.from (map-out.n-power rot k) point
      unique-neg zero = path
      unique-neg (suc k) =
           sym (Equiv.η rot _)
        ·· ap (Equiv.from rot) (
               sym (htpy (diff 0 (suc k)))
            ·· ap f (sym (quot 0 k))
            ·· unique-neg k)
        ·· sym (map-out.negatives⁻¹ rot k _)
```
