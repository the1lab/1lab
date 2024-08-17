---
description: |
  Partial Combinatory algebras.
---
<!--
```agda
open import 1Lab.Prelude

open import Data.Fin
open import Data.Vec.Base

open import Realizability.PAS
```
-->
```agda
module Realizability.PCA where
```

# Partial combinatory algebras

:::{.definition #partial-combinatory-algebra alias="pca"}
A **partial combinatory algebra** or **PCA** is a [[partial applicative structure]]
with abstraction operation that lets us interpret the untyped lambda
calculus. Explicitly, a PCA is a PAS $(A, \downarrow, \star)$ equipped
with an operation $\mathrm{abs} : \mathrm{Term}(A)_{n+1} \to \mathrm{Term}(A)_{n}$
such that:

- For every term $e : \mathrm{Term}(A)_{n+1}$ with $n+1$ free variables
  and every environment $\rho$, $\llbracket \mathrm{abs}(e) \rrbracket \rho$
  is defined; and
- For every term $e : \mathrm{Term}(A)_{n+1}$, environment $\rho$ and
  value $a$, $\llbracket e \rrbracket \rho \start a = \llbracket e \rrbracket (a, \rho)$.
:::

<!--
```agda
private variable
  ℓ ℓ' ℓ'' : Level
  A : Type ℓ
  k n : Nat
```
-->

```agda
record PCA-on (A : Type ℓ) : Type ℓ where
  field
    _⋆_ : A → A → A
    _↓ : A → Ω
    has-pas : is-pas _⋆_ _↓

  infixl 8 _⋆_

  open PAS has-pas public

  field
    abs : ∀ {n} → Term (1 + n) → Term n
    abs-def : {n : Nat} → {e : Term (1 + n)} → {ρ : Vec Val n} → ∣ eval (abs e) ρ ↓ ∣
    abs-eval
      : {n : Nat} {e : Term (1 + n)} {a : A} {ρ : Vec Val n}
      → (a↓ : ∣ a ↓ ∣)
      → (eval (abs e) ρ ⋆ a) ≡ eval e (value a a↓ ∷ ρ)
```

Working with de Bruijn indices is a bit annoying, so we expose an interface
that lets us pretend that we are using higher-order abstract syntax.

```agda
  abs-syntax : (Term (1 + n) → Term (1 + n)) → Term n
  abs-syntax k = abs (k (var 0))

  syntax abs-syntax (λ x → e) = ⟨ x ⟩ e
  infix 4 abs-syntax

```

## Programming with PCAs

The raison d'etre of PCAs is that they form a simple algebraic model
of computation, so let's write some programs! We begin by defining
n-ary versions of abstraction and application, and prove an n-ary
version of the 2nd PCA axiom.

```agda
module PCA (pca : PCA-on A) where
  open PCA-on pca public

  absₙ : (k : Nat) → Term (k + n) → Term n
  absₙ zero e = e
  absₙ (suc k) e = (absₙ k (abs e))

  _⋆ₙ_ : ∀ {n} → A → Vec Val n → A
  a ⋆ₙ [] = a
  a ⋆ₙ (b ∷ bs) = (a ⋆ₙ bs) ⋆ b .elt

  abs-evalₙ
    : {k n : Nat}
    → {e : Term (k + n)} {ρ : Vec Val n}
    → (as : Vec Val k)
    → (eval (absₙ k e) ρ ⋆ₙ as) ≡ eval e (as ++ᵥ ρ)
  abs-evalₙ [] = refl
  abs-evalₙ {k = suc k} {e =  e} {ρ = ρ} (a ∷ as) =
    ⌜ eval (absₙ k (abs e)) ρ ⋆ₙ as ⌝ ⋆ (a .elt) ≡⟨ ap! (abs-evalₙ as) ⟩
    eval (abs e) (as ++ᵥ ρ) ⋆ (a .elt)           ≡⟨ abs-eval (a .def) ⟩
    eval e ((a ∷ as) ++ᵥ ρ) ∎
```

With that out of the way, we can write our very first program: the
identity function!

```agda
  opaque
    “id” : A
    “id” = term (⟨ x ⟩ “ x ”)
```

We can also characterize the computational behaviour of the identity
function. The proof leverages Kleene extensionality: $\mathrm{abs}(0) \star a = a$
under the assumption that $a \downarrow$!

```agda
    id-eval : ∀ (a : A) → “id” ⋆ a ≡ a
    id-eval a = def-ext ∣ a ↓ ∣ ⋆-defr id abs-eval
```

<!--
```agda
    id-def : ∣ “id” ↓ ∣
    id-def = abs-def

    id-def₁ : ∀ {a} → ∣ a ↓ ∣ → ∣ (“id” ⋆ a) ↓ ∣
    id-def₁ a↓ = subst (λ e → ∣ e ↓ ∣) (sym (id-eval _)) a↓

  instance
    Defined-id : Defined “id”
    Defined-id .defined = id-def
```
-->

We can also define function composition.

```agda
  opaque
    “comp” : A
    “comp” = term (⟨ f ⟩ ⟨ g ⟩ ⟨ x ⟩ f “⋆” (g “⋆” x))
```

Kleene extensionality lets us prove that function composition acts like
function composition, though the proof is a bit more complicated than
the identity function!

```agda
    comp-eval : ∀ (f g a : A) → “comp” ⋆ f ⋆ g ⋆ a ≡ f ⋆ (g ⋆ a)
    comp-eval f g a =
      def-ext (∣ f ↓ ∣ × ∣ g ↓ ∣ × ∣ a ↓ ∣)
        (λ c↓ → ⋆-defr (⋆-defl (⋆-defl c↓)) , ⋆-defr (⋆-defl c↓) , ⋆-defr c↓)
        (λ c↓ → ⋆-defl c↓ , ⋆-defl (⋆-defr c↓) , ⋆-defr (⋆-defr c↓))
        (λ (f↓ , g↓ , a↓) → abs-evalₙ (value a a↓ ∷ value g g↓ ∷ value f f↓ ∷ []))
```

<!--
```agda
    comp-def : ∣ “comp” ↓ ∣
    comp-def = abs-def

    comp-def₂ : ∀ {f g : A} → ∣ f ↓ ∣ → ∣ g ↓ ∣ → ∣ (“comp” ⋆ f ⋆ g) ↓ ∣
    comp-def₂ f↓ g↓ = subst (λ e → ∣ e ↓ ∣) (sym (abs-evalₙ (value _ g↓ ∷ value _ f↓ ∷ []))) abs-def

  instance
    Defined-comp : Defined “comp”
    Defined-comp .defined = comp-def

    Defined-comp₂ : ∀ {f g : A} → ⦃ f↓ : Defined f ⦄ → ⦃ g↓ : Defined g ⦄ → Defined (“comp” ⋆ f ⋆ g)
    Defined-comp₂ .defined = comp-def₂ defined defined
```
-->

Next, we define constant functions.

```agda
  opaque
    “const” : A
    “const” = term (⟨ x ⟩ ⟨ y ⟩ “ x ”)

    “ignore” : A
    “ignore” = term (⟨ x ⟩ ⟨ y ⟩ “ y ”)
```

Once again, Kleene extensionality lets us characterise how constant
functions compute.

```agda
    const-eval : ∀ (a b : A) → ∣ b ↓ ∣ → “const” ⋆ a ⋆ b ≡ a
    const-eval a b b↓ =
      def-ext (∣ a ↓ ∣ × ∣ b ↓ ∣)
        (λ c↓ → (⋆-defr (⋆-defl c↓)) , ⋆-defr c↓)
        (λ a↓ → a↓ , b↓)
        (λ (a↓ , b↓) → abs-evalₙ (value b b↓ ∷ value a a↓ ∷ []))

    ignore-eval : ∀ (a b : A) → ∣ a ↓ ∣ → “ignore” ⋆ a ⋆ b ≡ b
    ignore-eval a b a↓ =
      def-ext (∣ a ↓ ∣ × ∣ b ↓ ∣)
        (λ c↓ → (⋆-defr (⋆-defl c↓)) , ⋆-defr c↓)
        (λ b↓ → a↓ , b↓)
        (λ (a↓ , b↓) → abs-evalₙ (value b b↓ ∷ value a a↓ ∷ []))

```

<!--
```agda
    const-def : ∣ “const” ↓ ∣
    const-def = abs-def

    ignore-def : ∣ “ignore” ↓ ∣
    ignore-def = abs-def

    const-def₁ : {x : A} → ∣ x ↓ ∣ → ∣ (“const” ⋆ x) ↓ ∣
    const-def₁ x↓ = subst (λ e → ∣ e ↓ ∣) (sym (abs-eval x↓)) abs-def

  instance
    Defined-const : Defined “const”
    Defined-const .defined = const-def

    Defined-ignore : Defined “ignore”
    Defined-ignore .defined = ignore-def
```
-->

We also have analog of the `flip`{.Agda} function.

```agda
  opaque
    “flip” : A
    “flip” = term (⟨ f ⟩ ⟨ x ⟩ ⟨ y ⟩ f “⋆” y “⋆” x)
```

<!--
```agda
    flip-def : ∣ “flip” ↓ ∣
    flip-def = abs-def

    flip-def₁ : ∀ {f} → ∣ f ↓ ∣ → ∣ (“flip” ⋆ f) ↓ ∣
    flip-def₁ f↓ = subst (λ e → ∣ e ↓ ∣) (sym (abs-eval f↓)) abs-def

    flip-def₂ : ∀ {f x} → ∣ f ↓ ∣ → ∣ x ↓ ∣ → ∣ (“flip” ⋆ f ⋆ x) ↓ ∣
    flip-def₂ f↓ x↓ = subst (λ e → ∣ e ↓ ∣) (sym (ap₂ _⋆_ (abs-eval f↓) refl ∙ (abs-eval x↓))) abs-def

```
-->

<details>
<summary>The characterisation of flip is more of the same, so we omit it.
</summary>
```agda
    flip-eval : ∀ f x y → “flip” ⋆ f ⋆ x ⋆ y ≡ f ⋆ y ⋆ x
    flip-eval f x y =
      def-ext (∣ f ↓ ∣ × ∣ x ↓ ∣ × ∣ y ↓ ∣)
        (λ p↓ → ⋆-defr (⋆-defl (⋆-defl p↓)) , ⋆-defr (⋆-defl p↓) , ⋆-defr p↓)
        (λ p↓ → ⋆-defl (⋆-defl p↓) , ⋆-defr p↓ , ⋆-defr (⋆-defl p↓))
        λ (f↓ , x↓ , y↓) →
      abs-evalₙ (value y y↓ ∷ value x x↓ ∷ value f f↓ ∷ [])
```
</details>

### Pairing

With those basics out of the way, we can build up some actual datastructures.
We start with pairs, as it is basically impossible to make any progress
without them. Like lambda calculi, all we have is functions and application,
so we must Church-encode all data. Luckily, we can use Church-encoded
pairs essentially verbaitim.

```agda
  opaque
    “pair” : A
    “pair” = term (⟨ x ⟩ ⟨ y ⟩ ⟨ p ⟩ p “⋆” x “⋆” y)

    “fst” : A
    “fst” = term (⟨ p ⟩ p “⋆” “const”)

    “snd” : A
    “snd” = term (⟨ p ⟩ p “⋆” “ignore”)
```

<!--
```agda
    fst-def : ∣ “fst” ↓ ∣
    fst-def = abs-def

    snd-def : ∣ “snd” ↓ ∣
    snd-def = abs-def

    pair-def : ∣ “pair” ↓ ∣
    pair-def = abs-def


    pair-def₂ : ∀ {a b : A} → ∣ a ↓ ∣ → ∣ b ↓ ∣ → ∣ (“pair” ⋆ a ⋆ b) ↓ ∣
    pair-def₂ {a = a} {b = b} a↓ b↓ =
      subst (λ e → ∣ e ↓ ∣) (sym (ap₂ _⋆_ (abs-eval a↓) refl ∙ (abs-eval b↓))) abs-def

    fst-eval : ∀ a → “fst” ⋆ a ≡ a ⋆ “const”
    fst-eval a =
      def-ext ∣ a ↓ ∣ ⋆-defr ⋆-defl abs-eval

    snd-eval : ∀ a → “snd” ⋆ a ≡ a ⋆ “ignore”
    snd-eval a =
      def-ext ∣ a ↓ ∣ ⋆-defr ⋆-defl abs-eval

    fst-def₁ : ∀ {a} → ∣ (a ⋆ “const”) ↓ ∣ → ∣ (“fst” ⋆ a) ↓ ∣
    fst-def₁ {a} p↓ =
      subst (λ e → ∣ e ↓ ∣) (sym (fst-eval a)) p↓

    snd-def₁ : ∀ {a} → ∣ (a ⋆ “ignore”) ↓ ∣ → ∣ (“snd” ⋆ a) ↓ ∣
    snd-def₁ {a} p↓ =
      subst (λ e → ∣ e ↓ ∣) (sym (snd-eval a)) p↓
```
-->

Following the usual pattern, we invoke Kleene extensionality to prove
the $\beta$-laws for pairs, though we need to do a bit more algebra
this time.

```agda
    fst-pair-eval : ∀ (a b : A) → ∣ b ↓ ∣ → “fst” ⋆ (“pair” ⋆ a ⋆ b) ≡ a
    fst-pair-eval a b b↓ =
      def-ext (∣ a ↓ ∣ × ∣ b ↓ ∣)
        (λ p↓ → ⋆-defr (⋆-defl (⋆-defr p↓)) , b↓)
        (λ a↓ → a↓ , b↓)
        (λ (a↓ , b↓) →
          “fst” ⋆ (“pair” ⋆ a ⋆ b) ≡⟨ abs-eval (pair-def₂ a↓ b↓) ⟩
          “pair” ⋆ a ⋆ b ⋆ “const” ≡⟨ abs-evalₙ (value “const” const-def ∷ value b b↓ ∷ value a a↓ ∷ []) ⟩
          “const” ⋆ a ⋆ b          ≡⟨ const-eval a b b↓ ⟩
          a ∎)

    snd-pair-eval : ∀ (a b : A) → ∣ a ↓ ∣ → “snd” ⋆ (“pair” ⋆ a ⋆ b) ≡ b
    snd-pair-eval a b a↓ =
      def-ext (∣ a ↓ ∣ × ∣ b ↓ ∣)
        (λ p↓ → a↓ , ⋆-defr (⋆-defr p↓))
        (λ b↓ → a↓ , b↓)
        (λ (a↓ , b↓) →
          “snd” ⋆ (“pair” ⋆ a ⋆ b)  ≡⟨ abs-eval (pair-def₂ a↓ b↓) ⟩
          “pair” ⋆ a ⋆ b ⋆ “ignore” ≡⟨ abs-evalₙ (value “ignore” ignore-def ∷ value b b↓ ∷ value a a↓ ∷ []) ⟩
          “ignore” ⋆ a ⋆ b          ≡⟨ ignore-eval a b a↓ ⟩
          b ∎)
```

<!--
```agda
  instance
    Defined-fst : Defined “fst”
    Defined-fst .defined = fst-def

    Defined-snd : Defined “snd”
    Defined-snd .defined = snd-def

    Defined-pair : Defined “pair”
    Defined-pair .defined = pair-def

  pair-val : Val → Val → Val
  pair-val v₁ v₂ = value (“pair” ⋆ v₁ .elt ⋆ v₂ .elt) (pair-def₂ (v₁ .def) (v₂ .def))
```
-->

We also take the time to define currying and uncurrying.

```agda
  opaque
    “curry” : A
    “curry” = term (⟨ f ⟩ ⟨ x ⟩ ⟨ y ⟩ f “⋆” (“pair” “⋆” x “⋆” y))

    “uncurry” : A
    “uncurry” = term (⟨ f ⟩ ⟨ xy ⟩ f “⋆” (“fst” “⋆” xy) “⋆” (“snd” “⋆” xy))

    curry-eval : ∀ (f a b : A) → “curry” ⋆ f ⋆ a ⋆ b ≡ f ⋆ (“pair” ⋆ a ⋆ b)
    uncurry-eval : ∀ (f a b : A) → “uncurry” ⋆ f ⋆ a ≡ f ⋆ (“fst” ⋆ a) ⋆ (“snd” ⋆ a)
```

<details>
<summary>The characterisations of currying and uncurrying are another
application of Kleene extensionality.
</summary>
```agda
    curry-eval f a b =
      def-ext (∣ f ↓ ∣ × ∣ a ↓ ∣ × ∣ b ↓ ∣)
        (λ p↓ → ⋆-defr (⋆-defl (⋆-defl p↓)) , ⋆-defr (⋆-defl p↓) , ⋆-defr p↓)
        (λ p↓ → ⋆-defl p↓ , ⋆-defr (⋆-defl (⋆-defr p↓)) , ⋆-defr (⋆-defr p↓))
        (λ (f↓ , a↓ , b↓) → abs-evalₙ (value b b↓ ∷ value a a↓ ∷ value f f↓ ∷ []))

    uncurry-eval f a b =
      def-ext (∣ f ↓ ∣ × ∣ a ↓ ∣)
        (λ p↓ → ⋆-defr (⋆-defl p↓) , ⋆-defr p↓)
        (λ p↓ → ⋆-defl (⋆-defl p↓) , ⋆-defr (⋆-defr p↓))
        (λ (f↓ , a↓) → abs-evalₙ (value a a↓ ∷ value f f↓ ∷ []))
```
</details>


### Booleans

Booleans are also represented via Church-encoding. We have already defined
both constant functions, so all we need to do is provide some more suggestive
names.

```agda
  “true” : A
  “true” = “const”

  “false” : A
  “false” = “ignore”
```

### Coproducts

Coproducts are encoded as pairs of a tag bit and data.

```agda
  opaque
    “inl” : A
    “inl” = term (⟨ x ⟩ “pair” “⋆” “true” “⋆” x)

    “inr” : A
    “inr” = term (⟨ x ⟩ “pair” “⋆” “false” “⋆” x)
```

The eliminator for coproducts is a bit subtle. We start by extracting
the tag bit from the scrutinee. This tag is then applied to methods
of the eliminator, taking advantage of the fact that booleans are represented
as binary functions. We then apply this to the data component of the product,
resulting in the somewhat opaque term $\langle l, r, x \rangle \mathrm{fst} x l r (\mathrm{snd} x)$

```agda
    “elim” : A
    “elim” = term (⟨ l ⟩ ⟨ r ⟩ ⟨ x ⟩ (“fst” “⋆” x) “⋆” l “⋆” r “⋆” (“snd” “⋆” x))
```

<!--
```agda
    inl-eval : (a : A) → “inl” ⋆ a ≡ “pair” ⋆ “true” ⋆ a
    inl-eval a = def-ext ∣ a ↓ ∣ ⋆-defr ⋆-defr abs-eval

    inr-eval : (a : A) → “inr” ⋆ a ≡ “pair” ⋆ “false” ⋆ a
    inr-eval a = def-ext ∣ a ↓ ∣ ⋆-defr ⋆-defr abs-eval

    inl-def : ∣ “inl” ↓ ∣
    inl-def = abs-def

    inr-def : ∣ “inr” ↓ ∣
    inr-def = abs-def

    inl-def₁ : {a : A} → ∣ a ↓ ∣ → ∣ (“inl” ⋆ a) ↓ ∣
    inl-def₁ a↓ = subst (λ e → ∣ e ↓ ∣) (sym (inl-eval _)) (pair-def₂ const-def a↓)

    inr-def₁ : {a : A} → ∣ a ↓ ∣ → ∣ (“inr” ⋆ a) ↓ ∣
    inr-def₁ a↓ = subst (λ e → ∣ e ↓ ∣) (sym (inr-eval _)) (pair-def₂ ignore-def a↓)

    elim-def₂ : {l r : A} → ∣ l ↓ ∣ → ∣ r ↓ ∣ → ∣ (“elim” ⋆ l ⋆ r) ↓ ∣
    elim-def₂ l↓ r↓ =
      subst (λ e → ∣ e ↓ ∣) (sym (abs-evalₙ (value _ r↓ ∷ value _ l↓ ∷ []))) abs-def
```
-->

We shall now prove the $\beta$-laws for coproducts.

```agda
    elim-inl-eval : ∀ (l r a : A) → ∣ r ↓ ∣ → “elim” ⋆ l ⋆ r ⋆ (“inl” ⋆ a) ≡ l ⋆ a
    elim-inr-eval : ∀ (l r a : A) → ∣ l ↓ ∣ → “elim” ⋆ l ⋆ r ⋆ (“inr” ⋆ a) ≡ r ⋆ a
```

We shall focus our attention on the left $\beta$-law. We start by applying
Kleene extensionality so that we can assume that all arguments are defined,
and then invoke the $\beta$ laws of pairs to get out the tag and data.
The rest follows from our characterisation of constant functions.

```agda
    elim-inl-eval l r a r↓ =
      def-ext (∣ l ↓ ∣ × ∣ r ↓ ∣ × ∣ a ↓ ∣)
        (λ p↓ → ⋆-defr (⋆-defl (⋆-defl p↓)) , ⋆-defr (⋆-defl p↓) , ⋆-defr (⋆-defr p↓))
        (λ la↓ → ⋆-defl la↓ , r↓ , (⋆-defr la↓))
        (λ (l↓ , r↓ , a↓) →
          “elim” ⋆ l ⋆ r ⋆ (“inl” ⋆ a)                                                ≡⟨ abs-evalₙ (value _ (inl-def₁ a↓) ∷ value r r↓ ∷ value l l↓ ∷ []) ⟩
          “fst” ⋆ ⌜ “inl” ⋆ a ⌝ ⋆ l ⋆ r ⋆ (“snd” ⋆ ⌜ “inl” ⋆ a ⌝)                     ≡⟨ ap! (inl-eval a) ⟩
          ⌜ “fst” ⋆ (“pair” ⋆ “true” ⋆ a) ⌝ ⋆ l ⋆ r ⋆ (“snd” ⋆ (“pair” ⋆ “true” ⋆ a)) ≡⟨ ap! (fst-pair-eval “true” a a↓) ⟩
          ⌜ “const” ⋆ l ⋆ r ⌝ ⋆ (“snd” ⋆ (“pair” ⋆ “true” ⋆ a))                       ≡⟨ ap! (const-eval l r r↓) ⟩
          l ⋆ ⌜ “snd” ⋆ (“pair” ⋆ “true” ⋆ a) ⌝                                       ≡⟨ ap! (snd-pair-eval “true” a const-def) ⟩
          l ⋆ a                                                                       ∎)
```

<details>
<summary>The right $\beta$-law follows from a similar line of reasoning.
</summary>
```agda
    elim-inr-eval l r a l↓ =
      def-ext (∣ l ↓ ∣ × ∣ r ↓ ∣ × ∣ a ↓ ∣)
        (λ p↓ → ⋆-defr (⋆-defl (⋆-defl p↓)) , ⋆-defr (⋆-defl p↓) , ⋆-defr (⋆-defr p↓))
        (λ ra↓ → l↓ , ⋆-defl ra↓ , (⋆-defr ra↓))
        (λ (l↓ , r↓ , a↓) →
          “elim” ⋆ l ⋆ r ⋆ (“inr” ⋆ a)                                                  ≡⟨ abs-evalₙ (value _ (inr-def₁ a↓) ∷ value r r↓ ∷ value l l↓ ∷ []) ⟩
          “fst” ⋆ ⌜ “inr” ⋆ a ⌝ ⋆ l ⋆ r ⋆ (“snd” ⋆ ⌜ “inr” ⋆ a ⌝)                       ≡⟨ ap! (inr-eval a) ⟩
          ⌜ “fst” ⋆ (“pair” ⋆ “false” ⋆ a) ⌝ ⋆ l ⋆ r ⋆ (“snd” ⋆ (“pair” ⋆ “false” ⋆ a)) ≡⟨ ap! (fst-pair-eval “false” a a↓) ⟩
          ⌜ “ignore” ⋆ l ⋆ r ⌝ ⋆ (“snd” ⋆ (“pair” ⋆ “false” ⋆ a))                       ≡⟨ ap! (ignore-eval l r l↓) ⟩
          r ⋆ ⌜ “snd” ⋆ (“pair” ⋆ “false” ⋆ a) ⌝                                        ≡⟨ ap! (snd-pair-eval “false” a ignore-def) ⟩
          r ⋆ a                                                                         ∎)
```
</details>

<!--
```agda
  inlv : Val → Val
  inlv a .elt = “inl” ⋆ a .elt
  inlv a .def = inl-def₁ (a .def)

  inrv : Val → Val
  inrv a .elt = “inr” ⋆ a .elt
  inrv a .def = inr-def₁ (a .def)
```
-->

### Fixpoints

```agda
  opaque
    “w” : A
    “w” = term (⟨ r ⟩ ⟨ f ⟩ (f “⋆” (r “⋆” r “⋆” f)))

    “fix” : A
    “fix” = “w” ⋆ “w”

    “u” : A
    “u” = term (⟨ r ⟩ ⟨ f ⟩ ⟨ x ⟩ (f “⋆” (r “⋆” r “⋆” f) “⋆” x))

    “loop” : A
    “loop” = “u” ⋆ “u”
```

<!--
```agda
    w-def : ∣ “w” ↓ ∣
    w-def = abs-def

    u-def : ∣ “u” ↓ ∣
    u-def = abs-def
```
-->

```agda
    fix-eval : ∀ f → “fix” ⋆ f ≡ f ⋆ (“fix” ⋆ f)
    fix-eval f =
      def-ext (∣ f ↓ ∣) ⋆-defr ⋆-defl λ f↓ →
      “w” ⋆ “w” ⋆ f         ≡⟨ abs-evalₙ (value f f↓ ∷ value “w” w-def ∷ []) ⟩
      (f ⋆ (“w” ⋆ “w” ⋆ f)) ∎

    loop-eval : ∀ f x → “loop” ⋆ f ⋆ x ≡ f ⋆ (“loop” ⋆ f) ⋆ x
    loop-eval f x =
      def-ext (∣ f ↓ ∣ × ∣ x ↓ ∣)
        (λ p↓ → ⋆-defr (⋆-defl p↓) , ⋆-defr p↓)
        (λ p↓ → ⋆-defl (⋆-defl p↓) , ⋆-defr p↓)
        (λ (f↓ , x↓) → abs-evalₙ (value x x↓ ∷ value f f↓ ∷ value “u” u-def ∷ []))
```


### Natural numbers

We encode natural numbers via **Curry numerals**, which encode
a natural number $n$ as an $n$-tuple where the first $n$ components
are `“true”`{.Agda}, and the final component is `“false”`{.Agda}.

```agda
  opaque
    “nat” : Nat → A
    “nat” zero = “false”
    “nat” (suc n) = “pair” ⋆ “true” ⋆ “nat” n

    “zero” : A
    “zero” = “false”

    “suc” : A
    “suc” = term (⟨ x ⟩ “pair” “⋆” “true” “⋆” x)
```

<!--
```agda
    zero-def : ∣ “zero” ↓ ∣
    zero-def = ignore-def

    zero-eval : “zero” ≡ “false”
    zero-eval = refl

    suc-eval : ∀ x → “suc” ⋆ x ≡ “pair” ⋆ “true” ⋆ x
    suc-eval x = def-ext ∣ x ↓ ∣ ⋆-defr ⋆-defr abs-eval

    suc-def₁ : ∀ {x} → ∣ x ↓ ∣ → ∣ (“suc” ⋆ x) ↓ ∣
    suc-def₁ x↓ = subst (λ e → ∣ e ↓ ∣) (sym (suc-eval _)) (pair-def₂ const-def x↓)

    nat-def : ∀ x → ∣ “nat” x ↓ ∣
    nat-def zero = ignore-def
    nat-def (suc x) = pair-def₂ const-def (nat-def x)

    nat-zero-eval : “nat” 0 ≡ “zero”
    nat-zero-eval = refl

    nat-suc-eval : ∀ x → “nat” (suc x) ≡ “suc” ⋆ (“nat” x)
    nat-suc-eval x = sym (abs-eval (nat-def x))
```
-->

We can define a predecessor function by examining the first component
of the tuple, and then using the church boolean within to select either
the rest of the Curry numeral or zero.

```agda
    “pred” : A
    “pred” = term (⟨ x ⟩ (“fst” “⋆” x) “⋆” (“snd” “⋆” x) “⋆” “zero”)
```

A bit of algebra lets us show that predecessor has the correct computational
behaviour.

```agda
    pred-zero-eval : “pred” ⋆ “zero” ≡ “zero”
    pred-zero-eval =
      “pred” ⋆ “zero”                                    ≡⟨ abs-eval zero-def ⟩
      ⌜ “fst” ⋆ “zero” ⌝ ⋆ (“snd” ⋆ “zero”)  ⋆ “zero”    ≡⟨ ap! (fst-eval “zero”) ⟩
      ⌜ “ignore” ⋆ “const” ⋆ (“snd” ⋆ “zero”) ⌝ ⋆ “zero” ≡⟨ ap! (ignore-eval “const” (“snd” ⋆ “zero”) const-def) ⟩
      ⌜ “snd” ⋆ “zero” ⌝ ⋆ “zero”                        ≡⟨ ap! (snd-eval “zero”) ⟩
      “ignore” ⋆ “ignore” ⋆ “zero”                       ≡⟨ ignore-eval “ignore” “zero” ignore-def ⟩
      “zero”                                             ∎

    pred-suc-eval : ∀ x → “pred” ⋆ (“suc” ⋆ x) ≡ x
    pred-suc-eval x =
      def-ext ∣ x ↓ ∣ (λ p↓ → ⋆-defr (⋆-defr p↓)) (λ x↓ → x↓) $ λ x↓ →
      “pred” ⋆ (“suc” ⋆ x)                                                         ≡⟨ abs-eval (suc-def₁ x↓) ⟩
      “fst” ⋆ ⌜ “suc” ⋆ x ⌝ ⋆ (“snd” ⋆ ⌜ “suc” ⋆ x ⌝) ⋆ “zero”                     ≡⟨ ap! (suc-eval x) ⟩
      ⌜ “fst” ⋆ (“pair” ⋆ “true” ⋆ x) ⌝ ⋆ (“snd” ⋆ (“pair” ⋆ “true” ⋆ x)) ⋆ “zero” ≡⟨ ap! (fst-pair-eval “true” x x↓) ⟩
      “true” ⋆ (“snd” ⋆ (“pair” ⋆ “true” ⋆ x)) ⋆ “zero”                            ≡⟨ const-eval _ _ zero-def ⟩
      “snd” ⋆ (“pair” ⋆ “true” ⋆ x)                                                ≡⟨ snd-pair-eval “true” x const-def ⟩
      x ∎
```
