---
description: |
  F-Algebras, Lambek's lemma, Adámek's theorem.
---
<!--
```agda
open import Data.Nat

open import Cat.Diagram.Colimit.Base
open import Cat.Diagram.Initial
open import Cat.Diagram.Free
open import Cat.Prelude

open import Cat.Displayed.Base
open import Cat.Displayed.Total

open import Order.Instances.Nat
open import Order.Cat

import Cat.Reasoning
import Cat.Functor.Reasoning
```
-->
```agda
module Cat.Displayed.Instances.F-Algebras where
```

```agda
module _ {o ℓ} {C : Precategory o ℓ} (F : Functor C C) where
```

# Algebras over an endofunctor {defines="f-algebra algebra-over-an-endofunctor"}

<!--
```agda
  open Cat.Reasoning C
  module F = Cat.Functor.Reasoning F
  open Displayed
  open Total-hom
```
-->

Let $F : \cC \to \cC$ be an arbitrary endofunctor on $\cC$. We can view
$F$ as a means of embellishing an object with extra structure: for
instance, the functor $X \mapsto X + 1$ endows $X$ with an additional
point and an endomap $X \to X$, the functor $X \mapsto A \times X + 1$
adds an extra point and a copy of $A$, etc. Consequently, a map $\cC(F(A), A)$
picks out a suitably structured $A$; e.g. writing a map $\cC(A + 1, A)$
requires $A$ to be equipped with a global element and an endomap $\cC(A,A)$.
In analogy to [[monad algebras]], a map $\cC(F(A),A)$ is called an
**F-algebra** on $A$.[^Alternatively, we can view $F$-algebras as monad
algebras over functors that lack algebraic structure.]

Likewise, a map $f : \cC(A,B)$ between two $F$-algebras $\alpha : \cC(F(A),A)$
and $\beta : \cC(F(B), B)$ is an **F-algebra homomorphism** if it commutes
with the algebras on $A$ and $B$, as in the following digram.

~~~{.quiver}
\begin{tikzcd}
  {F(A)} && {F(B)} \\
  \\
  A && B
  \arrow["\alpha"', from=1-1, to=3-1]
  \arrow["f"', from=3-1, to=3-3]
  \arrow["\beta", from=1-3, to=3-3]
  \arrow["{F(f)}", from=1-1, to=1-3]
\end{tikzcd}
~~~

Intuitively, $F$-algebra morphisms are morphisms that preserve the structure
encoded by $F$; going back to our previous example, an $F$-algebra homomorphism
between $\alpha : A + 1 \to A$ and $\beta : B + 1 \to B$ is a map
$f : A \to B$ that preserves the designated global elements of $A$ and $B$
and commutes with the chosen endomaps.

$F$-algebras and their homomorphisms assemble into a displayed category
over $\cC$: the type of objects over $A$ consists of all possible algebra
structures on $A$, and the type of morphisms over $f : \cC(A,B)$ are
proofs that $f$ is an $F$-algebra.

```agda
  F-Algebras : Displayed C ℓ ℓ
  F-Algebras .Ob[_] a = Hom (F.₀ a) a
  F-Algebras .Hom[_] f α β = f ∘ α ≡ β ∘ F.₁ f
  F-Algebras .Hom[_]-set = hlevel!
  F-Algebras .id' = idl _ ∙ intror F.F-id
  F-Algebras ._∘'_ p q = pullr q ∙ pulll p ∙ pullr (sym (F.F-∘ _ _))
  F-Algebras .idr' _ = prop!
  F-Algebras .idl' _ = prop!
  F-Algebras .assoc' _ _ _ = prop!
```

We can take the [[total category]] of this displayed category to recover
the more traditional category of $F$-algebras.

```agda
  FAlg : Precategory (o ⊔ ℓ) ℓ
  FAlg = ∫ F-Algebras

  module FAlg = Cat.Reasoning FAlg

  F-Algebra : Type _
  F-Algebra = FAlg.Ob
```

## Lambek's lemma {defines="lambeks-lemma"}

As noted above, $F$-algebras are a tool for picking out objects equipped
with a semantics for a "signature" described by $F$. This leads to a very
natural question: can we characterize the syntax generated from the
signature of $F$?

To answer this question, we must pin down exactly what we mean by "syntax".
Categorically, we have two options: [[initial objects]], and
[[free objects]]; these correspond to "syntax" and "syntax with generators",
respectively. We will focus initial $F$-algebras for now: free objects are
much harder to come by, and initial $F$-algebras have a nice characterization:
they are the *least fixpoints* of functors. This result is known as Lambek's
lemma, and we shall prove it now.

First, a tiny lemma. Let $(A, \alpha)$ be an $F$-algebra, and note that
$(F(A), F(\alpha))$ is also an $F$-algebra. If $\alpha$ has a section
$f : (A, \alpha) \to (F(A), F(\alpha))$, then $f$ and $\alpha$ are
inverses.

```agda
  algebra-section→inverses
    : ∀ {a} (α : Hom (F.₀ a) a)
    → (f : FAlg.Hom (a , α) (F.₀ a , F.₁ α))
    → f .hom section-of α
    → Inverses α (f .hom)
  algebra-section→inverses α f section =
    make-inverses section $
      f .hom ∘ α           ≡⟨ f .preserves ⟩
      F.₁ α ∘ F.₁ (f .hom) ≡⟨ F.annihilate section ⟩
      id ∎
```

On to the main result. Let $(A, \alpha)$ be an initial $F$-algebra. As before,
$(F(A), F(\alpha))$ is also an $F$-algebra, so initiality gives us a unique
$F$-algebra morphism $\textrm{unroll} : (A, \alpha) \to (F(A), F(\alpha))$.
Likewise, $\alpha$ induces an $F$-algebra morphism $\textrm{roll} : (F(A), F(\alpha) \to (A, \alpha)$.
Furthermore, $\textrm{unroll}$ is a section of $\textrm{roll}$, as maps
out of the initial object are unique. Therefore, $\textrm{unroll}$ must
also be an inverse, so $\alpha$ is invertible.

```agda
  lambek : ∀ {a} (α : Hom (F.₀ a) a) → is-initial FAlg (a , α) → is-invertible α
  lambek {a} α initial = inverses→invertible $
    algebra-section→inverses α unroll roll-unroll
    where
      unroll : FAlg.Hom (a , α) (F.₀ a , F.₁ α)
      unroll = initial (F.₀ a , F.₁ α) .centre

      roll : FAlg.Hom (F.₀ a , F.₁ α) (a , α)
      roll .hom = α
      roll .preserves = refl

      roll-unroll : α ∘ unroll .hom ≡ id
      roll-unroll =
        ap hom $
        is-contr→is-prop (initial (a , α)) (roll FAlg.∘ unroll) FAlg.id
```

This result means that an initial $F$-algebra $(A, \alpha)$ is a fixpoint of the
functor $F$, and should be thought of as the the object $F(F(F(\cdots)))$.
The canonical example is the initial algebra of $X \mapsto 1 + X$: if it
exists, this will be an object of the form $1 + (1 + (1 + \cdots))$: in
$\Sets$, this initial algebra is the natural numbers! In general, initial
$F$-algebras are how we give a categorical semantics to non-indexed
inductive datatypes like `Nat`{.Agda}, `List`{.Agda}, etc.

## Adámek's fixpoint theorem {defines="adameks-theorem"}

Note that initial $F$-algebras need not exist for a given functor $F$.
Nevertheless, **Adámek's fixpoint theorem** lets us can construct some
initial $F$-algebras, provided that:

1. $\cC$ has an initial object.
2. $\cC$ has a colimit for the diagram:
~~~{.quiver}
\begin{tikzcd}
  \bot && {F(\bot)} && {F(F(\bot))} && \cdots
  \arrow["{!}", from=1-1, to=1-3]
  \arrow["{F(!)}", from=1-3, to=1-5]
  \arrow[from=1-5, to=1-7]
\end{tikzcd}
~~~
3. $F$ preserves the aforementioned colimit.

Note that this construction is precisely a categorified version of
[[Kleene's fixpoint theorem]], so we will be following the exact same
proof strategy.

We begin by constructing the above diagram as a functor $F^{(-)}(\bot)\omega \to \cC$,
where $\omega$ is the [[poset of natural numbers]], regarded as a category.

<!--
```agda
  private
    ω : Precategory _ _
    ω = poset→category Nat-poset

  module _
    (initial : Initial C)
    where

    open Functor
    open Initial initial
```
-->

```agda
    F₀ⁿ[⊥] : Nat → Ob
    F₀ⁿ[⊥] zero = bot
    F₀ⁿ[⊥] (suc n) = F.₀ (F₀ⁿ[⊥] n)

    F₁ⁿ[⊥] : ∀ {m n} → m ≤ n → Hom (F₀ⁿ[⊥] m) (F₀ⁿ[⊥] n)
    F₁ⁿ[⊥] 0≤x = ¡
    F₁ⁿ[⊥] (s≤s p) = F.₁ (F₁ⁿ[⊥] p)

    Fⁿ[⊥] : Functor ω C
```

<details>
<summary>Functoriality follows from some straightforward induction.
</summary>

```agda
    Fⁿ[⊥]-id : ∀ n → F₁ⁿ[⊥] (≤-refl {n}) ≡ id
    Fⁿ[⊥]-id zero = ¡-unique id
    Fⁿ[⊥]-id (suc n) = F.elim (Fⁿ[⊥]-id n)

    Fⁿ[⊥]-∘
      : ∀ {m n o}
      → (p : n ≤ o) (q : m ≤ n)
      → F₁ⁿ[⊥] (≤-trans q p) ≡ F₁ⁿ[⊥] p ∘ F₁ⁿ[⊥] q
    Fⁿ[⊥]-∘ p 0≤x = ¡-unique₂ _ _
    Fⁿ[⊥]-∘ (s≤s p) (s≤s q) = F.expand (Fⁿ[⊥]-∘ p q)

    Fⁿ[⊥] .F₀ = F₀ⁿ[⊥]
    Fⁿ[⊥] .F₁ = F₁ⁿ[⊥]
    Fⁿ[⊥] .F-id {n} = Fⁿ[⊥]-id n
    Fⁿ[⊥] .F-∘ p q = Fⁿ[⊥]-∘ p q
```
</details>

Next, note that every $F$-algebra $(A, \alpha)$ can be extended to
a morphism $\cC(F^{n}(\bot), A)$. Furthermore, this extension is natural
in $n$.

```agda
    Fⁿ[⊥]-fold : ∀ {a} → Hom (F.₀ a) a → ∀ n → Hom (F₀ⁿ[⊥] n) a
    Fⁿ[⊥]-fold α zero = ¡
    Fⁿ[⊥]-fold α (suc n) = α ∘ F.₁ (Fⁿ[⊥]-fold α n)

    Fⁿ[⊥]-fold-nat
      : ∀ {a} {α : Hom (F.₀ a) a} {m n}
      → (m≤n : m ≤ n)
      → Fⁿ[⊥]-fold α n ∘ F₁ⁿ[⊥] m≤n ≡ Fⁿ[⊥]-fold α m
    Fⁿ[⊥]-fold-nat 0≤x = sym (¡-unique _)
    Fⁿ[⊥]-fold-nat (s≤s m≤n) = F.pullr (Fⁿ[⊥]-fold-nat m≤n)
```

Now, suppose that $\cC$ has a colimit $F^{\infty}(\bot)$ of the diagram
$F^{(-)}(\bot)$, and $F$ preserves this colimit. We can equip $F^{\infty}(\bot)$
with an $F$-algebra $\mathrm{roll} : F(F^{\infty}(\bot)) \to F^{\infty}(\bot)$
by using the universal property of the colimit $F(F^{\infty}(\bot))$.

```agda
    adamek : Colimit Fⁿ[⊥] → preserves-colimit F Fⁿ[⊥] → Initial FAlg
    adamek Fⁿ[⊥]-colim F-pres-Fⁿ[⊥]-colim = ∐Fⁿ[⊥]-initial
      module adamek where
      module ∐Fⁿ[⊥] = Colimit Fⁿ[⊥]-colim
      module F[∐Fⁿ[⊥]] = is-colimit (F-pres-Fⁿ[⊥]-colim (∐Fⁿ[⊥].has-colimit))
      module F-pres-Fⁿ[⊥] = preserves-colimit F-pres-Fⁿ[⊥]-colim

      ∐Fⁿ[⊥] : Ob
      ∐Fⁿ[⊥] = ∐Fⁿ[⊥].coapex

      roll : Hom (F.₀ ∐Fⁿ[⊥]) ∐Fⁿ[⊥]
      roll = F[∐Fⁿ[⊥]].universal (∐Fⁿ[⊥].ψ ⊙ suc) (∐Fⁿ[⊥].commutes ⊙ s≤s)
```

Next, we can extend any F-algebra $(A, \alpha)$ to a morphism $F^{\infty}(\bot)$
by using the universal property, along with the extensions $\cC(F^{n}(\bot), A)$
we constructed earlier.

```agda
      fold : ∀ {a} → Hom (F.₀ a) a → Hom ∐Fⁿ[⊥] a
      fold α = ∐Fⁿ[⊥].universal (Fⁿ[⊥]-fold α) Fⁿ[⊥]-fold-nat
```

This extension commutes with $\mathrm{roll}$, and thus induces an
$F$-algebra morphism $(F^{\infty}(\bot), \mathrm{roll}) \to (A, \alpha)$.

```agda
      fold-roll : ∀ {a} (α : Hom (F.₀ a) a) → fold α ∘ roll ≡ α ∘ F.₁ (fold α)
      fold-roll α =
        F[∐Fⁿ[⊥]].unique₂ (Fⁿ[⊥]-fold α ⊙ suc) (Fⁿ[⊥]-fold-nat ⊙ s≤s)
          (λ j →
            (fold α ∘ roll) ∘ F.₁ (∐Fⁿ[⊥].ψ j) ≡⟨ pullr (F[∐Fⁿ[⊥]].factors _ _) ⟩
            fold α ∘ ∐Fⁿ[⊥].ψ (suc j)          ≡⟨ ∐Fⁿ[⊥].factors _ _ ⟩
            Fⁿ[⊥]-fold α (suc j)               ∎)
          (λ j →
            (α ∘ F.₁ (fold α)) ∘ F.₁ (∐Fⁿ[⊥].ψ j) ≡⟨ F.pullr (∐Fⁿ[⊥].factors _ _) ⟩
            α ∘ F.F₁ (Fⁿ[⊥]-fold α j)             ∎)
```

Furthermore, this extension is unique: this follows from a quick induction
paired with the universal property of $F^{\infty}(\bot)$.

```agda
      fold-step
        : ∀ {a} {α : Hom (F.₀ a) a}
        → (f : Hom ∐Fⁿ[⊥] a)
        → f ∘ roll ≡ α ∘ F.₁ f
        → ∀ n → f ∘ ∐Fⁿ[⊥].ψ n ≡ Fⁿ[⊥]-fold α n
      fold-step {α = α} f p zero = sym (¡-unique _)
      fold-step {α = α} f p (suc n) =
         f ∘ ∐Fⁿ[⊥].ψ (suc n)               ≡˘⟨ ap (f ∘_) (F[∐Fⁿ[⊥]].factors _ _) ⟩
         f ∘ roll ∘ F.F₁ (∐Fⁿ[⊥].ψ n)       ≡⟨ pulll p ⟩
         (α ∘ F.F₁ f) ∘ F.F₁ (∐Fⁿ[⊥].ψ n)   ≡⟨ F.pullr (fold-step f p n) ⟩
         α ∘ F.₁ (Fⁿ[⊥]-fold _ n)           ∎

      fold-unique
        : ∀ {a} {α : Hom (F.₀ a) a}
        → (f : Hom ∐Fⁿ[⊥] a)
        → f ∘ roll ≡ α ∘ F.₁ f
        → fold α ≡ f
      fold-unique f p = sym $ ∐Fⁿ[⊥].unique _ _ _ (fold-step f p)
```

If we put all the pieces together, we observe that $(F^{\infty}(\bot), \mathrm{roll})$
is an initial $F$-algebra.

```agda
      ∐Fⁿ[⊥]-initial : Initial FAlg
      ∐Fⁿ[⊥]-initial .Initial.bot .fst = ∐Fⁿ[⊥]
      ∐Fⁿ[⊥]-initial .Initial.bot .snd = roll
      ∐Fⁿ[⊥]-initial .Initial.has⊥ (a , α) .centre .hom = fold α
      ∐Fⁿ[⊥]-initial .Initial.has⊥ (a , α) .centre .preserves = fold-roll α
      ∐Fⁿ[⊥]-initial .Initial.has⊥ (a , α) .paths f =
        total-hom-path F-Algebras (fold-unique (f .hom) (f .preserves)) prop!
```

