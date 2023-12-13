<!--
```agda
open import Cat.Displayed.Comprehension.Coproduct.Strong
open import Cat.Displayed.Comprehension.Coproduct
open import Cat.Displayed.Cartesian.Indexing
open import Cat.Displayed.Comprehension
open import Cat.Displayed.Cocartesian
open import Cat.Displayed.Cartesian
open import Cat.Morphism.Orthogonal
open import Cat.Displayed.Fibre
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Reasoning
import Cat.Reasoning
```
-->

```agda
module Cat.Displayed.Comprehension.Coproduct.VeryStrong where
```

# Very strong comprehension coproducts {defines="very-strong-comprehension-coproduct"}

As noted in [[strong comprehension coproducts]], the elimination
principle for [[comprehension coproducts]] is quite weak, being more of
a _recursion_ principle. Strong coproducts model coproducts with a
proper _elimination_, but as also noted there, we're lacking large
elimination. If we want that, we have to find **very strong
comprehension coproducts**.

Let $\cD$ and $\cE$ be [[comprehension categories]] over $\cB$.
We say that $\cD$ has **very strong $\cE$-comprehension coproducts** if
the canonical substitution

$$
\pi_{\cE}, \langle x , a \rangle : \Gamma,_{\cE}X,_{\cD}A \to \Gamma,_{\cD}\textstyle\coprod_X A
$$

is an isomorphism.

<!--
```agda
module _
  {ob ℓb od ℓd oe ℓe} {B : Precategory ob ℓb}
  {D : Displayed B od ℓd} {E : Displayed B oe ℓe}
  {D-fib : Cartesian-fibration D} {E-fib : Cartesian-fibration E}
  (P : Comprehension D) {Q : Comprehension E}
  (coprods : has-comprehension-coproducts D-fib E-fib Q)
  where
  private
    open Cat.Reasoning B
    module E = Displayed E
    module D = Displayed D
    module P = Comprehension D D-fib P
    module Q = Comprehension E E-fib Q
    open has-comprehension-coproducts coprods
```
-->

```agda
  very-strong-comprehension-coproducts : Type _
  very-strong-comprehension-coproducts =
    ∀ {Γ} (x : E.Ob[ Γ ]) (a : D.Ob[ Γ Q.⨾ x ])
    → is-invertible (Q.πᶜ P.⨾ˢ ⟨ x , a ⟩)
```

<!--
```agda
module very-strong-comprehension-coproducts
  {ob ℓb od ℓd oe ℓe} {B : Precategory ob ℓb}
  {D : Displayed B od ℓd} {E : Displayed B oe ℓe}
  {D-fib : Cartesian-fibration D} {E-fib : Cartesian-fibration E}
  (P : Comprehension D) {Q : Comprehension E}
  (coprods : has-comprehension-coproducts D-fib E-fib Q)
  (vstrong : very-strong-comprehension-coproducts P coprods)
  where
  private
    open Cat.Reasoning B
    module E = Displayed E
    module D = Displayed D
    module P = Comprehension D D-fib P
    module Q = Comprehension E E-fib Q
    open has-comprehension-coproducts coprods
    module vstrong {Γ} (x : E.Ob[ Γ ]) (a : D.Ob[ Γ Q.⨾ x ]) =
      is-invertible (vstrong x a)
```
-->

This gives us the familiar first and second projections out of the
coproduct.

```agda
  opaque
    ∐-fst
      : ∀ {Γ} (x : E.Ob[ Γ ]) (a : D.Ob[ Γ Q.⨾ x ])
      → Hom (Γ P.⨾ ∐ x a) (Γ Q.⨾ x)
    ∐-fst x a = P.πᶜ ∘ vstrong.inv x a

  opaque
    ∐-snd
      : ∀ {Γ} (x : E.Ob[ Γ ]) (a : D.Ob[ Γ Q.⨾ x ])
      → Hom (Γ P.⨾ ∐ x a) (Γ Q.⨾ x P.⨾ a)
    ∐-snd x a = vstrong.inv x a
```

These come with their respective $\beta$ rules, but they are slightly
obfuscated due to having to work with _substitutions_ rather than terms.

```agda
  opaque
    unfolding ∐-fst
    ∐-fst-β
      : ∀ {Γ} (x : E.Ob[ Γ ]) (a : D.Ob[ Γ Q.⨾ x ])
      → ∐-fst x a ∘ (Q.πᶜ P.⨾ˢ ⟨ x , a ⟩) ≡ P.πᶜ
    ∐-fst-β x a = cancelr (vstrong.invr x a)

  opaque
    unfolding ∐-snd
    ∐-snd-β
      : ∀ {Γ} (x : E.Ob[ Γ ]) (a : D.Ob[ Γ Q.⨾ x ])
      → ∐-snd x a ∘ (Q.πᶜ P.⨾ˢ ⟨ x , a ⟩) ≡ id
    ∐-snd-β x a = vstrong.invr x a
```

We also have an $\eta$ law, though this too is still a bit obfuscated.

```agda
  opaque
    unfolding ∐-fst ∐-snd
    ∐-very-strong-η
      : ∀ {Γ} (x : E.Ob[ Γ ]) (a : D.Ob[ Γ Q.⨾ x ])
      → (Q.πᶜ P.⨾ˢ ⟨ x , a ⟩) ∘ ∐-snd x a ≡ id
    ∐-very-strong-η x a = vstrong.invl x a
```

Note that very strong coproducts are always strong.

```agda
  strong : strong-comprehension-coproducts P coprods
  strong = to-strong-comprehension-coproducts P coprods mkstrong where
    open make-strong-comprehension-coproducts

    mkstrong : make-strong-comprehension-coproducts P coprods
    mkstrong .∐-strong-elim σ ν p = ν ∘ ∐-snd _ _
    mkstrong .∐-strong-β p = cancelr (∐-snd-β _ _)
    mkstrong .∐-strong-sub p = pulll (sym p) ∙ cancelr (∐-very-strong-η _ _)
    mkstrong .∐-strong-η p other β η = intror (∐-very-strong-η _ _) ∙ pulll β
```

## Strong coproducts over the same category are very strong

Let $\cE$ be a comprehension category over $\cB$ having comprehension
coproducts _over itself_. If these coproducts are strong, then they are
automatically very strong. That should make sense: we have have been
motivating *strong* comprehension coproducts as having elimination but
no large elimination, but if we only have one "size" going around, then
elimination _is_ large elimination!

```agda
module _
  {ob ℓb oe ℓe} {B : Precategory ob ℓb}
  {E : Displayed B oe ℓe}
  {E-fib : Cartesian-fibration E}
  {P : Comprehension E}
  (coprods : has-comprehension-coproducts E-fib E-fib P)
  where
```

<!--
```agda
  private
    open Cat.Reasoning B
    module E = Displayed E
    module E* {Γ Δ : Ob} (σ : Hom Γ Δ) = Functor (base-change E E-fib σ)
    module E-fib {x y} (f : Hom x y) (y' : E.Ob[ y ]) =
      Cartesian-lift (Cartesian-fibration.has-lift E-fib f y')
    open Comprehension E E-fib P
    open has-comprehension-coproducts coprods
```
-->

```agda
  self-strong-comprehension-coproducts→very-strong
    : strong-comprehension-coproducts P coprods
    → very-strong-comprehension-coproducts P coprods
```

We begin by defining a first projection $\Gamma, \coprod X A \to \Gamma,
X$ by factorizing the following square. This really is special: in the
case of _strong_ comprehension coproducts, $\Gamma, X$ and $\Gamma, X,
D$ correspond to _different_ context extensions (analogy: the first
extends the context by a kind, the second by a type). But since we're
dealing with _very strong_ coproducts, they're the same extension.

~~~{.quiver}
\begin{tikzcd}
  {\Gamma,X,A} && {\Gamma,X} \\
  \\
  {\Gamma,\coprod X A} && \Gamma
  \arrow["{\pi,\langle X, A\rangle}"', from=1-1, to=3-1]
  \arrow["\pi", from=1-3, to=3-3]
  \arrow["\pi"', from=3-1, to=3-3]
  \arrow["\pi", from=1-1, to=1-3]
  \arrow["{\mathit{fst}}", dashed, from=3-1, to=1-3]
\end{tikzcd}
~~~

We can then define the second projection
$\Gamma, \coprod X A \to \Gamma, X, A$ using the first.

~~~{.quiver}
\begin{tikzcd}
  {\Gamma,X,A} && {\Gamma,X,A} \\
  \\
  {\Gamma,\coprod X A} && {\Gamma,X}
  \arrow["{\pi,\langle X, A\rangle}"', from=1-1, to=3-1]
  \arrow["\pi", from=1-3, to=3-3]
  \arrow["{\mathit{fst}}"', from=3-1, to=3-3]
  \arrow["\id", from=1-1, to=1-3]
  \arrow["{\mathit{snd}}", dashed, from=3-1, to=1-3]
\end{tikzcd}
~~~

The $\beta$ and $\eta$ laws follow from some short calculations.

```agda
  self-strong-comprehension-coproducts→very-strong strong {Γ = Γ} x a =
    make-invertible
      ∐-strong-snd
      ∐-strong-snd-η
      (∐-strong-β ∐-strong-fst-β)
    where
      open strong-comprehension-coproducts P coprods strong

      ∐-strong-fst : Hom (Γ ⨾ ∐ x a) (Γ ⨾ x)
      ∐-strong-fst = ∐-strong-elim πᶜ πᶜ (sub-proj ⟨ x , a ⟩)

      ∐-strong-fst-β : ∐-strong-fst ∘ (πᶜ ⨾ˢ ⟨ x , a ⟩) ≡ πᶜ ∘ id
      ∐-strong-fst-β = ∐-strong-β _ ∙ sym (idr _)

      ∐-strong-snd : Hom (Γ ⨾ ∐ x a) (Γ ⨾ x ⨾ a)
      ∐-strong-snd = ∐-strong-elim ∐-strong-fst id ∐-strong-fst-β

      ∐-strong-snd-forget : πᶜ ∘ (πᶜ ⨾ˢ ⟨ x , a ⟩) ∘ ∐-strong-snd ≡ πᶜ
      ∐-strong-snd-forget =
        πᶜ ∘ (πᶜ ⨾ˢ ⟨ x , a ⟩) ∘ ∐-strong-snd ≡⟨ pulll (sub-proj ⟨ x , a ⟩) ⟩
        (πᶜ ∘ πᶜ) ∘ ∐-strong-snd              ≡⟨ pullr (∐-strong-sub ∐-strong-fst-β) ⟩
        (πᶜ ∘ ∐-strong-fst)                   ≡⟨ ∐-strong-sub (sub-proj ⟨ x , a ⟩) ⟩
        πᶜ                                    ∎

      ∐-strong-snd-η : (πᶜ ⨾ˢ ⟨ x , a ⟩) ∘ ∐-strong-snd ≡ id
      ∐-strong-snd-η =
        ∐-strong-η refl _ (cancelr (∐-strong-β ∐-strong-fst-β)) ∐-strong-snd-forget
        ∙ ∐-strong-id
```
