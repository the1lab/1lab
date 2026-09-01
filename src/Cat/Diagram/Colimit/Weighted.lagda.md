---
description: |
  Weighted colimits.
---

<!--
```agda
open import Cat.Diagram.Coproduct.Indexed
open import Cat.Instances.Product.Duality
open import Cat.Instances.Shape.Terminal
open import Cat.Diagram.Colimit.Cocone
open import Cat.Diagram.Colimit.Base
open import Cat.Diagram.Coequaliser
open import Cat.Instances.Elements
open import Cat.Functor.Bifunctor
open import Cat.Instances.Product
open import Cat.Functor.Constant
open import Cat.Diagram.Coend
open import Cat.Functor.Base
open import Cat.Functor.Hom
open import Cat.Groupoid
open import Cat.Prelude

import Cat.Functor.Reasoning.Presheaf
import Cat.Functor.Reasoning
import Cat.Reasoning
```
-->

```agda
module Cat.Diagram.Colimit.Weighted where
```

<!--
```agda
module _
  {oc ℓc oj ℓj}
  {J : Precategory oj ℓj} {C : Precategory oc ℓc}
  where
  private
    module C = Cat.Reasoning C
    module J = Precategory J
    variable
      ℓw : Level
```
-->

# Weighted colimits

:::{.definition #weighted-colimit}
Let $W : \cJ\op \to \Sets_{\kappa}$ be a [[presheaf]], and $F : \cJ \to \cC$
be a functor. A diagram $\iota : (j : \cJ) \to W(j) \to \cC(F(j), \colim_{W} F)$
is a **$W$-weighted colimit** of $F$ when:

- $\iota$ is natural in $\cJ$, insofar that the following diagram commutes
for all $f : \cJ(I,J)$ and $w : W(J)$:

~~~{.quiver}
\begin{tikzcd}
  {F(i)} && \\
  \\
  {F(j)} && {\colim_W F}
  \arrow["{F(f)}"', from=1-1, to=3-1]
  \arrow["{\iota_{i,W(f)(w)}}", from=1-1, to=3-3]
  \arrow["{\iota_{j,w}}"', from=3-1, to=3-3]
\end{tikzcd}
~~~

```agda
  is-weighted-cocone
    : ∀ {coapex}
    → (W : Functor (J ^op) (Sets ℓw))
    → (F : Functor J C)
    → (∀ j → W ʻ j → C.Hom (F · j) coapex)
    → Type _
  is-weighted-cocone W F ψ =
    ∀ {i j} (f : J.Hom i j) (w : W ʻ j) → ψ j w C.∘ F.₁ f ≡ ψ i (W ⟪ f ⟫ w)
    where
      module W = Functor W
      module F = Functor F

  record Weighted-cocone
    (W : Functor (J ^op) (Sets ℓw))
    (F : Functor J C)
    : Type (oc ⊔ ℓc ⊔ oj ⊔ ℓj ⊔ ℓw)
    where
    no-eta-equality
    field
      coapex : C.Ob
      ψ : ∀ j → W ʻ j → C.Hom (F · j) coapex
      commutes : is-weighted-cocone W F ψ

  record is-weighted-colimit
    (W : Functor (J ^op) (Sets ℓw))
    (F : Functor J C)
    (colim : C.Ob)
    (ι : ∀ (j : J.Ob) → W ʻ j → C.Hom (F · j) colim)
    : Type (oc ⊔ ℓc ⊔ oj ⊔ ℓj ⊔ ℓw) where
    no-eta-equality
    private
      module W = Functor W
      module F = Functor F
    field
      commutes : is-weighted-cocone W F ι
```

- $\iota$ is the *universal* such diagram: for any other
  natural diagram $\psi : (j : \cJ) \to W(j) \to \cC(F(j), x)$,
  there exists a unique map $[ \psi ] : \cC(\colim_{W} F, x)$
  satisfying $[ \psi ] \circ \iota_{j,w} = \psi_{j,w}$ for all
  $j : \cJ$ and $w : W(j)$.

```agda
      universal
        : ∀ {x}
        → (ψ : ∀ (j : J.Ob) → W ʻ j → C.Hom (F · j) x)
        → is-weighted-cocone W F ψ
        → C.Hom colim x
      factors
        : ∀ {x}
        → (ψ : ∀ (j : J.Ob) → W ʻ j → C.Hom (F · j) x)
        → (p : is-weighted-cocone W F ψ)
        → ∀ j w → universal ψ p C.∘ ι j w ≡ ψ j w
      unique
        : ∀ {x}
        → (ψ : ∀ (j : J.Ob) → W ʻ j → C.Hom (F · j) x)
        → (p : is-weighted-cocone W F ψ)
        → (other : C.Hom colim x)
        → (∀ j w → other C.∘ ι j w ≡ ψ j w)
        → universal ψ p ≡ other
```

<!--
```agda
    abstract
      universal-η
        : ∀ {x}
        → (u : C.Hom colim x)
        → u ≡ universal (λ j w → u C.∘ ι j w) (λ f w → C.pullr (commutes f w))
      universal-η u = sym $ unique _ _ u λ _ _ → refl

      universal-∘
        : ∀ {x y}
        → (f : C.Hom x y)
        → (ψ : ∀ j → W ʻ j → C.Hom (F · j) x)
        → (p : is-weighted-cocone W F λ j w → f C.∘ ψ j w)
        → (q : is-weighted-cocone W F ψ)
        → universal (λ j w → f C.∘ ψ j w) p ≡ f C.∘ universal ψ q
      universal-∘ f ψ p q = unique _ _ _ λ j w → C.pullr (factors _ _ j w)

      unique₂
          : ∀ {x}
          → (u v : C.Hom colim x)
          → (∀ j w → u C.∘ ι j w ≡ v C.∘ ι j w)
          → u ≡ v
      unique₂ u v p =
        u                                 ≡⟨ universal-η u ⟩
        universal (λ j w → u C.∘ ι j w) _ ≡⟨ ap₂ universal (ext p) prop! ⟩
        universal (λ j w → v C.∘ ι j w) _ ≡˘⟨ universal-η v ⟩
        v                                 ∎

      unique-id
        : (u : C.Hom colim colim)
        → (∀ j w → u C.∘ ι j w ≡ ι j w)
        → u ≡ C.id
      unique-id u p = unique₂ u C.id λ j w → p j w ∙ C.introl refl
```
-->

A **$W$-weighted colimit** is the data of an $W$-weighted colimit
diagram $\iota : (j : \cJ) \to W(j) \to \cC(F(j), \colim_{W} F)$.

```agda
  record Weighted-colimit
    (W : Functor (J ^op) (Sets ℓw))
    (F : Functor J C)
    : Type (oc ⊔ ℓc ⊔ oj ⊔ ℓj ⊔ ℓw) where
    no-eta-equality
    field
      colim : C.Ob
      ι : (j : J.Ob) (w : W ʻ j) → C.Hom (F · j) colim
      has-is-weighted-colimit : is-weighted-colimit W F colim ι

    open is-weighted-colimit has-is-weighted-colimit public
```
:::

<!--
```agda
{-# INLINE is-weighted-colimit.constructor #-}
{-# INLINE Weighted-colimit.constructor #-}

module _
  {oc ℓc oj ℓj ℓw}
  {J : Precategory oj ℓj} {C : Precategory oc ℓc}
  {W : Functor (J ^op) (Sets ℓw)} {F : Functor J C}
  where
  private
    module C = Cat.Reasoning C
    module J = Precategory J
    module F = Functor F

    variable
      colim : C.Ob
      ι : ∀ (j : J.Ob) → W ʻ j → C.Hom (F · j) colim

  is-weighted-colimit-is-prop
    : is-prop (is-weighted-colimit W F colim ι)
  is-weighted-colimit-is-prop {colim = colim} {ι = ι} is-colim is-colim' =
    mk-path (ext λ ψ p → is-colim .unique _ _ _ (is-colim' .factors _ _))
    where
      unquoteDecl mk-path = declare-record-path mk-path (quote is-weighted-colimit)
      open is-weighted-colimit

  instance
    H-Level-is-weighted-colimit
      : ∀ {n} → H-Level (is-weighted-colimit W F colim ι) (suc n)
    H-Level-is-weighted-colimit = prop-instance is-weighted-colimit-is-prop

  private unquoteDecl weighted-colimit-Σ-iso = declare-record-iso weighted-colimit-Σ-iso (quote Weighted-colimit)

  Weighted-colimit≃is-weighted-colimit
    : Weighted-colimit W F
    ≃ (Σ[ colim ∈ C.Ob ] Σ[ ι ∈ (∀ j → W ʻ j → C.Hom (F · j) colim) ] is-weighted-colimit W F colim ι)
  Weighted-colimit≃is-weighted-colimit = Iso→Equiv weighted-colimit-Σ-iso

  instance
    Extensional-Weighted-colimit
      : ∀ {ℓr}
      → ⦃ _ : Extensional (Σ[ colim ∈ C.Ob ] (∀ j → W ʻ j → C.Hom (F · j) colim)) ℓr ⦄
      → Extensional (Weighted-colimit W F) ℓr
    Extensional-Weighted-colimit ⦃ e ⦄ =
      embedding→extensional
        (Equiv→Embedding (Weighted-colimit≃is-weighted-colimit ∙e Σ-assoc)
         ∙emb (fst , Subset-proj-embedding λ _ → hlevel 1))
        e

-- New section to clear out our variable block
module _
  {oc ℓc oj ℓj ℓw}
  {J : Precategory oj ℓj} {C : Precategory oc ℓc}
  {W : Functor (J ^op) (Sets ℓw)} {F : Functor J C}
  where
  private
    module C = Cat.Reasoning C
    module J = Precategory J
    module F = Functor F

  -- Flattened version of Weighted-colimit that is intended to be used
  -- with 'record where'.
  record Make-weighted-colimit : Type (ℓw ⊔ oj ⊔ ℓj ⊔ oc ⊔ ℓc) where
    field
      colim : C.Ob
      ι : (j : J.Ob) (w : W ʻ j) → C.Hom (F · j) colim
      commutes : is-weighted-cocone W F ι
      universal
        : ∀ {x}
        → (ψ : ∀ (j : J.Ob) → W ʻ j → C.Hom (F · j) x)
        → is-weighted-cocone W F ψ
        → C.Hom colim x
      factors
        : ∀ {x}
        → (ψ : ∀ (j : J.Ob) → W ʻ j → C.Hom (F · j) x)
        → (p : is-weighted-cocone W F ψ)
        → ∀ j w → universal ψ p C.∘ ι j w ≡ ψ j w
      unique
        : ∀ {x}
        → (ψ : ∀ (j : J.Ob) → W ʻ j → C.Hom (F · j) x)
        → (p : is-weighted-cocone W F ψ)
        → (other : C.Hom colim x)
        → (∀ j w → other C.∘ ι j w ≡ ψ j w)
        → universal ψ p ≡ other

  make-weighted-colimit
    : Make-weighted-colimit
    → Weighted-colimit W F
  {-# INLINE make-weighted-colimit #-}
  make-weighted-colimit mk = record
    { colim = colim
    ; ι = ι
    ; has-is-weighted-colimit = record
      { commutes = commutes
      ; universal = universal
      ; factors = factors
      ; unique = unique
      }
    }
    where open Make-weighted-colimit mk
```
-->

## Intuition

Like most categorical notions, there are many perspectives we can view
weighted colimits from. We will explore a couple of these, in increasing
order of sophistication.

### Weighted colimits as weighted sums

<!--
```agda
module _ {oc ℓc} {C : Precategory oc ℓc} where
  private
    module C = Cat.Reasoning C
```
-->

Perhaps the simplest intuition for weighted colimits is that they
are a categorification of *weighted sums*, EG: sums of the form

$$
\sum_{a \in A} w(a) * f(a)
$$

where both $f$ and $w$ are functions taking values in some (semi)ring
$R$. These are clearly equivalent to non-weighted sums: every sum
$\sum_{a : A} f(a)$ can be trivially considered a sum weighted by
$w(a) = 1$, and likewise every weighted sum can be computed as a
non-weighted sum.

However, distinguishing the weights makes algebraic manipulations of
such sums notably easier, and also provides some clarifying power, as
noted by the following examples:

- Every univariate polynomial $f : R[X]$ can be expressed as a weighted
  sum

  $$
  f(x) = \sum_{i=0}^{\deg(f)}a_n x^n
  $$

  where the weights $a_n$ are the coefficients of $f$. This lets us
  manipulate polynomials by *only* manipulating the weights.

- The weighted cardinality of a finite type $A$ is defined as the
  weighted sum

  $$\sum_{a : A} w(a) * 1$$

  where $w : A \to \NN$. This notion is useful for combinatorial problems
  that require tracking extra data (e.g. the number of leaves in a tree
  with $n$ vertices).

- The dot/inner product of two vectors $u, v : V$ in an $n$-dimensional
  vector space is given by the weighted sum[^1]

  $$\langle u , v \rangle := \sum_{i=0}^{n} u_i * v_i$$

[^1]: This example is particularly suggestive: every bilinear map
  $\langle - , - \rangle : V \times V \to V$ gives rise to a map
  $\langle u, - \rangle : V \to V^{*}$ into the dual space of $V$.
  In other words, this weighted sum treats the weight $u$ as if it were a
  *covector* rather than a vector, which provides some intuition
  as to why the domains of $W$ and $F$ have different variances.

<!--
```agda
  module _
    {oj ℓj ℓw} {J : Precategory oj ℓj}
    {W : Functor (J ^op) (Sets ℓw)} {F : Functor J C}
    (J-disc : is-univalent-groupoid J)
    where
    private
      module F = Cat.Functor.Reasoning F
      module W = Cat.Functor.Reasoning.Presheaf W
```
-->

To make this analogy precise, let $\cJ$ be a [[univalent groupoid]],
$W : \cJ^\op \to \Sets$ and $F : \cJ \to \cC$ be a pair of functors, and

$$
\psi : (j : \cJ) \to W(j) \to \cC(F(j), \sum_{j : \cJ} W(j) \otimes F(j))
$$

be a family of maps into a coproduct over the [[copower]] of $W(j)$ with
$F(j)$ that factors through the coproduct inclusions, as in the following
diagram:

~~~{.quiver}
\begin{tikzcd}
  {F(j)} && \\
  \\
  {W(j) \otimes F(j)} && {\sum_{j : \mathcal{J}} W(j) \otimes F(j)}
  \arrow["{\iota_{j,w}}"', from=1-1, to=3-1]
  \arrow["{\psi_{j,w}}", from=1-1, to=3-3]
  \arrow["{\iota_{j}}"', from=3-1, to=3-3]
\end{tikzcd}
~~~

We shall now prove that $\psi$ is a colimiting cocone of $F$ weighted
by $W$.

```agda
    is-indexed-coproducts→is-groupoid-weighted-colimit
      : ∀ {copow : ⌞ J ⌟ → C.Ob} {colim : C.Ob}
      → {ψ : ∀ j → W ʻ j → C.Hom (F.₀ j) colim}
      → (ι-⊗ : ∀ j → W ʻ j → C.Hom (F.₀ j) (copow j))
      → (ι-∐ : ∀ j → C.Hom (copow j) colim)
      → (∀ j → (w : W ʻ j) → ψ j w ≡ ι-∐ j C.∘ ι-⊗ j w)
      → (∀ j → is-indexed-coproduct C (λ _ → F.₀ j) (ι-⊗ j))
      → is-indexed-coproduct C copow ι-∐
      → is-weighted-colimit W F colim ψ
```

We must first show that $\psi_{i, w} \circ F(f) = \psi_{i, W(f)(w)}$ for
all $f : \cJ(i, j)$. Luckily, this is straightforward: $\cJ$ is a univalent
groupoid, so by identity system induction it suffices to prove that $\psi_{i, w} \circ F(\id) = \psi_{i, W(\id)(w)}$,
which follows from some easy algebra.

```agda
    {-# INLINE is-indexed-coproducts→is-groupoid-weighted-colimit #-}
    is-indexed-coproducts→is-groupoid-weighted-colimit {ψ = ψ} ι-⊗ ι-∐ ψ-factor is-copower is-coprod = record where
      module ⊗ j = is-indexed-coproduct (is-copower j)
      module ∐ = is-indexed-coproduct is-coprod

      commutes {i} {j} f w =
        IdsJ J-disc (λ j p → ∀ (w : W ʻ j) → ψ j w C.∘ F.₁ p ≡ ψ i (W ⟪ p ⟫ w))
          (λ w → F.elimr refl ∙ ap (ψ i) (sym (W.F-id)))
          f w
```

Next, let $\xi : (j : \cJ) \to W(j) \to \cC(F(j), X)$ be another cocone
weighted by $W$; our goal is to construct a universal map $\cC(\sum_{j : \cJ} W(j) \otimes F(j), X)$.
To that end, let $[ w.\ \psi_{j, w} ] : \cC(W(j) \otimes F(j), X)$ be the
$\cJ$-indexed family of universal maps out of each of the copowers. We can then gather these
together into a single map $[ j\. [ w\. \psi_{j,w} ] ] : \cC(\sum_{j : \cJ} W(j) \otimes F(j), X)$
out of their sum. Moreover, this map commutes with our inclusions, completing
the proof.

```agda
      universal ξ ξ-nat = ∐.match (λ j → ⊗.match j (ξ j))
      factors ξ ξ-nat j w =
        ∐.match (λ j → ⊗.match j (ξ j)) C.∘ ψ j w             ≡⟨ C.cdr (ψ-factor j w) ⟩
        ∐.match (λ j → ⊗.match j (ξ j)) C.∘ ι-∐ j C.∘ ι-⊗ j w ≡⟨ C.pulll ∐.commute ⟩
        ⊗.match j (ξ j) C.∘ ι-⊗ j w                           ≡⟨ ⊗.commute j ⟩
        ξ j w                                                 ∎
      unique ξ ξ-nat u p = ∐.unique _ λ j → sym $ ⊗.unique j (ξ j) λ w →
        (u C.∘ ι-∐ j) C.∘ ι-⊗ j w ≡⟨ C.pullr (sym (ψ-factor j w)) ⟩
        u C.∘ ψ j w               ≡⟨ p j w ⟩
        ξ j w                     ∎
```

<!--
```agda
    indexed-coproducts→discrete-weighted-colimit
      : (∀ j → has-coproducts-indexed-by C (W ʻ j))
      → has-coproducts-indexed-by C ⌞ J ⌟
      → Weighted-colimit W F
    {-# INLINE indexed-coproducts→discrete-weighted-colimit #-}
    indexed-coproducts→discrete-weighted-colimit Wj-coprods J-coprods = record where
      module Wj⊗Fj j = Indexed-coproduct (Wj-coprods j λ _ → F.₀ j)
      module ∐Wj⊗Fj = Indexed-coproduct (J-coprods λ j → Wj⊗Fj.ΣF j)

      colim = ∐Wj⊗Fj.ΣF
      ι j w = ∐Wj⊗Fj.ι j C.∘ Wj⊗Fj.ι j w
      has-is-weighted-colimit =
        is-indexed-coproducts→is-groupoid-weighted-colimit
          Wj⊗Fj.ι ∐Wj⊗Fj.ι (λ _ _ → refl)
          Wj⊗Fj.has-is-ic
          ∐Wj⊗Fj.has-is-ic
```
-->

As a corollary, we get that copowers $W \otimes X$ are colimits of
the constant diagram $\Delta_{X} : \top \to \cC$ weighted by the
constant presheaf $\Delta_{W} : \top\op \to \Sets$.

```agda
  is-copower→is-weighted-colimit
    : ∀ {κ} {W : Functor (⊤Cat ^op) (Sets κ)} {F : Functor ⊤Cat C}
    → {colim : C.Ob} {ι : ⊤ → W ʻ tt → C.Hom (F · tt) colim}
    → is-indexed-coproduct C (λ _ → F · tt) (ι tt)
    → is-weighted-colimit {C = C} W F colim ι
  {-# INLINE is-copower→is-weighted-colimit #-}
  is-copower→is-weighted-colimit {ι = ι} is-copow =
    is-indexed-coproducts→is-groupoid-weighted-colimit
      ⊤Cat-is-univalent-groupoid
      ι (λ _ → C.id) (λ _ _ → C.introl refl)
      (λ _ → is-copow)
      (is-contr-indexed-coproduct C (hlevel 0))
```

## Weighted colimits are weighted integrals

In the previous section, we saw how weighted colimits over suitably
discrete indexing categories can be viewed as weighted sums. That
raises the natural question: how can we generalise this perspective
to non-discrete categories?

As it turns out, weighted colimits indexed by general category $\cJ$
behave like **weighted Lebesgue integrals**; i.e. integrals of the form

$$
\int_{\Omega} f(x) d\mu
$$

where $\Omega$ is a measurable set and $\mu$ is a measure[^density].
More concisely: a Lebesgue integral is a sum weighted by measures
of sets; a weighted colimit is a colimit weighted by sets!

[^density]: This is why theorems relating to weighted colimits
  are often called *density* theorems: the weight function in
  such an integral can be thought of as assigning a density to
  each measurable set of a volume.

We can make this vague intuition a bit more precise by proving that
all weighted colimits can be computed as [[coends]] of [[copowers]]
via the following formula:

$$
\colim_{W} F = \int^{j : \cJ} W(j) \otimes F(j)
$$

<!--
```agda
module _
  {oj ℓj oc ℓc ℓw} {J : Precategory oj ℓj} {C : Precategory oc ℓc}
  (W : Functor (J ^op) (Sets ℓw)) (F : Functor J C)
  where
  private
    module J = Precategory J
    module C = Cat.Reasoning C
    module F = Cat.Functor.Reasoning F
    module W = Cat.Functor.Reasoning.Presheaf W
    open Cowedge
```
-->

Unfortunately, even stating this formally requires some non-trivial setup.
To that end, suppose that $\cC$ has all copowers of the form $W(i) \otimes F(j)$ for $i, j : \cJ$.
We can then assemble these copowers into a bifunctor $W(-) \otimes F(=) : \cJ\op \times \cJ \to \cC$.

```agda
  module _ (copowers : ∀ i j → Indexed-coproduct C {Idx = W ʻ i} λ _ → F · j) where
    module _ (i j : J.Ob) where
      open Indexed-coproduct (copowers i j)
        renaming (ΣF to W[_]⊗F[_])
        using ()
        public
    module W⊗F {i j : J.Ob} where
      open Indexed-coproduct (copowers i j)
        hiding (ΣF)
        public

    Tensor : Bifunctor (J ^op) J C
    Tensor = make-bifunctor record where
      F₀ i j = W[ i ]⊗F[ j ]
      lmap f = W⊗F.match λ w → W⊗F.ι (W ⟪ f ⟫ w)
      rmap f = W⊗F.match λ w → W⊗F.ι w C.∘ F.₁ f
```

<details>
<summary>Proving that this is functorial is a tedious exercise in
commuting copowers around, so we elide the details.
</summary>

```agda
      lmap-id = W⊗F.unique-id _ λ w → W⊗F.commute ∙ ap W⊗F.ι W.F-id
      rmap-id  = W⊗F.unique-id _ λ w → W⊗F.commute ∙ F.elimr refl
      lmap-∘ f g = W⊗F.unique _ λ w →
        (W⊗F.match (W⊗F.ι ⊙ W.F₁ f) C.∘ W⊗F.match (W⊗F.ι ⊙ W.F₁ g)) C.∘ W⊗F.ι w ≡⟨ C.pullr W⊗F.commute ⟩
        W⊗F.match (W⊗F.ι ⊙ W.F₁ f) C.∘ W⊗F.ι (W.F₁ g w)                         ≡⟨ W⊗F.commute ⟩
        W⊗F.ι (W ⟪ f ⟫ (W ⟪ g ⟫ w))                                             ≡˘⟨ ap W⊗F.ι (W.F-∘ f g) ⟩
        W⊗F.ι (W ⟪ g J.∘ f ⟫ w)                                                 ∎
      rmap-∘ f g = W⊗F.unique _ λ w →
        (W⊗F.match (λ w → W⊗F.ι w C.∘ F.F₁ f) C.∘ W⊗F.match (λ w → W⊗F.ι w C.∘ F.F₁ g)) C.∘ W⊗F.ι w ≡⟨ C.pullr W⊗F.commute ⟩
        W⊗F.match (λ w → W⊗F.ι w C.∘ F.F₁ f) C.∘ W⊗F.ι w C.∘ F.F₁ g                                 ≡⟨ C.pulll W⊗F.commute ⟩
        (W⊗F.ι w C.∘ F.F₁ f) C.∘ F.F₁ g                                                             ≡⟨ F.pullr refl ⟩
        W⊗F.ι w C.∘ F.F₁ (f J.∘ g)                                                                  ∎
      lrmap f g = W⊗F.unique₂ λ w →
        (W⊗F.match (λ w → W⊗F.ι (W.F₁ f w)) C.∘ W⊗F.match (λ w → W⊗F.ι w C.∘ F.F₁ g)) C.∘ W⊗F.ι w   ≡⟨ C.pullr W⊗F.commute ⟩
        W⊗F.match (λ w → W⊗F.ι (W.F₁ f w)) C.∘ W⊗F.ι w C.∘ F.F₁ g                                   ≡⟨ C.pulll W⊗F.commute ⟩
        W⊗F.ι (W.F₁ f w) C.∘ F.F₁ g                                                                 ≡˘⟨ W⊗F.commute ⟩
        (W⊗F.match (λ w → W⊗F.ι w C.∘ F.F₁ g) C.∘ W⊗F.ι (W.F₁ f w))                                 ≡˘⟨ C.pullr W⊗F.commute ⟩
        ((W⊗F.match (λ w → W⊗F.ι w C.∘ F.F₁ g) C.∘ W⊗F.match (λ w → W⊗F.ι (W.F₁ f w))) C.∘ W⊗F.ι w) ∎
```
</details>

Next, note that each $W$-weighted cocone $\xi_{j} : W(j) \to \cC(F(j), x)$ under $F$ gives rise to a
[[cowedge]] $[ \xi_j ] : \cC(W(j) \otimes F(j), x)$ under $W(-) \otimes F(=)$.

```agda
    cocone→tensor-cowedge
      : ∀ {x} (ξ : ∀ j → W ʻ j → C.Hom (F · j) x)
      → is-weighted-cocone W F ξ
      → Cowedge Tensor
    cocone→tensor-cowedge {x} ξ ξ-cocone .nadir = x
    cocone→tensor-cowedge {x} ξ ξ-cocone .ψ j = W⊗F.match (ξ j)
```

<details>
<summary>Extranaturality is another exercise in copower manipulation.
</summary>

```agda
    cocone→tensor-cowedge {x} ξ ξ-cocone .extranatural {i} {j} f = W⊗F.unique₂ λ w →
      (W⊗F.match (ξ j) C.∘ W⊗F.match (λ w → W⊗F.ι w C.∘ F.F₁ f)) C.∘ W⊗F.ι w       ≡⟨ C.pullr W⊗F.commute ⟩
      W⊗F.match (ξ j) C.∘ W⊗F.ι w C.∘ F.F₁ f                                       ≡⟨ C.pulll W⊗F.commute ⟩
      ξ j w C.∘ F.F₁ f                                                             ≡⟨ ξ-cocone f w ⟩
      ξ i (W.F₁ f w)                                                               ≡˘⟨ W⊗F.commute ⟩
      W⊗F.match (ξ i) C.∘ W⊗F.ι (W.F₁ f w)                                         ≡˘⟨ C.pullr W⊗F.commute ⟩
      (W⊗F.match (λ w → ξ i w) C.∘ W⊗F.match (λ w → W⊗F.ι (W.F₁ f w))) C.∘ W⊗F.ι w ∎
```

</details>

Now, suppose that we have a coend $\int^{j} W(j) \otimes F(j)$; i.e. a universal
cowedge $\psi_{j} : \cC(W(j) \otimes F(j), int^{j} W(j) \otimes F(j))$. If we precompose
$\psi_{j}$ with the inclusion $\iota_{j, w} : \cC(F(j), W(j) \otimes F(j))$, then we get
a $W$-weighted cocone of $F$.

```agda
    coends+coequalisers→weighted-colimits
      : Coend Tensor
      → Weighted-colimit W F
    {-# INLINE coends+coequalisers→weighted-colimits #-}
    coends+coequalisers→weighted-colimits ∫W⊗F = make-weighted-colimit record where
      module ∫W⊗F = Coend ∫W⊗F

      colim = ∫W⊗F.nadir
      ι j w = ∫W⊗F.ψ j C.∘ W⊗F.ι w
      commutes {i} {j} f w =
        (∫W⊗F.ψ j C.∘ W⊗F.ι w) C.∘ F.₁ f                                ≡⟨ C.extendr (sym W⊗F.commute) ⟩
        (∫W⊗F.ψ j C.∘ W⊗F.match (λ w → W⊗F.ι w C.∘ F.F₁ f)) C.∘ W⊗F.ι w ≡⟨ C.car (∫W⊗F.extranatural f) ⟩
        (∫W⊗F.ψ i C.∘ W⊗F.match (λ w → W⊗F.ι (W.F₁ f w))) C.∘ W⊗F.ι w   ≡⟨ C.pullr W⊗F.commute ⟩
        ∫W⊗F.ψ i C.∘ W⊗F.ι (W.F₁ f w) ∎
```

Moreover, $\psi$ is universal, and every $W$-weighted cocone of $F$ gives rise to
a cowedge, so the weighted cocone we just constructed is also universal.

```agda
      universal ξ ξ-cocone = ∫W⊗F.factor (cocone→tensor-cowedge ξ ξ-cocone)
      factors ξ ξ-cocone j w =
        ∫W⊗F.factor (cocone→tensor-cowedge ξ ξ-cocone) C.∘ ∫W⊗F.ψ j C.∘ W⊗F.ι w ≡⟨ C.pulll ∫W⊗F.commutes ⟩
        W⊗F.match (ξ j) C.∘ W⊗F.ι w                                      ≡⟨ W⊗F.commute ⟩
        ξ j w                                                            ∎
      unique ξ ξ-cocone u p = ∫W⊗F.unique λ {j} → sym $ W⊗F.unique (ξ j) λ w →
        C.reassocl.from (p j w)
```

To put an even finer point on our analogy, coends over some bifunctor
$F : \cC\op \times \cC \to \cD$ are colimits of $F$ weighted by the
[[hom functor]][^delta].

[^delta]: In the language of sums, this essentially the identity

  $$
  \sum_{i, j} f(i,j) = \sum_{i} \sum_{j} f(i,j) \delta^{i}_{j}
  $$

  where $\delta^{i}$ is the Kronecker delta function.

<!--
```agda
module _
  {oc ℓc od ℓd}
  {C : Precategory oc ℓc} {D : Precategory od ℓd}
  (F : Bifunctor (C ^op) C D)
  where
  private
    module C = Cat.Reasoning C
    module D = Cat.Reasoning D
    module F = Bifunctor F
    open Cowedge
```
-->

To that end, let $F : \cC\op \times \cC \to \cD$ be a bifunctor, and
$\psi_{c, c'} : \cC(c, c') \to \cD(F(c,c'), d)$ be cocone under $F$
weighted by $\cC(-,=) : \cC\ \times \cC\op \to \Sets$. We can
owedge under $F$ by taking the diagonal $\psi_{c, c}(\id) : \cD(F(c,c), d)$.

::: note
Unfortunately, proof assistants: weighted colimits require the weights
to be a presheaf, which in our case means a functor $(\cC\op \times \cC)\op \to \Sets$.
However, we've defined the hom functor on $\cC$ as a [[bifunctor]]
$\cC(-,=) : \cC\op \to \cC \to \Sets$, so to get something that matches our
desired type signature we need to uncurry the hom functor on $\cC\op$, and
then precompose with the equivalence between $(\cC\op\op \times \cC\op)$
and $(\cC \op \times \cC)\op$.
:::


```agda
    private
      C[-,-] : Functor ((C ^op ×ᶜ C) ^op) (Sets ℓc)
      C[-,-] = Uncurry (Hom[-,-] (C ^op)) F∘ ×^op→

    cocone→hom-cowedge
      : ∀ {d}
      → (ψ : ((c , c') : C.Ob × C.Ob) → C.Hom c' c → D.Hom (F · c · c') d)
      → is-weighted-cocone C[-,-] (Uncurry F) ψ
      → Cowedge F
    cocone→hom-cowedge {d} ψ ψ-cocone .Cowedge.nadir = d
    cocone→hom-cowedge {d} ψ ψ-cocone .Cowedge.ψ c = ψ (c , c) C.id
    cocone→hom-cowedge {d} ψ ψ-cocone .Cowedge.extranatural {c} {c'} f =
      ψ (c' , c') C.id D.∘ (c' F.▶ f)                   ≡⟨ D.cdr (F.◀.introl refl) ⟩
      ψ (c' , c') C.id D.∘ (C.id F.◀ c') D.∘ (c' F.▶ f) ≡⟨ ψ-cocone (C.id , f) C.id ⟩
      ψ (c' , c) (C.id C.∘ C.id C.∘ f)                  ≡⟨ ap (ψ (c' , c)) (C.cancell C.id2 ∙ C.intror C.id2) ⟩
      ψ (c' , c) (f C.∘ C.id C.∘ C.id)                  ≡˘⟨ ψ-cocone (f , C.id) C.id ⟩
      ψ (c , c) C.id D.∘ (f F.◀ c) D.∘ (c' F.▶ C.id)    ≡⟨ D.cdr (F.▶.elimr refl) ⟩
      ψ (c , c) C.id D.∘ (f F.◀ c)                      ∎
```

We can also convert any cowedge $\psi_{c} : \cD(F(c,c), d)$ under $F$
to a weighted cocone by precomposing with either the left or right
action of $F$; we will choose the left.

```agda
    abstract
      hom-cowedge→cocone
        : (W : Cowedge F)
        → is-weighted-cocone C[-,-] (Uncurry F)
            (λ (c , c') f → W .ψ c' D.∘ (f F.◀ c'))
      hom-cowedge→cocone W {c1 , c1'} {c2 , c2'} (f1 , f2) g =
        (W .ψ c2' D.∘ (g F.◀ c2')) D.∘ (f1 F.◀ c2') D.∘ (c1 F.▶ f2) ≡⟨ D.extendl (F.◀.pullr refl) ⟩
        W .ψ c2' D.∘ (f1 C.∘ g F.◀ c2') D.∘ (c1 F.▶ f2)             ≡⟨ D.pulll (sym (W .extranatural (f1 C.∘ g))) ⟩
        (W .ψ c1 D.∘ (c1 F.▶ f1 C.∘ g)) D.∘ (c1 F.▶ f2)             ≡⟨ F.▶.pullr (sym (C.assoc _ _ _)) ⟩
        W .ψ c1 D.∘ (c1 F.▶ f1 C.∘ g C.∘ f2)                        ≡⟨ W .extranatural (f1 C.∘ g C.∘ f2) ⟩
        W .ψ c1' D.∘ (f1 C.∘ g C.∘ f2 F.◀ c1')                      ∎
```

Now, suppose that $\int^c F(c,c)$ is a coend of $F$. By our previous result,
the the universal cowedge $\psi$ associated to $\int^c F(c,c)$ forms
a cocone under $F$ weighted by $\cC(-,=)$.

```agda
    coend→weighted-colimit
      : Coend F
      → Weighted-colimit C[-,-] (Uncurry F)
    {-# INLINE coend→weighted-colimit #-}
    coend→weighted-colimit coend = make-weighted-colimit record where
      module coend = Coend coend

      colim = coend.nadir
      ι (c , c') f = coend.ψ c' D.∘ (f F.◀ c')
      commutes = hom-cowedge→cocone coend.cowedge
```

Moreover, this cocone is universal: any other such cocone
$\xi_{c,c'} : \cC(c,c') \to \cD(F(c,c'), d)$ gives rise to a cowedge $\xi_{c,c}$,
which induces a unique map $[ \xi_{c,c} ] : \cD(\int^{c} F(c,c), d)$.

```agda
      universal ξ ξ-cocone = coend.factor (cocone→hom-cowedge ξ ξ-cocone)
      factors ξ ξ-cocone (c , c') f =
        coend.factor (cocone→hom-cowedge ξ ξ-cocone) D.∘ coend.ψ c' D.∘ (f F.◀ c') ≡⟨ D.pulll coend.commutes ⟩
        ξ (c' , c') C.id D.∘ (f F.◀ c')                                            ≡⟨ D.cdr (F.▶.intror refl) ⟩
        ξ (c' , c') C.id D.∘ (f F.◀ c') D.∘ (c F.▶ C.id)                           ≡⟨ ξ-cocone (f , C.id) C.id ⟩
        ξ (c , c') (f C.∘ C.id C.∘ C.id)                                           ≡⟨ ap (ξ (c , c')) (C.elimr C.id2) ⟩
        ξ (c , c') f                                                               ∎
      unique ξ ξ-cocone u p = coend.unique λ {c} →
        u D.∘ coend.ψ c                  ≡⟨ D.cdr (F.◀.intror refl) ⟩
        u D.∘ coend.ψ c D.∘ (C.id F.◀ c) ≡⟨ p (c , c) C.id ⟩
        ξ (c , c) C.id                   ∎
```

The reverse direction follows a similar pattern: if we have a universal
$\cC(-,=)$-weighted cocone under $F$, then we can convert it to a universal
cowedge by taking the diagonal.

```agda
    weighted-colimit→coend
      : Weighted-colimit C[-,-] (Uncurry F)
      → Coend F
    weighted-colimit→coend colim = record where
      module colim = Weighted-colimit colim

      cowedge = cocone→hom-cowedge colim.ι colim.commutes
      factor W = colim.universal (λ _ f → W .ψ _ D.∘ (f F.◀ _)) (hom-cowedge→cocone W)
      commutes {W} {c} =
        colim.universal (λ _ f → ψ W _ D.∘ (f F.◀ _)) _ D.∘ colim.ι (c , c) C.id ≡⟨ colim.factors _ _ _ _ ⟩
        ψ W c D.∘ (C.id F.◀ c)                                                   ≡⟨ F.◀.elimr refl ⟩
        ψ W c                                                                    ∎
      unique {W} {u} p = colim.unique _ _ _ λ (c , c') f →
        u D.∘ colim.ι (c , c') f                                       ≡⟨ D.cdr (ap (colim.ι (c , c')) (C.intror C.id2)) ⟩
        u D.∘ colim.ι (c , c') (f C.∘ C.id C.∘ C.id)                   ≡⟨ D.pushr (sym $ colim.commutes _ _) ⟩
        (u D.∘ colim.ι (c' , c') C.id) D.∘ (f F.◀ c') D.∘ (_ F.▶ C.id) ≡⟨ D.car p ⟩
        ψ W c' D.∘ (f F.◀ c') D.∘ (_ F.▶ C.id)                         ≡⟨ D.cdr (F.▶.elimr refl) ⟩
        ψ W c' D.∘ (f F.◀ c')                                          ∎
```

## Weighted colimits are colimits of generalized cocones

We can also approach weighted colimits from a purely categorical angle,
and view them as colimits of $W$-*generalized elements* of a cocone under
$F$.

<!--
```agda
module _
  {oj ℓj oc ℓc} {J : Precategory oj ℓj} {C : Precategory oc ℓc}
  (W : Functor (J ^op) (Sets ℓc)) (F : Functor J C)
  where
  private
    module J = Precategory J
    module C = Cat.Reasoning C
    module F = Cat.Functor.Reasoning F
    module W = Cat.Functor.Reasoning.Presheaf W
    open Weighted-cocone
    open Cocone
    open _=>_
```
-->

To make sense of this statement, note that the data of a non-weighted [[cocone]]
under $F$ can be given as a natural transformation $\psi : \top \Rightarrow \cC(x,F(-))$
from a [[terminal]] presheaf[^terminal], which is precisely a global element of
$\cC(x,F(-))$ in the presheaf category $\cJ\op \to \Sets$.

[^terminal]: Recall that a presheaf is a terminal object precisely
  when all of its sections are [[contractible]].

```agda
  nat-trans→cocone
    : ∀ {coapex}
    → (∀ j → is-contr (W ʻ j))
    → (ψ : W => Hom-from (C ^op) coapex F∘ F.op)
    → Cocone F
  nat-trans→cocone {coapex} W-contr ψ .coapex = coapex
  nat-trans→cocone {coapex} W-contr ψ .ψ j = ψ .η j (W-contr j .centre)
  nat-trans→cocone {coapex} W-contr ψ .commutes {i} {j} f =
    ψ .η j (W-contr j .centre) C.∘ F.₁ f ≡˘⟨ ψ .is-natural j i f ·ₚ W-contr j .centre ⟩
    ψ .η i (W ⟪ f ⟫ W-contr j .centre)   ≡˘⟨ ap (ψ .η i) (W-contr i .paths _) ⟩
    ψ .η i (W-contr i .centre)           ∎
```

If we pass to generalized elements of $\cC(x,F(-))$, then we obtain
weighted cocones[^enriched]!

[^enriched]: This makes weighted colimits inevitable in settings like
  enriched category theory, as our enriching category may have very
  few global sections.

```agda
  nat-trans→weighted-cocone
    : ∀ {coapex}
    → (ψ : W => Hom-from (C ^op) coapex F∘ F.op)
    → Weighted-cocone W F
  nat-trans→weighted-cocone {coapex} ψ .coapex = coapex
  nat-trans→weighted-cocone {coapex} ψ .ψ j = ψ .η j
  nat-trans→weighted-cocone {coapex} ψ .commutes {i} {j} f w = sym $ ψ .is-natural j i f ·ₚ w
```

<!--
```agda
module _
  {oj ℓj oc ℓc ℓw} {J : Precategory oj ℓj} {C : Precategory oc ℓc}
  (W : Functor (J ^op) (Sets ℓw)) (F : Functor J C)
  where
  private
    module J = Precategory J
    module C = Cat.Reasoning C
    module F = Cat.Functor.Reasoning F
    module W = Cat.Functor.Reasoning.Presheaf W
    open Weighted-cocone
    open Cocone
    open _=>_
    open Element-hom
```
-->


To further sharpen this point, observe that a cocone weighted by contractible
weights is contains the same data as an unweighted cocone.

```agda
  module _ (W-contr : (∀ j → is-contr (W ʻ j))) where
    private
      open module W-contr (j : J.Ob) = is-contr (W-contr j)
        renaming (centre to w*; paths to w*-path)

    abstract
      is-contr-weighted-cocone→is-cocone
        : ∀ {coapex} {ψ : ∀ j → W ʻ j → C.Hom (F · j) coapex}
        → (ψ-cocone : is-weighted-cocone W F ψ)
        → ∀ {i j} (f : J.Hom i j)
        → ψ j (w* j) C.∘ F.₁ f ≡ ψ i (w* i)
      is-contr-weighted-cocone→is-cocone {ψ = ψ} ψ-cocone {i} {j} f =
        ψ j (w* j) C.∘ F.F₁ f ≡⟨ ψ-cocone f (w* j) ⟩
        ψ i (W ⟪ f ⟫ w* j)    ≡˘⟨ ap (ψ i) (w*-path i (W ⟪ f ⟫ w* j)) ⟩
        ψ i (w* i)            ∎

    is-contr-weighted-cocone→cocone
      : ∀ {coapex}
      → (ψ : ∀ j → W ʻ j → C.Hom (F · j) coapex)
      → (ι-cocone : is-weighted-cocone W F ψ)
      → F => Const coapex
    is-contr-weighted-cocone→cocone ψ ψ-cocone .η j = ψ j (w* j)
    is-contr-weighted-cocone→cocone ψ ψ-cocone .is-natural i j f =
      ψ j (w* j) C.∘ F.F₁ f ≡⟨ is-contr-weighted-cocone→is-cocone ψ-cocone f ⟩
      ψ i (w* i)            ≡⟨ C.introl refl ⟩
      C.id C.∘ ψ i (w* i)   ∎
```

Moreover, contractibly-weighted colimits are equivalent to unweighted
colimits.

```agda
    is-contr-weighted-colimit→is-colimit
      : ∀ {colim} {ι : F => Const colim}
      → is-weighted-colimit W F colim (λ j w → ι .η j)
      → is-colimit F colim ι

    is-colimit→is-contr-weighted-colimit
      : ∀ {colim} {ι : ∀ j → W ʻ j → C.Hom (F · j) colim}
      → (ι-cocone : is-weighted-cocone W F ι)
      → is-colimit F colim (is-contr-weighted-cocone→cocone ι ι-cocone)
      → is-weighted-colimit W F colim ι
```

<details>
<summary>The proofs are unenlightening data shuffling, so we will not provide
commentary.
</summary>

```agda
    is-contr-weighted-colimit→is-colimit {colim} {ι} is-wcolim = to-is-colimitp is-colim refl where
      module colim = is-weighted-colimit is-wcolim
      open make-is-colimit

      is-colim : make-is-colimit F colim
      is-colim .ψ = ι .η
      is-colim .commutes f = ι .is-natural _ _ f ∙ C.idl _
      is-colim .universal ξ ξ-cocone = colim.universal (λ j _ → ξ j) (λ f _ → ξ-cocone f)
      is-colim .factors {j} ξ ξ-cocone = colim.factors _ _ _ (w* j)
      is-colim .unique ξ ξ-cocone u p = colim.unique _ _ _ λ j _ → p j

    {-# INLINE is-colimit→is-contr-weighted-colimit #-}
    is-colimit→is-contr-weighted-colimit {colim} {ι} ι-cocone is-colim = record where
      module colim = is-colimit is-colim
      commutes f w = ι-cocone f w
      universal ξ ξ-cocone =
        colim.universal (λ j → ξ j (w* j)) $ is-contr-weighted-cocone→is-cocone ξ-cocone
      factors ξ ξ-cocone j w =
        colim.universal (λ j → ξ j (w* j)) _ C.∘ ι j ⌜ w ⌝  ≡⟨ ap! (sym (w*-path j w)) ⟩
        colim.universal (λ j → ξ j (w* j)) _ C.∘ ι j (w* j) ≡⟨ colim.factors _ _ ⟩
        ξ j (w* j)                                          ≡⟨ ap (ξ j) (w*-path j w) ⟩
        ξ j w                                               ∎
      unique ξ ξ-cocone u p = colim.unique _ _ _ λ j → p j (w* j)
```

</details>

Conversely, every $W$-weighted colimit of $F$ is can be computed as a colimit over
the diagram $\int W \xto{\pi} \cJ \xto{F} \cC$ indexed by the [[category of
elements]] of $W$.

```agda
  is-weighted-cocone→is-elts-cocone
    : ∀ {coapex}
    → {ψ : ∀ j → W ʻ j → C.Hom (F · j) coapex}
    → is-weighted-cocone W F ψ
    → ∀ {(i , wi) (j , wj) : Element J W}
    → (f : Element-hom J W (i , wi) (j , wj))
    → ψ j wj C.∘ F.₁ (f .hom) ≡ ψ i wi

  is-weighted-cocone→elts-cocone
    : ∀ {coapex}
    → (ψ : ∀ j → W ʻ j → C.Hom (F · j) coapex)
    → is-weighted-cocone W F ψ
    → F F∘ πₚ J W => Const coapex

  is-elts-colimit→is-weighted-limit
    : ∀ {colim} {ι : ∀ j → W ʻ j → C.Hom (F · j) colim}
    → (ι-cocone : is-weighted-cocone W F ι)
    → is-colimit (F F∘ πₚ J W) colim (is-weighted-cocone→elts-cocone ι ι-cocone)
    → is-weighted-colimit W F colim ι

  is-weighted-limit→is-elts-colimit
    : ∀ {colim} {ι : F F∘ πₚ J W => Const colim}
    → is-weighted-colimit W F colim (λ j w → ι .η (j , w))
    → is-colimit (F F∘ πₚ J W) colim ι
```

<details>
<summary>This somewhat complicated-sounding statement mostly boils down
to currying and uncurrying: a cocone under $F \circ \pi$ consists of a
natural family of maps $\psi : \Sigma(j : \cJ).\ W(j) \to \cC(F(j), c)$, whereas
a weighted cocone consists of a family of maps $\psi : (j : \cJ) \to W(j) \to \cC(F(j), c)$.
</summary>

```agda
  is-weighted-cocone→elts-cocone ψ ψ-cocone .η (j , w) = ψ j w
  is-weighted-cocone→elts-cocone ψ ψ-cocone .is-natural (i , wi) (j , wj) f =
    ψ j wj C.∘ F.F₁ (f .hom) ≡⟨ is-weighted-cocone→is-elts-cocone ψ-cocone f ⟩
    ψ i wi                   ≡⟨ C.introl refl ⟩
    C.id C.∘ ψ i wi          ∎

  is-weighted-cocone→is-elts-cocone {ψ = ψ} ψ-cocone {i , wi} {j , wj} f =
    ψ j wj C.∘ F.F₁ (f .hom) ≡⟨ ψ-cocone (f .hom) wj ⟩
    ψ i (W ⟪ f .hom ⟫ wj)    ≡⟨ ap (ψ i) (f .commute) ⟩
    ψ i wi                   ∎

  is-weighted-limit→is-elts-colimit {colim} {ι} is-wcolim = to-is-colimitp is-colim refl where
    module colim = is-weighted-colimit is-wcolim
    open make-is-colimit

    is-colim : make-is-colimit (F F∘ πₚ J W) colim
    is-colim .ψ = ι .η
    is-colim .commutes f = ι .is-natural _ _ f ∙ C.idl _
    is-colim .universal ξ ξ-cocone = colim.universal (curry ξ) λ f w → ξ-cocone (elem-hom f refl)
    is-colim .factors ξ ξ-cocone = colim.factors _ _ _ _
    is-colim .unique ξ ξ-cocone u p = colim.unique _ _ _ λ j w → p (j , w)


  {-# INLINE is-elts-colimit→is-weighted-limit #-}
  is-elts-colimit→is-weighted-limit {colim} {ι} ι-cocone is-colim = record where
    module colim = is-colimit is-colim

    commutes f w = ι-cocone f w
    universal ξ ξ-cocone = colim.universal (uncurry ξ) (is-weighted-cocone→is-elts-cocone ξ-cocone)
    factors ξ ξ-cocone j w = colim.factors _ _
    unique ξ ξ-cocone u p = colim.unique _ _ _ λ (j , w) → p j w
```

</details>
