<!--
```agda
open import Algebra.Group.Ab

open import Cat.Monoidal.Instances.Cartesian
open import Cat.Functor.Naturality
open import Cat.Diagram.Coproduct
open import Cat.Diagram.Terminal
open import Cat.Diagram.Initial
open import Cat.Diagram.Product
open import Cat.Monoidal.Base
open import Cat.Diagram.Zero
open import Cat.Prelude

import Cat.Reasoning

open _=>_
```
-->

```agda
module Cat.Diagram.Biproduct where
```

<!--
```agda
module _ {o ℓ} (C : Precategory o ℓ) where
  open Cat.Reasoning C
```
-->

# Biproducts {defines="biproduct"}

Recall that, in an [[$\Ab$-enriched category]], [[products]] and
[[coproducts]] automatically coincide: these are called **biproducts**
and are written $A \oplus B$.

~~~{.quiver}
\[\begin{tikzcd}
  A & {A \oplus B} & B
  \arrow["{\iota_1}", shift left, from=1-1, to=1-2]
  \arrow["{\pi_1}", shift left, from=1-2, to=1-1]
  \arrow["{\pi_2}"', shift right, from=1-2, to=1-3]
  \arrow["{\iota_2}"', shift right, from=1-3, to=1-2]
\end{tikzcd}\]
~~~

Following [@KarvonenBiproducts], we can define what it means to be a
biproduct in a general category:
we say that a diagram like the one above is a biproduct diagram if
$(A \oplus B, \pi_1, \pi_2)$ is a product diagram, $(A \oplus B, \iota_1, \iota_2)$
is a coproduct diagram, and the following equations relating the product
projections and coproduct injections hold:

$$
\begin{align*}
\pi_1 \circ \iota_1 &\equiv \id_A \\
\pi_2 \circ \iota_2 &\equiv \id_B \\
\iota_1 \circ \pi_1 \circ \iota_2 \circ \pi_2 &\equiv \iota_2 \circ \pi_2 \circ \iota_1 \circ \pi_1
\end{align*}
$$

```agda
  record is-biproduct {A B P}
    (π₁ : Hom P A) (π₂ : Hom P B)
    (ι₁ : Hom A P) (ι₂ : Hom B P)
    : Type (o ⊔ ℓ) where
    field
      has-is-product   : is-product C π₁ π₂
      has-is-coproduct : is-coproduct C ι₁ ι₂
      πι₁ : π₁ ∘ ι₁ ≡ id
      πι₂ : π₂ ∘ ι₂ ≡ id
      ιπ-comm : ι₁ ∘ π₁ ∘ ι₂ ∘ π₂ ≡ ι₂ ∘ π₂ ∘ ι₁ ∘ π₁

  record Biproduct (A B : Ob) : Type (o ⊔ ℓ) where
    field
      biapex : Ob
      π₁ : Hom biapex A
      π₂ : Hom biapex B
      ι₁ : Hom A biapex
      ι₂ : Hom B biapex
      has-is-biproduct : is-biproduct π₁ π₂ ι₁ ι₂
```

<!--
```agda
    open is-biproduct has-is-biproduct public

    product : Product C A B
    product = record
      { apex = biapex ; π₁ = π₁ ; π₂ = π₂ ; has-is-product = has-is-product }

    coproduct : Coproduct C A B
    coproduct = record
      { coapex = biapex ; ι₁ = ι₁ ; ι₂ = ι₂ ; has-is-coproduct = has-is-coproduct }

    open Product product public
      hiding (π₁; π₂)
      renaming (unique₂ to ⟨⟩-unique₂)
    open Coproduct coproduct public
      hiding (ι₁; ι₂)
      renaming (unique₂ to []-unique₂)
```
-->

## Semiadditive categories {defines="semiadditive-category"}

Just like [[terminal objects]] (resp. [[initial objects]]) are 0-ary
products (resp. coproducts), [[zero objects]] are 0-ary biproducts.
A category with a zero object and binary biproducts (hence all finite
biproducts) is called **semiadditive**.

```agda
  record is-semiadditive : Type (o ⊔ ℓ) where
    field
      has-zero : Zero C
      has-biproducts : ∀ {A B} → Biproduct A B
```

As the name hints, every [[additive category]] is semiadditive.
However, quite surprisingly, it turns out that the structure^[Really *property*, in a univalent category.]
of a semiadditive category is already enough to define an enrichment of
$\cC$ in *commutative monoids*!

<!--
```agda
    open Zero has-zero public
    module Biprod {A B} = Biproduct (has-biproducts {A} {B})
    open Biprod using (πι₁; πι₂; ιπ-comm)

    open Binary-products C (λ _ _ → Biprod.product)
    open Binary-coproducts C (λ _ _ → Biprod.coproduct)

    open Monoidal-category (Cartesian-monoidal (λ _ _ → Biprod.product) terminal) using (associator; module ⊗)
```
-->

We define the addition of morphisms $f + g : A \to B$ by the following diagram,
where $\delta$ (resp. $\nabla$) is the diagonal map (resp. codiagonal map).

~~~{.quiver}
\[\begin{tikzcd}
  A & {A \oplus A} & {B \oplus B} & B
  \arrow["\delta", from=1-1, to=1-2]
  \arrow["{f \oplus g}", from=1-2, to=1-3]
  \arrow["\nabla", from=1-3, to=1-4]
\end{tikzcd}\]
~~~

```agda
    _+→_ : ∀ {x y} → Hom x y → Hom x y → Hom x y
    f +→ g = ∇ ∘ (f ⊗₁ g) ∘ δ
```

We start by noticing a few properties of finite biproducts. First, while
we are of course justified in writing $A \oplus B$ without ambiguity
for *objects*, we must prove that $f \times_1 g \equiv f +_1 g$ so that we
can write $f \oplus g$ without ambiguity for *morphisms*.

<details>
<summary>
To that end, we start by showing that $\pi_1 \circ \iota_2$ and
$\pi_2 \circ \iota_1$ are [[zero morphisms]].

```agda
    π₁-ι₂ : ∀ {a b} → π₁ {a} {b} ∘ ι₂ ≡ zero→
    π₂-ι₁ : ∀ {a b} → π₂ {a} {b} ∘ ι₁ ≡ zero→
```

The proofs follow [@KarvonenBiproducts] and are unenlightening.
</summary>

```agda
    π₁-ι₂ = zero-unique λ f g →
      let h = ⟨ π₁ ∘ ι₂ ∘ g , f ⟩ in
      (π₁ ∘ ι₂) ∘ f                   ≡⟨ insertl πι₁ ⟩
      π₁ ∘ ι₁ ∘ (π₁ ∘ ι₂) ∘ f         ≡˘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc _ _ _ ∙ (refl⟩∘⟨ π₂∘⟨⟩) ⟩
      π₁ ∘ ι₁ ∘ π₁ ∘ ι₂ ∘ π₂ ∘ h      ≡⟨ refl⟩∘⟨ pulll4 ιπ-comm ⟩
      π₁ ∘ (ι₂ ∘ π₂ ∘ ι₁ ∘ π₁) ∘ h    ≡⟨ refl⟩∘⟨ pullr (pullr (pullr π₁∘⟨⟩)) ⟩
      π₁ ∘ ι₂ ∘ π₂ ∘ ι₁ ∘ π₁ ∘ ι₂ ∘ g ≡˘⟨ refl⟩∘⟨ extendl4 ιπ-comm ⟩
      π₁ ∘ ι₁ ∘ π₁ ∘ ι₂ ∘ π₂ ∘ ι₂ ∘ g ≡⟨ cancell πι₁ ⟩
      π₁ ∘ ι₂ ∘ π₂ ∘ ι₂ ∘ g           ≡⟨ pushr (refl⟩∘⟨ cancell πι₂) ⟩
      (π₁ ∘ ι₂) ∘ g                   ∎

    π₂-ι₁ = zero-unique λ f g →
      let h = ⟨ f , π₂ ∘ ι₁ ∘ g ⟩ in
      (π₂ ∘ ι₁) ∘ f                   ≡⟨ insertl πι₂ ⟩
      π₂ ∘ ι₂ ∘ (π₂ ∘ ι₁) ∘ f         ≡˘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc _ _ _ ∙ (refl⟩∘⟨ π₁∘⟨⟩) ⟩
      π₂ ∘ ι₂ ∘ π₂ ∘ ι₁ ∘ π₁ ∘ h      ≡˘⟨ refl⟩∘⟨ pushl4 ιπ-comm ⟩
      π₂ ∘ (ι₁ ∘ π₁ ∘ ι₂ ∘ π₂) ∘ h    ≡⟨ refl⟩∘⟨ pullr (pullr (pullr π₂∘⟨⟩)) ⟩
      π₂ ∘ ι₁ ∘ π₁ ∘ ι₂ ∘ π₂ ∘ ι₁ ∘ g ≡⟨ refl⟩∘⟨ extendl4 ιπ-comm ⟩
      π₂ ∘ ι₂ ∘ π₂ ∘ ι₁ ∘ π₁ ∘ ι₁ ∘ g ≡⟨ cancell πι₂ ⟩
      π₂ ∘ ι₁ ∘ π₁ ∘ ι₁ ∘ g           ≡⟨ pushr (refl⟩∘⟨ cancell πι₁) ⟩
      (π₂ ∘ ι₁) ∘ g                   ∎
```
</details>

Next, we note that maps $f : A \oplus B \to C \oplus D$ are uniquely determined,
thanks to the universal properties of the product and coproduct, by the
four components $\pi_i \circ f \circ \iota_j$ for $i, j : \{1, 2\}$.
In other words, $f$ admits a unique *matrix representation*

$$
\begin{bmatrix}
f_{11} & f_{12} \\
f_{21} & f_{22}
\end{bmatrix}
$$

```agda
    unique-matrix
      : ∀ {a b c d} {f g : Hom (a ⊕₀ b) (c ⊕₀ d)}
      → (π₁ ∘ f ∘ ι₁ ≡ π₁ ∘ g ∘ ι₁)
      → (π₂ ∘ f ∘ ι₁ ≡ π₂ ∘ g ∘ ι₁)
      → (π₁ ∘ f ∘ ι₂ ≡ π₁ ∘ g ∘ ι₂)
      → (π₂ ∘ f ∘ ι₂ ≡ π₂ ∘ g ∘ ι₂)
      → f ≡ g
    unique-matrix p₁₁ p₁₂ p₂₁ p₂₂ = Biprod.[]-unique₂
      (Biprod.⟨⟩-unique₂ p₁₁ p₁₂ refl refl)
      (Biprod.⟨⟩-unique₂ p₂₁ p₂₂ refl refl)
      refl refl
```

This implies that $f \times_1 g$ and $f +_1 g$ are equal, as they both have
the same matrix representation:

$$
\begin{bmatrix}
\mathrm{id} & 0 \\
0 & \mathrm{id}
\end{bmatrix}
$$

```agda
    ⊕₁≡⊗₁ : ∀ {a b c d} {f : Hom a b} {g : Hom c d} → f ⊕₁ g ≡ f ⊗₁ g
    ⊕₁≡⊗₁ = unique-matrix
      ((refl⟩∘⟨ []∘ι₁) ∙ cancell πι₁ ∙ sym (pulll π₁∘⟨⟩ ∙ cancelr πι₁))
      ((refl⟩∘⟨ []∘ι₁) ∙ pulll π₂-ι₁ ∙ zero-∘r _ ∙ sym (pulll π₂∘⟨⟩ ∙ pullr π₂-ι₁ ∙ zero-∘l _))
      ((refl⟩∘⟨ []∘ι₂) ∙ pulll π₁-ι₂ ∙ zero-∘r _ ∙ sym (pulll π₁∘⟨⟩ ∙ pullr π₁-ι₂ ∙ zero-∘l _))
      ((refl⟩∘⟨ []∘ι₂) ∙ cancell πι₂ ∙ sym (pulll π₂∘⟨⟩ ∙ cancelr πι₂))
```

<details>
<summary>
Similarly, we show that the associators and braidings for products and
coproducts coincide.

```agda
    coassoc≡assoc : ∀ {a b c} → ⊕-assoc {a} {b} {c} ≡ ×-assoc
    coswap≡swap : ∀ {a b} → coswap {a} {b} ≡ swap
```
</summary>

```agda
    coassoc≡assoc = unique-matrix
      ((refl⟩∘⟨ []∘ι₁) ∙ cancell πι₁ ∙ sym (pulll π₁∘⟨⟩ ∙ Biprod.⟨⟩-unique₂
        (pulll π₁∘⟨⟩ ∙ πι₁)
        (pulll π₂∘⟨⟩ ∙ pullr π₂-ι₁ ∙ zero-∘l _)
        πι₁ π₂-ι₁))
      ((refl⟩∘⟨ []∘ι₁) ∙ pulll π₂-ι₁ ∙ zero-∘r _ ∙ sym (pulll π₂∘⟨⟩ ∙ pullr π₂-ι₁ ∙ zero-∘l _))
      ((refl⟩∘⟨ []∘ι₂) ∙ unique-matrix
        ((refl⟩∘⟨ pullr []∘ι₁ ∙ cancell πι₁) ∙ π₁-ι₂ ∙ sym (pulll (pulll π₁∘⟨⟩) ∙ (π₁-ι₂ ⟩∘⟨refl) ∙ zero-∘r _))
        ((refl⟩∘⟨ pullr []∘ι₁ ∙ cancell πι₁) ∙ πι₂ ∙ sym (pulll (pulll π₂∘⟨⟩) ∙ (cancelr πι₂ ⟩∘⟨refl) ∙ πι₁))
        ((refl⟩∘⟨ pullr []∘ι₂ ∙ π₁-ι₂) ∙ zero-∘l _ ∙ sym (pulll (pulll π₁∘⟨⟩) ∙ (π₁-ι₂ ⟩∘⟨refl) ∙ zero-∘r _))
        ((refl⟩∘⟨ pullr []∘ι₂ ∙ π₁-ι₂) ∙ zero-∘l _ ∙ sym (pulll (pulll π₂∘⟨⟩) ∙ (cancelr πι₂ ⟩∘⟨refl) ∙ π₁-ι₂))
      ∙ sym (pulll π₁∘⟨⟩))
      ((refl⟩∘⟨ []∘ι₂) ∙ Biprod.[]-unique₂
        (pullr []∘ι₁ ∙ pulll π₂-ι₁ ∙ zero-∘r _)
        (pullr []∘ι₂ ∙ πι₂)
        ((cancelr πι₂ ⟩∘⟨refl) ∙ π₂-ι₁)
        ((cancelr πι₂ ⟩∘⟨refl) ∙ πι₂)
      ∙ sym (pulll π₂∘⟨⟩))

    coswap≡swap = ⟨⟩-unique
      (Biprod.[]-unique₂
        (pullr []∘ι₁ ∙ π₁-ι₂) (pullr []∘ι₂ ∙ πι₁)
        π₂-ι₁ πι₂)
      (Biprod.[]-unique₂
        (pullr []∘ι₁ ∙ πι₂) (pullr []∘ι₂ ∙ π₂-ι₁)
        πι₁ π₁-ι₂)
```
</details>

We are finally ready to show that addition of morphisms is associative,
commutative and unital. These properties essentially follow from the
corresponding properties of biproducts. For associativity, we use the
following diagram:

~~~{.quiver}
\[\begin{tikzcd}
  && {(A \oplus A) \oplus A} & {(B \oplus B) \oplus B} \\
  A & {A \oplus A} &&& {B \oplus B} & B \\
  && {A \oplus (A \oplus A)} & {B \oplus (B \oplus B)}
  \arrow["{(f \oplus g) \oplus h}", from=1-3, to=1-4]
  \arrow["\alpha"', from=1-3, to=3-3]
  \arrow["{\nabla \oplus B}", from=1-4, to=2-5]
  \arrow["\alpha", from=1-4, to=3-4]
  \arrow["\delta", from=2-1, to=2-2]
  \arrow["{\delta \oplus A}", from=2-2, to=1-3]
  \arrow["{A \oplus \delta}"', from=2-2, to=3-3]
  \arrow["\nabla", from=2-5, to=2-6]
  \arrow["{f \oplus (g \oplus h)}"', from=3-3, to=3-4]
  \arrow["{B \oplus \nabla}"', from=3-4, to=2-5]
\end{tikzcd}\]
~~~

```agda
    +-assoc : ∀ {x y} {f g h : Hom x y} → f +→ (g +→ h) ≡ (f +→ g) +→ h
    +-assoc {f = f} {g} {h} =
      ∇ ∘ (f ⊗₁ (∇ ∘ (g ⊗₁ h) ∘ δ)) ∘ δ                           ≡˘⟨ refl⟩∘⟨ ⊗.pulll3 (idl _ ∙ idr _ ,ₚ refl) ⟩
      ∇ ∘ (id ⊗₁ ∇) ∘ (f ⊗₁ (g ⊗₁ h)) ∘ (id ⊗₁ δ) ∘ δ             ≡˘⟨ refl⟩∘⟨ ⊕₁≡⊗₁ ⟩∘⟨refl ⟩
      ∇ ∘ (id ⊕₁ ∇) ∘ (f ⊗₁ (g ⊗₁ h)) ∘ (id ⊗₁ δ) ∘ δ             ≡˘⟨ pushl ∇-assoc ⟩
      (∇ ∘ (∇ ⊕₁ id) ∘ ⊕-assoc) ∘ (f ⊗₁ (g ⊗₁ h)) ∘ (id ⊗₁ δ) ∘ δ ≡⟨ (refl⟩∘⟨ ⊕₁≡⊗₁ ⟩∘⟨refl) ⟩∘⟨refl ⟩
      (∇ ∘ (∇ ⊗₁ id) ∘ ⊕-assoc) ∘ (f ⊗₁ (g ⊗₁ h)) ∘ (id ⊗₁ δ) ∘ δ ≡⟨ pullr (pullr (coassoc≡assoc ⟩∘⟨refl)) ⟩
      ∇ ∘ (∇ ⊗₁ id) ∘ ×-assoc ∘ (f ⊗₁ (g ⊗₁ h)) ∘ (id ⊗₁ δ) ∘ δ   ≡⟨ refl⟩∘⟨ refl⟩∘⟨ extendl (associator .Isoⁿ.from .is-natural _ _ _) ⟩
      ∇ ∘ (∇ ⊗₁ id) ∘ ((f ⊗₁ g) ⊗₁ h) ∘ ×-assoc ∘ (id ⊗₁ δ) ∘ δ   ≡⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc-δ ⟩
      ∇ ∘ (∇ ⊗₁ id) ∘ ((f ⊗₁ g) ⊗₁ h) ∘ (δ ⊗₁ id) ∘ δ             ≡⟨ refl⟩∘⟨ ⊗.pulll3 (refl ,ₚ idl _ ∙ idr _) ⟩
      ∇ ∘ ((∇ ∘ (f ⊗₁ g) ∘ δ) ⊗₁ h) ∘ δ                           ∎
```

Commutativity follows from the following diagram, where $\beta$ is the
[[braiding]]:

~~~{.quiver}
\[\begin{tikzcd}
  & {A \oplus A} & {B \oplus B} \\
  A &&& B \\
  & {A \oplus A} & {B \oplus B}
  \arrow["{f \oplus g}", from=1-2, to=1-3]
  \arrow["\beta"', from=1-2, to=3-2]
  \arrow["\nabla", from=1-3, to=2-4]
  \arrow["\beta", from=1-3, to=3-3]
  \arrow["\delta", from=2-1, to=1-2]
  \arrow["\delta"', from=2-1, to=3-2]
  \arrow["{g \oplus f}"', from=3-2, to=3-3]
  \arrow["\nabla"', from=3-3, to=2-4]
\end{tikzcd}\]
~~~

```agda
    +-comm : ∀ {x y} {f g : Hom x y} → f +→ g ≡ g +→ f
    +-comm {f = f} {g} =
      ∇ ∘ (f ⊗₁ g) ∘ δ          ≡˘⟨ pulll ∇-coswap ⟩
      ∇ ∘ coswap ∘ (f ⊗₁ g) ∘ δ ≡⟨ refl⟩∘⟨ coswap≡swap ⟩∘⟨refl ⟩
      ∇ ∘ swap ∘ (f ⊗₁ g) ∘ δ   ≡˘⟨ refl⟩∘⟨ extendl (swap-natural _) ⟩
      ∇ ∘ (g ⊗₁ f) ∘ swap ∘ δ   ≡⟨ refl⟩∘⟨ refl⟩∘⟨ swap-δ ⟩
      ∇ ∘ (g ⊗₁ f) ∘ δ          ∎
```

Since addition is commutative, it suffices to show that the zero morphism
is a left unit. We again use the analogous property of biproducts,
which is that the [[zero object]] is a left unit for $\oplus$.

~~~{.quiver}
\[\begin{tikzcd}
  A & {A \oplus A} & {B \oplus B} & B \\
  && {0 \oplus B}
  \arrow["\delta", from=1-1, to=1-2]
  \arrow["{0 \oplus f}", from=1-2, to=1-3]
  \arrow["{! \oplus f}"', from=1-2, to=2-3]
  \arrow["\nabla", from=1-3, to=1-4]
  \arrow["{\text{\textexclamdown} \oplus B}"', from=2-3, to=1-3]
  \arrow["{\pi_2}"', from=2-3, to=1-4]
\end{tikzcd}\]
~~~

```agda
    ∇-¡l : ∀ {a} → ∇ {a} ∘ (¡ ⊕₁ id) ≡ π₂
    ∇-¡l = Biprod.[]-unique₂
      (¡-unique₂ _ _) (pullr []∘ι₂ ∙ cancell []∘ι₂)
      refl πι₂

    +-idl : ∀ {x y} {f : Hom x y} → zero→ +→ f ≡ f
    +-idl {f = f} =
      ∇ ∘ (zero→ ⊗₁ f) ∘ δ         ≡⟨ refl⟩∘⟨ ⊗.pushl (refl ,ₚ sym (idl _)) ⟩
      ∇ ∘ (¡ ⊗₁ id) ∘ (! ⊗₁ f) ∘ δ ≡˘⟨ refl⟩∘⟨ ⊕₁≡⊗₁ ⟩∘⟨refl ⟩
      ∇ ∘ (¡ ⊕₁ id) ∘ (! ⊗₁ f) ∘ δ ≡⟨ pulll ∇-¡l ⟩
      π₂ ∘ (! ⊗₁ f) ∘ δ            ≡⟨ pulll π₂∘⟨⟩ ⟩
      (f ∘ π₂) ∘ δ                 ≡⟨ cancelr π₂∘⟨⟩ ⟩
      f                            ∎

    +-idr : ∀ {x y} {f : Hom x y} → f +→ zero→ ≡ f
    +-idr = +-comm ∙ +-idl
```

Naturality of the (co)diagonals implies that composition is bilinear
with respect to our defined addition.

```agda
    ∘-linear-l
      : ∀ {a b c} {f g : Hom b c} {h : Hom a b}
      → f ∘ h +→ g ∘ h ≡ (f +→ g) ∘ h
    ∘-linear-l {f = f} {g} {h} =
      ∇ ∘ ((f ∘ h) ⊗₁ (g ∘ h)) ∘ δ ≡⟨ refl⟩∘⟨ ⊗.pushl refl ⟩
      ∇ ∘ (f ⊗₁ g) ∘ (h ⊗₁ h) ∘ δ  ≡˘⟨ pullr (pullr (δ-natural _ _ _)) ⟩
      (∇ ∘ (f ⊗₁ g) ∘ δ) ∘ h       ∎

    ∘-linear-r
      : ∀ {a b c} {f g : Hom a b} {h : Hom b c}
      → h ∘ f +→ h ∘ g ≡ h ∘ (f +→ g)
    ∘-linear-r {f = f} {g} {h} =
      ∇ ∘ ((h ∘ f) ⊗₁ (h ∘ g)) ∘ δ ≡⟨ refl⟩∘⟨ ⊗.pushl refl ⟩
      ∇ ∘ (h ⊗₁ h) ∘ (f ⊗₁ g) ∘ δ  ≡˘⟨ refl⟩∘⟨ ⊕₁≡⊗₁ ⟩∘⟨refl ⟩
      ∇ ∘ (h ⊕₁ h) ∘ (f ⊗₁ g) ∘ δ  ≡⟨ extendl (∇-natural _ _ _) ⟩
      h ∘ ∇ ∘ (f ⊗₁ g) ∘ δ         ∎
```

This provides an alternative route to defining [[additive categories]]:
instead of starting with an [[$\Ab$-enriched category]] and requiring
finite (co)products, we can start with a semiadditive category and
require that every $\hom$-monoid be a group.

In order to *construct* a semiadditive category from a category
with a [[zero object]], binary [[products]] and [[coproducts]], it
suffices to require that the map $A + B \to A \times B$ defined by
the matrix representation

$$
\begin{bmatrix}
\mathrm{id} & 0 \\
0 & \mathrm{id}
\end{bmatrix}
$$

is invertible.

```agda
  record make-semiadditive : Type (o ⊔ ℓ) where
    field
      has-zero : Zero C
      has-coprods : ∀ a b → Coproduct C a b
      has-prods : ∀ a b → Product C a b

    open Zero has-zero
    open Binary-products C has-prods
    open Binary-coproducts C has-coprods

    coproduct→product : ∀ {a b} → Hom (a ⊕₀ b) (a ⊗₀ b)
    coproduct→product = ⟨ [ id , zero→ ]
                        , [ zero→ , id ] ⟩

    field
      coproduct≅product : ∀ {a b} → is-invertible (coproduct→product {a} {b})
```

If that is the case, then the coproduct $A + B$ is a biproduct
when equipped with the projections $[\id, 0]$ and $[0, \id]$.

```agda
    has-biproducts : ∀ {a b} → Biproduct a b
    has-biproducts {a} {b} .Biproduct.biapex = a ⊕₀ b
    has-biproducts .Biproduct.π₁ = [ id , zero→ ]
    has-biproducts .Biproduct.π₂ = [ zero→ , id ]
    has-biproducts .Biproduct.ι₁ = ι₁
    has-biproducts .Biproduct.ι₂ = ι₂
    has-biproducts .Biproduct.has-is-biproduct .is-biproduct.has-is-product =
        is-product-iso-apex coproduct≅product π₁∘⟨⟩ π₂∘⟨⟩ has-is-product
    has-biproducts .Biproduct.has-is-biproduct .is-biproduct.has-is-coproduct = has-is-coproduct
    has-biproducts .Biproduct.has-is-biproduct .is-biproduct.πι₁ = []∘ι₁
    has-biproducts .Biproduct.has-is-biproduct .is-biproduct.πι₂ = []∘ι₂
    has-biproducts .Biproduct.has-is-biproduct .is-biproduct.ιπ-comm =
      ι₁ ∘ [ id , zero→ ] ∘ ι₂ ∘ [ zero→ , id ] ≡⟨ refl⟩∘⟨ pulll []∘ι₂ ⟩
      ι₁ ∘ zero→ ∘ [ zero→ , id ]               ≡⟨ pulll (zero-∘l _) ∙ zero-∘r _ ⟩
      zero→                                     ≡˘⟨ pulll (zero-∘l _) ∙ zero-∘r _ ⟩
      ι₂ ∘ zero→ ∘ [ id , zero→ ]               ≡˘⟨ refl⟩∘⟨ pulll []∘ι₁ ⟩
      ι₂ ∘ [ zero→ , id ] ∘ ι₁ ∘ [ id , zero→ ] ∎

  open make-semiadditive

  to-semiadditive : make-semiadditive → is-semiadditive
  to-semiadditive mk .is-semiadditive.has-zero = has-zero mk
  to-semiadditive mk .is-semiadditive.has-biproducts = has-biproducts mk
```
