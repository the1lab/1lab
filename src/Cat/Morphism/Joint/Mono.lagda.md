---
description: |
  Joint monomorphisms.
---
<!--
```agda
open import Cat.Diagram.Product.Indexed
open import Cat.Diagram.Product
open import Cat.Prelude

import Cat.Reasoning
```
-->
```agda
module Cat.Morphism.Joint.Mono {o ℓ} (C : Precategory o ℓ) where
```

<!--
```agda
open Cat.Reasoning C
```
-->

# Joint monomorphisms {defines="joint-monomorphism"}

:::{.definition #jointly-monic}
A pair of morphisms $f : \cC(X,Y)$ and $g : \cC(X,Z)$ are **jointly monic**
if for every $h, k : \cC(A,X)$, $h = k$ if $f \circ h = f \circ k$ and
$g \circ h = g \circ k$.
:::

```agda
is-jointly-monic : ∀ {x y z} → Hom x y → Hom x z → Type (o ⊔ ℓ)
is-jointly-monic {x = x} f g =
  ∀ {a} → (h k : Hom a x) → f ∘ h ≡ f ∘ k → g ∘ h ≡ g ∘ k → h ≡ k
```

:::{.definition #jointly-monic-family}
More genererally, an $I$-indexed family of morphisms $f_{i} : \cC(X, Y_{i})$
is a **jointly monic family** if for every $h, k : \cC(A,X)$, $h = k$ if
$f_{i} \circ h = f_{i} \circ k$ for every $i : I$.
:::

```agda
is-jointly-monic-fam
  : ∀ {ℓ'} {I : Type ℓ'}
  → {x : Ob} {yᵢ : I → Ob}
  → (fᵢ : ∀ i → Hom x (yᵢ i))
  → Type (o ⊔ ℓ ⊔ ℓ')
is-jointly-monic-fam {x = x} fᵢ =
  ∀ {a} → (h k : Hom a x) → (∀ i → fᵢ i ∘ h ≡ fᵢ i ∘ k) → h ≡ k
```

## Joint monomorphisms and products

If $\cC$ has [[products]], then a pair of morphisms $f : \cC(X,Y)$, $g : \cC(X,Z)$
is jointly monic if and only if $\langle f , g \rangle : \cC(X,Y \times Z)$
is [[monic]].

```agda
module _ (all-products : has-products C) where
  open Binary-products C all-products
```

The forward direction follows from a short calculation.

```agda
  ⟨⟩-monic→jointly-monic
    : ∀ {x y z} {f : Hom x y} {g : Hom x z}
    → is-monic ⟨ f , g ⟩
    → is-jointly-monic f g
  ⟨⟩-monic→jointly-monic {f = f} {g = g} ⟨f,g⟩-mono h k p q =
    ⟨f,g⟩-mono h k $
      ⟨ f , g ⟩ ∘ h     ≡⟨ ⟨⟩∘ h ⟩
      ⟨ f ∘ h , g ∘ h ⟩ ≡⟨ ap₂ ⟨_,_⟩ p q ⟩
      ⟨ f ∘ k , g ∘ k ⟩ ≡˘⟨ ⟨⟩∘ k ⟩
      ⟨ f , g ⟩ ∘ k     ∎
```

The reverse direction is a bit tricker, but only just. Suppose that
$f, g$ are jointly monic, and let $h, k : \cC(A,X)$ such that:

$$\langle f , g \rangle \circ h = \rangle f , g \langle \circ k$$

Our goal is to show that $h = k$. As $f$ and $g$ are jointly monic,
it suffices to show that $f \circ h = f \circ k$ and $g \circ h = g \circ k$.
We can re-arrange our hypothesis to deduce that

$$\langle f \circ h , g \circ h \rangle = \langle f \circ k , g \circ k \rangle$$

We can then apply first and second projections to this equation, which
lets us deduce that $f \circ h = f \circ k$ and $g \circ h = g \circ k$.

```agda
  jointly-monic→⟨⟩-monic
    : ∀ {x y z} {f : Hom x y} {g : Hom x z}
    → is-jointly-monic f g
    → is-monic ⟨ f , g ⟩
  jointly-monic→⟨⟩-monic {f = f} {g = g} fg-joint-mono h k p =
    fg-joint-mono h k (by-π₁ ⟨fh,gh⟩=⟨fk,gk⟩) (by-π₂ ⟨fh,gh⟩=⟨fk,gk⟩)
    where
      ⟨fh,gh⟩=⟨fk,gk⟩ : ⟨ f ∘ h , g ∘ h ⟩ ≡ ⟨ f ∘ k , g ∘ k ⟩
      ⟨fh,gh⟩=⟨fk,gk⟩ =
        ⟨ f ∘ h , g ∘ h ⟩ ≡˘⟨ ⟨⟩∘ h ⟩
        ⟨ f , g ⟩ ∘ h     ≡⟨ p ⟩
        ⟨ f , g ⟩ ∘ k     ≡⟨ ⟨⟩∘ k ⟩
        ⟨ f ∘ k , g ∘ k ⟩ ∎
```

This result provides the main motivation for joint monomorphisms: they
let us talk about monomorphisms into products, even when we don't have
products.

Joint monos are also slightly more ergonomic than monos into products.
Typically, if we want to prove that some $R \mono X \times Y$ is monic,
then our first step is to invoke the universal property of $R$: joint
monos factor out this first step into the definition!

## Jointly monic families and indexed products

We can obtain a similar result for jointly monic families and [[indexed products]]:
if $\cC$ has $I$-indexed products, then a family of morphisms $f_{i} : \cC(X, Y_{i})$
is jointly monic if and only if the universal map $\prod f_{i} : \cC(X, \prod Y_{i})$
is monic.

```agda
module _ {ℓ} {I : Type ℓ} (indexed-products : has-products-indexed-by C I) where
  private module ∏ {xᵢ : I → Ob} = Indexed-product (indexed-products xᵢ)

  tuple-monic→jointy-monic-fam
    : ∀ {x} {yᵢ : I → Ob}
    → {fᵢ : ∀ i → Hom x (yᵢ i)}
    → is-monic (∏.tuple fᵢ)
    → is-jointly-monic-fam fᵢ

  jointy-monic-fam→tuple-monic
    : ∀ {x} {yᵢ : I → Ob}
    → {fᵢ : ∀ i → Hom x (yᵢ i)}
    → is-jointly-monic-fam fᵢ
    → is-monic (∏.tuple fᵢ)
```

<details>
<summary>The proofs are almost identical to the non-indexed case, so we
omit the details in the interest of brevity.
</summary>

```agda
  tuple-monic→jointy-monic-fam {yᵢ = yᵢ} {fᵢ = fᵢ} tuple-mono h k p =
    tuple-mono h k $
      ∏.tuple fᵢ ∘ h           ≡⟨ tuple∘ C yᵢ (indexed-products yᵢ) fᵢ ⟩
      ∏.tuple (λ i → fᵢ i ∘ h) ≡⟨ ap ∏.tuple (funext p) ⟩
      ∏.tuple (λ i → fᵢ i ∘ k) ≡˘⟨ tuple∘ C yᵢ (indexed-products yᵢ) fᵢ ⟩
      ∏.tuple fᵢ ∘ k           ∎

  jointy-monic-fam→tuple-monic {yᵢ = yᵢ} {fᵢ = fᵢ} fᵢ-joint-mono h k p =
    fᵢ-joint-mono h k λ i →
      fᵢ i ∘ h               ≡⟨ pushl (sym ∏.commute) ⟩
      ∏.π i ∘ ∏.tuple fᵢ ∘ h ≡⟨ ap (∏.π i ∘_) p ⟩
      ∏.π i ∘ ∏.tuple fᵢ ∘ k ≡⟨ pulll ∏.commute ⟩
      fᵢ i ∘ k               ∎
```
</details>

## Joint monos as relations

In the previous section we proved that in the presence of products,
joint monomorphisms $X \ot R \to Y$ are equivalent to monos $R \to X \times Y$.
When viewed as a [[subobject]], a mono $R \to X \times Y$ gives us a
categorical notion of a binary relation, so we can take the same perspective
on joint monos! More generally, we can view an $I$-indexed jointly monic family
as an $I$-ary relation.

This has the nice technical benefit of being able to
talk about relations in categories that lack products (though such
relations tend to be rather poorly behaved).

## Closure properties of joint monos

If $f, g$ are jointly monic and $h$ is monic, then
$f \circ h$ and $g \circ h$ are jointly monic.

```agda
jointly-monic-∘
  : ∀ {w x y z} {f : Hom x y} {g : Hom x z} {h : Hom w x}
  → is-jointly-monic f g
  → is-monic h
  → is-jointly-monic (f ∘ h) (g ∘ h)
jointly-monic-∘ {h = h} fg-joint-mono h-mono k₁ k₂ p q =
  h-mono k₁ k₂ $
  fg-joint-mono (h ∘ k₁) (h ∘ k₂)
    (assoc _ _ _ ·· p ·· sym (assoc _ _ _))
    (assoc _ _ _ ·· q ·· sym (assoc _ _ _))
```

Moreover, if $f \circ h$ and $g \circ h$ are jointly monic, then
$h$ is monic.

```agda
jointly-monic-cancell
  : ∀ {w x y z} {f : Hom x y} {g : Hom x z} {h : Hom w x}
  → is-jointly-monic (f ∘ h) (g ∘ h)
  → is-monic h
jointly-monic-cancell fgh-joint-mono k₁ k₂ p =
  fgh-joint-mono k₁ k₂ (extendr p) (extendr p)
```

We get a similar pair of results for jointly monic families.

```agda
jointly-monic-fam-∘
  : ∀ {ℓ} {I : Type ℓ} {x y} {zᵢ : I → Ob}
  → {fᵢ : ∀ i → Hom y (zᵢ i)} {g : Hom x y}
  → is-jointly-monic-fam fᵢ
  → is-monic g
  → is-jointly-monic-fam (λ i → fᵢ i ∘ g)
jointly-monic-fam-∘ {g = g} fᵢ-joint-mono g-mono k₁ k₂ p =
  g-mono k₁ k₂ $
  fᵢ-joint-mono (g ∘ k₁) (g ∘ k₂) λ i →
    assoc _ _ _ ·· p i ·· sym (assoc _ _ _)

jointly-monic-fam-cancell
  : ∀ {ℓ} {I : Type ℓ} {x y} {zᵢ : I → Ob}
  → {fᵢ : ∀ i → Hom y (zᵢ i)} {g : Hom x y}
  → is-jointly-monic-fam (λ i → fᵢ i ∘ g)
  → is-monic g
jointly-monic-fam-cancell fᵢg-joint-mono k₁ k₂ p =
  fᵢg-joint-mono k₁ k₂ λ i → extendr p
```

If either of $f : \cC(X,Y)$ or $g : \cC(X,Z)$ are monic, then
$f$ and $g$ are jointly monic.

```agda
left-monic→jointly-monic
  : ∀ {x y z} {f : Hom x y} {g : Hom x z}
  → is-monic f
  → is-jointly-monic f g
left-monic→jointly-monic f-mono k₁ k₂ p q =
  f-mono k₁ k₂ p

right-monic→jointly-monic
  : ∀ {x y z} {f : Hom x y} {g : Hom x z}
  → is-monic g
  → is-jointly-monic f g
right-monic→jointly-monic g-mono k₁ k₂ p q =
  g-mono k₁ k₂ q
```

Similarly, if any component of a family of maps $f_{i} : \cC(X,Y_{i})$
is monic, then $f_{i}$ is a jointly monic family.

```agda
monic→jointly-monic-fam
  : ∀ {ℓ} {I : Type ℓ} {x} {yᵢ : I → Ob}
  → {fᵢ : ∀ i → Hom x (yᵢ i)}
  → (i : I) → is-monic (fᵢ i)
  → is-jointly-monic-fam fᵢ
monic→jointly-monic-fam i fᵢ-monic k₁ k₂ p =
  fᵢ-monic k₁ k₂ (p i)
```

If $f$ is jointly monic with itself, then $f$ is monic. Moreover, if
the constant family $\lam i \to f$ is jointly monic, then $f$ is monic.

```agda
self-jointly-monic→monic
  : ∀ {x y} {f : Hom x y}
  → is-jointly-monic f f
  → is-monic f
self-jointly-monic→monic f-joint-monic k₁ k₂ p =
  f-joint-monic k₁ k₂ p p

self-jointly-monic-fam→monic
  : ∀ {ℓ'} {I : Type ℓ'} {x y} {f : Hom x y}
  → is-jointly-monic-fam (λ (i : I) → f)
  → is-monic f
self-jointly-monic-fam→monic f-joint-mono k₁ k₂ p =
  f-joint-mono k₁ k₂ (λ _ → p)
```

## Miscellaneous properties of joint monos

If $f : \cC(X,Y)$ and $g : \cC(X,Z)$ are jointly monic, then the
map $\cC(A,X) \to \cC(A,Y) \times \cC(A,Z)$ induced by postcompositon
is an [[embedding]].

```agda
jointly-monic-postcomp-embedding
  : ∀ {w x y z} {f : Hom x y} {g : Hom x z}
  → is-jointly-monic f g
  → is-embedding {B = Hom w y × Hom w z} (λ h → f ∘ h , g ∘ h)
jointly-monic-postcomp-embedding fg-joint-mono =
  injective→is-embedding! λ {k₁} {k₂} p →
    fg-joint-mono k₁ k₂ (ap fst p) (ap snd p)
```

If $f_{i} : \cC(X,Y_{i})$ is an $I$-indexed jointly monic family, then
the map $\cC(A,X) \to ((i : I) \to \cC(A,Y_{i}))$ induced by postcomposition
is an embedding.

```agda
jointly-monic-fam-postcomp-embedding
  : ∀ {ℓ} {I : Type ℓ} {x y} {zᵢ : I → Ob}
  → {fᵢ : ∀ i → Hom y (zᵢ i)}
  → is-jointly-monic-fam fᵢ
  → is-embedding {B = (i : I) → Hom x (zᵢ i)} (λ g i → fᵢ i ∘ g)
jointly-monic-fam-postcomp-embedding fᵢ-joint-mono =
  injective→is-embedding! λ {k₁} {k₂} p →
    fᵢ-joint-mono k₁ k₂ (apply p)
```