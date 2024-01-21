---
description: |
  We prove some basic facts about what classes of functors preserve epis,
  monos, etc.
---
<!--
```agda
open import Cat.Functor.Properties
open import Cat.Morphism.Duality
open import Cat.Functor.Adjoint
open import Cat.Prelude

import Cat.Functor.Reasoning
import Cat.Reasoning
```
-->

```agda
module Cat.Functor.Morphism
  {o ℓ o' ℓ'}
  {𝒞 : Precategory o ℓ} {𝒟 : Precategory o' ℓ'}
  (F : Functor 𝒞 𝒟)
  where
```

<!--
```agda
private
  module 𝒞 = Cat.Reasoning 𝒞
  module 𝒟 = Cat.Reasoning 𝒟
open Cat.Functor.Reasoning F public

private variable
  A B C : 𝒞.Ob
  a b c d : 𝒞.Hom A B
  X Y Z : 𝒟.Ob
  f g h i : 𝒟.Hom X Y
```
-->

# Actions of functors on morphisms

This module describes how various classes of functors act
on designated collections of morphisms.

## Faithful functors

[[Faithful functors]] reflect [[monomorphisms]] and [[epimorphisms]].
We shall only prove this for monomorphisms, as the proof for epis is
identical. Let $F(a)$ be monic in $\cD$, and let $b, c$ be a pair of
morphisms in $\cC$ such that $a \circ b = a \circ c$. $F$ preserves
all commutative diagrams, so $F(a) \circ F(b) = F(a) \circ F(c)$.
$F(a)$ is monic, so $F(b) = F(c)$. Finally, $F$ is faithful, so we
can deduce $b = c$.

```agda
module _ (faithful : is-faithful F) where
  faithful→reflects-mono : 𝒟.is-monic (F₁ a) → 𝒞.is-monic a
  faithful→reflects-mono {a = a} F[a]-monic b c p =
    faithful (F[a]-monic (F₁ b) (F₁ c) (weave p))

  faithful→reflects-epi : 𝒟.is-epic (F₁ a) → 𝒞.is-epic a
  faithful→reflects-epi {a = a} F[a]-epic b c p =
    faithful (F[a]-epic (F₁ b) (F₁ c) (weave p))
```

Likewise, faithful functors reflect all diagrams: this means that if $F(a)$ and $F(b)$
either form a section/retract pair or form an iso, then $a$ and $b$ do too.

```agda
  faithful→reflects-section-of : (F₁ a) 𝒟.section-of (F₁ b) → a 𝒞.section-of b
  faithful→reflects-section-of p = faithful (F-∘ _ _ ∙ p ∙ sym F-id)

  faithful→reflects-retract-of : (F₁ a) 𝒟.retract-of (F₁ b) → a 𝒞.retract-of b
  faithful→reflects-retract-of p = faithful→reflects-section-of p

  faithful→reflects-inverses : 𝒟.Inverses (F₁ a) (F₁ b) → 𝒞.Inverses a b
  faithful→reflects-inverses ab-inv .𝒞.Inverses.invl =
    faithful→reflects-section-of (𝒟.Inverses.invl ab-inv)
  faithful→reflects-inverses ab-inv .𝒞.Inverses.invr =
    faithful→reflects-section-of (𝒟.Inverses.invr ab-inv)
```

## Fully faithful, essentially surjective functors

If a functor $F$ is [[fully faithful]] and [[essentially surjective]], then
it preserves all mono and epimorphisms. Recall that this is a slightly
weaker condition on $F$ than being an [[equivalence of categories]] as both
the domain and codomain categories are only precategories.

Let $a : \cC(A,B)$ be a mono, and let $f, g : \cD(X,F(A))$ be a pair
of morphisms in $\cD$ such that $F(a) \circ f = F(a) \circ g$.
$F$ is eso, so there merely exists a $C : \cC$ with $i : F(C) \iso X$.
Furthermore, $F$ is full: this means that there must merely exist
a pair of morphisms $f', g' : \cC(C,A)$ such that $F(f') = f \circ i$
and $F(g') = g \circ i$.


```agda
module _ (ff : is-fully-faithful F) (eso : is-eso F) where
  ff+eso→preserves-mono : 𝒞.is-monic a → 𝒟.is-monic (F₁ a)
  ff+eso→preserves-mono {a = a} a-monic {x} f g p = ∥-∥-proj! do
    (x* , i) ← eso x
    (f* , q) ← fully-faithful→full {F = F} ff (f 𝒟.∘ 𝒟.to i)
    (g* , r) ← fully-faithful→full {F = F} ff (g 𝒟.∘ 𝒟.to i)
```

Next, note that $a \circ f' = a \circ g'$: this follows from faithfulness
of $F$ and our hypothesis that $F(a) \circ f = F(a) \circ g$.

```agda
    let s =
          fully-faithful→faithful {F = F} ff $
          F₁ (a 𝒞.∘ f*)           ≡⟨ F-∘ _ _ ∙ 𝒟.pushr q ⟩
          (F₁ a 𝒟.∘ f) 𝒟.∘ 𝒟.to i ≡⟨ ap₂ 𝒟._∘_ p refl ⟩
          (F₁ a 𝒟.∘ g) 𝒟.∘ 𝒟.to i ≡⟨ 𝒟.pullr (sym r) ∙ sym (F-∘ _ _) ⟩
          F₁ (a 𝒞.∘ g*)           ∎
```

To wrap things up, recall $a$ is monic, so $f' = g'$, and $F(f') = F(g')$.
However, $F(f') = f \circ i$ and $F(g') = g \circ i$ by definition, so we
can deduce that $f \circ i = g \circ i$. Finally, isomorphisms are epis,
so we can left-cancel to conclude that $f = g$.

```agda
    pure $ 𝒟.iso→epic i f g $
      f 𝒟.∘ 𝒟.to i ≡˘⟨ q ⟩
      F₁ f*        ≡⟨ ap F₁ (a-monic f* g* s) ⟩
      F₁ g*        ≡⟨ r ⟩
      g 𝒟.∘ 𝒟.to i ∎
```

As mentioned earlier, a similar result holds for epis.

```agda
  ff+eso→preserves-epi : 𝒞.is-epic a → 𝒟.is-epic (F₁ a)
```

<details>
<summary>The proof is dual to the one for monos, so we omit it.
</summary>

```agda
  ff+eso→preserves-epi {a = a} a-epic {x} f g p = ∥-∥-proj! do
    (x* , i) ← eso x
    (f* , q) ← fully-faithful→full {F = F} ff (𝒟.from i 𝒟.∘ f)
    (g* , r) ← fully-faithful→full {F = F} ff (𝒟.from i 𝒟.∘ g)
    let s = F-∘ _ _ ∙ 𝒟.pushl q ∙ ap₂ 𝒟._∘_ refl p ∙ 𝒟.pulll (sym r) ∙ sym (F-∘ _ _)
    pure $ 𝒟.iso→monic (i 𝒟.Iso⁻¹) f g $
      sym q
      ·· ap F₁ (a-epic f* g* (fully-faithful→faithful {F = F} ff s))
      ·· r
```
</details>

## Left and right adjoints

If $F$ is a [[right adjoint]], then $F$ preserves monos. Let $a : \cC(A,B)$,
and let $f, g : \cD(X, F(A))$ such that $F(a) \circ f = F(a) \circ g$.
$L$ is a left adjoint to $F$, so it suffices to show that $\eps \circ L(f) = \eps \circ L(g)$.
Furthermore, $a$ is a mono, so it suffices to show that $a \circ \eps \circ L(f) = a \circ \eps \circ L(g)$.
This follows by a quick calculation.

```agda
module _ {L : Functor 𝒟 𝒞} (L⊣F : L ⊣ F) where
  private
    module L = Cat.Functor.Reasoning L
  open _⊣_ L⊣F

  right-adjoint→preserves-monos : 𝒞.is-monic a → 𝒟.is-monic (F₁ a)
  right-adjoint→preserves-monos {a = a} a-monic f g p =
    Equiv.injective (_ , R-adjunct-is-equiv L⊣F) $
    a-monic _ _ $
    a 𝒞.∘ counit.ε _ 𝒞.∘ L.₁ f            ≡⟨ 𝒞.pulll (sym (counit.is-natural _ _ _)) ⟩
    (counit.ε _ 𝒞.∘ L.₁ (F₁ a)) 𝒞.∘ L.₁ f ≡⟨ L.extendr p ⟩
    (counit.ε _ 𝒞.∘ L.₁ (F₁ a)) 𝒞.∘ L.₁ g ≡⟨ 𝒞.pushl (counit.is-natural _ _ _) ⟩
    a 𝒞.∘ counit.ε _ 𝒞.∘ L.₁ g            ∎
```

A similar result holds for epis when $F$ is a [[left adjoint]].

```agda
module _ {R : Functor 𝒟 𝒞} (F⊣R : F ⊣ R) where
  private
    module R = Cat.Functor.Reasoning R
  open _⊣_ F⊣R

  left-adjoint→preserves-epis : 𝒞.is-epic a → 𝒟.is-epic (F₁ a)
```

<details>
<summary>The proof is dual to the right adjoint case, so we omit it.
</summary>
```agda
  left-adjoint→preserves-epis {a = a} a-epic f g p =
    Equiv.injective (_ , L-adjunct-is-equiv F⊣R) $
    a-epic _ _ $
    𝒞.pullr (unit.is-natural _ _ _)
    ∙ R.extendl p
    ∙ 𝒞.pushr (sym (unit.is-natural _ _ _))
```
</details>
