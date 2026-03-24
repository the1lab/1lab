<!--
```agda
open import Cat.Instances.Functor
open import Cat.Instances.Product
open import Cat.Bi.Base
open import Cat.Prelude

import Cat.Functor.Bifunctor as Bifunctor
import Cat.Functor.Reasoning as Fr
import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Monoidal.Base where
```

<!--
```agda
open _=>_
```
-->

# Monoidal categories {defines="monoidal-category"}

```agda
record Monoidal-category {o ℓ} (C : Precategory o ℓ) : Type (o ⊔ ℓ) where
  no-eta-equality
  open Cr C
```

A **monoidal category** is a vertical categorification of the concept of
[_monoid_]: We replace the identities in a monoid by isomorphisms. For
this to make sense, a monoidal category must have an underlying
[precategory], rather than an underlying set; Similarly, the
multiplication operation must be a multiplication _functor_, and we have
to throw on some coherence data on top, to make sure everything works
out.

[_monoid_]: Algebra.Monoid.html
[precategory]: Cat.Base.html

We start with a category $\cC$ together with a chosen functor, the
**tensor product**, $\otimes : \cC \times \cC \to \cC$, and a
distinguished object $1 : \cC$, the **tensor unit**. These take the
place of the multiplication operation and identity element,
respectively.

```agda
  field
    -⊗-  : Functor (C ×ᶜ C) C
    Unit : Ob
```

<!--
```agda
  private module -⊗- = Bifunctor -⊗-
  _⊗_ : Ob → Ob → Ob
  A ⊗ B = -⊗- .Functor.F₀ (A , B)

  _⊗₁_ : ∀ {w x y z} → Hom w x → Hom y z → Hom (w ⊗ y) (x ⊗ z)
  f ⊗₁ g = -⊗- .Functor.F₁ (f , g)

  infixr 25 _⊗_
```
-->

We replace the associativity and unit laws by
associativity and unitor _morphisms_, which are natural isomorphisms (in
components)

$$
\begin{align*}
&\alpha_{X,Y,Z} : X \otimes (Y \otimes Z) \xto{\sim} (X \otimes Y) \otimes Z \\
&\rho_{X} : X \otimes 1 \xto{\sim} X \\
&\lambda_{X} : 1 \otimes X \xto{\sim} X\text{,}
\end{align*}
$$

The morphism $\alpha$ is called the **associator**, and $\rho$ (resp.
$\lambda$) are the **right unitor** (resp. **left unitor**).

```agda
  field
    unitor-l : Cr._≅_ Cat[ C , C ] Id (-⊗-.Right Unit)
    unitor-r : Cr._≅_ Cat[ C , C ] Id (-⊗-.Left Unit)

    associator : Cr._≅_ Cat[ C ×ᶜ C ×ᶜ C , C ]
      (compose-assocˡ {O = ⊤} {H = λ _ _ → C} -⊗-)
      (compose-assocʳ {O = ⊤} {H = λ _ _ → C} -⊗-)
```

<!--
```agda
  λ≅ : ∀ {X} → X ≅ Unit ⊗ X
  λ≅ = isoⁿ→iso unitor-l _

  λ← : ∀ {X} → Hom (Unit ⊗ X) X
  λ← = unitor-l .Cr._≅_.from .η _

  λ→ : ∀ {X} → Hom X (Unit ⊗ X)
  λ→ = unitor-l .Cr._≅_.to .η _

  ρ≅ : ∀ {X} → X ≅ X ⊗ Unit
  ρ≅ = isoⁿ→iso unitor-r _

  ρ← : ∀ {X} → Hom (X ⊗ Unit) X
  ρ← = unitor-r .Cr._≅_.from .η _

  ρ→ : ∀ {X} → Hom X (X ⊗ Unit)
  ρ→ = unitor-r .Cr._≅_.to .η _

  α≅ : ∀ {A B C} → (A ⊗ B) ⊗ C ≅ A ⊗ (B ⊗ C)
  α≅ = isoⁿ→iso associator _

  α→ : ∀ A B C → Hom ((A ⊗ B) ⊗ C) (A ⊗ (B ⊗ C))
  α→ _ _ _ = associator .Cr._≅_.to .η _

  α← : ∀ A B C → Hom (A ⊗ (B ⊗ C)) ((A ⊗ B) ⊗ C)
  α← _ _ _ = associator .Cr._≅_.from .η _

  module ⊗ = Fr -⊗-
  module ▶ {A} = Fr (-⊗-.Right A)
  module ◀ {A} = Fr (-⊗-.Left A)

  -- whiskering on the right
  _▶_ : ∀ A {B C} (g : Hom B C) → Hom (A ⊗ B) (A ⊗ C)
  _▶_ A f = id ⊗₁ f

  -- whiskering on the left
  _◀_ : ∀ {A B} (g : Hom A B) C → Hom (A ⊗ C) (B ⊗ C)
  _◀_ f A = f ⊗₁ id
```
-->

The final data we need are coherences relating the left and right
unitors (the **triangle identity**; despite the name, nothing to do with
adjunctions), and one for reducing sequences of associators, the
**pentagon identity**. As for where the name "pentagon" comes from, the
path `pentagon`{.Agda} witnesses commutativity of the diagram

~~~{.quiver}
\[\begin{tikzcd}
  & {A\otimes(B\otimes(C\otimes D))} \\
  {(A\otimes B)\otimes(C\otimes D)} && {A \otimes ((B \otimes C) \otimes D)} \\
  \\
  {((A\otimes B)\otimes C)\otimes D} && {(A \otimes (B\otimes C)) \otimes D\text{,}}
  \arrow[from=4-1, to=4-3]
  \arrow[from=4-3, to=2-3]
  \arrow[from=2-3, to=1-2]
  \arrow[from=2-1, to=1-2]
  \arrow[from=4-1, to=2-1]
\end{tikzcd}\]
~~~

which we have drawn less like a regular pentagon and more like a
children's drawing of a house, so that it fits on the page horizontally.

```agda
  field
    triangle : ∀ {A B} → (ρ← ◀ B) ∘ α← A Unit B ≡ A ▶ λ←

    pentagon
      : ∀ {A B C D}
      → (α← A B C ◀ D) ∘ α← A (B ⊗ C) D ∘ (A ▶ α← B C D)
      ≡ α← (A ⊗ B) C D ∘ α← A B (C ⊗ D)
```

<!--
```agda
  triangle-α→ : ∀ {A B} → (A ▶ λ←) ∘ α→ _ _ _ ≡ ρ← ◀ B
  triangle-α→ = rswizzle (sym triangle) (α≅ .invr)

  pentagon-α→
    : ∀ {A B C D}
    → (A ▶ α→ B C D) ∘ α→ A (B ⊗ C) D ∘ (α→ A B C ◀ D)
    ≡ α→ A B (C ⊗ D) ∘ α→ (A ⊗ B) C D
  pentagon-α→ = inverse-unique₀
    (▶.F-map-iso (α≅ Iso⁻¹) ∙Iso α≅ Iso⁻¹ ∙Iso ◀.F-map-iso (α≅ Iso⁻¹))
    (α≅ Iso⁻¹ ∙Iso α≅ Iso⁻¹)
    (sym (assoc _ _ _) ∙ pentagon)
```
-->

## Deloopings

Just as a monoid can be [promoted] to a 1-object category, with the
underlying set of the monoid becoming the single $\hom$-set, we can
deloop a monoidal category into a [[bicategory]] with a single object,
where the sole $\hom$-_category_ is given by the monoidal category.

[promoted]: Cat.Instances.Delooping.html

```agda
Deloop
  : ∀ {o ℓ} {C : Precategory o ℓ} → Monoidal-category C → Prebicategory lzero o ℓ
Deloop {C = C} mon = bi where
  open Prebicategory
  module M = Monoidal-category mon
  bi : Prebicategory _ _ _
  bi .Ob = ⊤
  bi .Hom _ _ = C
  bi .id = M.Unit
  bi .compose = M.-⊗-
  bi .unitor-l = M.unitor-l
  bi .unitor-r = M.unitor-r
  bi .associator = M.associator
  bi .triangle _ _ = M.triangle
  bi .pentagon _ _ _ _ = M.pentagon
```

This makes the idea that a monoidal category is "just" the categorified
version of a monoid precisely, and it's generally called the _delooping
hypothesis_: A monoidal $n$-category is the same as an $(n+1)$-category
with a single object.

## Endomorphism categories

In the same way that, if you have a category $\cC$, making a choice
of object $a : \cC$ canonically gives you a monoid
$\rm{Endo}_\cC(a)$ of _endomorphisms_ $a \to a$, having a bicategory
$\bicat{B}$ and choosing an object $a : \bicat{B}$ canonically gives you
a choice of _monoidal category_, $\rm{Endo}_\bicat{B}(a)$.

```agda
Endomorphisms
  : ∀ {o ℓ ℓ'} (B : Prebicategory o ℓ ℓ')
  → (a : Prebicategory.Ob B)
  → Monoidal-category (Prebicategory.Hom B a a)
Endomorphisms B a = mon where
  open Monoidal-category
  module B = Prebicategory B
  mon : Monoidal-category (B.Hom a a)
  mon .-⊗- = B.compose
  mon .Unit = B.id
  mon .unitor-l = B.unitor-l
  mon .unitor-r = B.unitor-r
  mon .associator = to-natural-iso $ ni where
    open make-natural-iso
    open Cr
    ni : make-natural-iso _ _
    ni .eta _ = B.α→ _
    ni .inv _ = B.α← _
    ni .eta∘inv _ = Cr.invl _ B.associator ηₚ _
    ni .inv∘eta _ = Cr.invr _ B.associator ηₚ _
    ni .natural x y f = sym $ Cr.to B.associator .is-natural _ _ _
  mon .triangle = B.triangle _ _
  mon .pentagon = B.pentagon _ _ _ _
```

## Properties

<!--
```agda
module Monoidal {o ℓ} {C : Precategory o ℓ} (M : Monoidal-category C) where
  open Cr C
  open Monoidal-category M public
```
-->

While the `triangle`{.Agda} and `pentagon`{.Agda} identities turn out
to be sufficient to derive all the desired coherence in a monoidal
category, this is not exactly trivial. We prove a few basic identities
that follow from the axioms.

::: source
The proofs in this section are from Kelly [-@Kelly:coherence], but the
visualisation as a triangular prism takes inspiration from the previous
formalisation in [`agda-categories`](https://agda.github.io/agda-categories/Categories.Category.Monoidal.Properties.html).
:::

First, we will show that the two ways of going $1 \otimes A \otimes B
\to A \otimes B$ (using the unitor on $A$ or on $A \otimes B$) are coherent.
We do this by pasting isomorphisms together to form a triangular prism
with given sides and lid, as in the following diagram:

~~~{.quiver}
\[\begin{tikzcd}
  & {((1 \otimes 1) \otimes A)\otimes B} \\
  {(1 \otimes (1 \otimes A))\otimes B} & {(1 \otimes 1)\otimes (A \otimes B)} & {(1 \otimes A)\otimes B} \\
  & {1 \otimes (1 \otimes (A\otimes B))} \\
  {1\otimes((1\otimes A)\otimes B)} && {1\otimes (A\otimes B)}
  \arrow["{1 \otimes (\lambda \otimes B)}"', from=4-1, to=4-3]
  \arrow["\alpha", from=2-1, to=4-1]
  \arrow["\alpha"', from=2-3, to=4-3]
  \arrow["{(1 \otimes \lambda)\otimes B}"'{pos=0.2}, curve={height=6pt}, from=2-1, to=2-3]
  \arrow["{1 \otimes \alpha}"', dashed, from=4-1, to=3-2]
  \arrow["{1 \otimes \lambda}"', dashed, from=3-2, to=4-3]
  \arrow["{\alpha^{-1}\otimes B}", from=2-1, to=1-2]
  \arrow["{(\rho\otimes A)\otimes B}", from=1-2, to=2-3]
  \arrow["\alpha", dashed, from=1-2, to=2-2]
  \arrow["\alpha", dashed, from=2-2, to=3-2]
\end{tikzcd}\]
~~~

We obtain the commutativity of the bottom triangle, which yields the
desired equation since $1 \otimes -$ is an equivalence.

```agda
  triangle-λ← : ∀ {A B} → λ← ∘ α→ Unit A B ≡ λ← ⊗₁ id
  triangle-λ← {A} {B} = push-eqⁿ (unitor-l ni⁻¹) $
    ▶.F-∘ _ _ ∙ ap to (Iso-prism base sq1 sq2 sq3)
    where
      base : ◀.F-map-iso (α≅ Iso⁻¹) ∙Iso ◀.F-map-iso (◀.F-map-iso (ρ≅ Iso⁻¹))
           ≡ ◀.F-map-iso (▶.F-map-iso (λ≅ Iso⁻¹))
      base = ≅-path (◀.collapse triangle)

      sq1 : ◀.F-map-iso (α≅ Iso⁻¹) ∙Iso α≅ ∙Iso α≅ ≡ α≅ ∙Iso ▶.F-map-iso α≅
      sq1 = ≅-path (rswizzle (sym pentagon-α→ ∙ assoc _ _ _)
        (◀.annihilate (α≅ .invl)))

      sq2 : ◀.F-map-iso (◀.F-map-iso (ρ≅ Iso⁻¹)) ∙Iso α≅
          ≡ (α≅ ∙Iso α≅) ∙Iso ▶.F-map-iso (λ≅ Iso⁻¹)
      sq2 = ≅-path $
        α→ _ _ _ ∘ ((ρ← ⊗₁ id) ⊗₁ id)    ≡⟨ associator .Isoⁿ.to .is-natural _ _ _ ⟩
        (ρ← ⊗₁ ⌜ id ⊗₁ id ⌝) ∘ α→ _ _ _  ≡⟨ ap! ⊗.F-id ⟩
        (ρ← ⊗₁ id) ∘ α→ _ _ _            ≡˘⟨ pulll triangle-α→ ⟩
        (id ⊗₁ λ←) ∘ α→ _ _ _ ∘ α→ _ _ _ ∎

      sq3 : ◀.F-map-iso (▶.F-map-iso (λ≅ Iso⁻¹)) ∙Iso α≅
          ≡ α≅ ∙Iso ▶.F-map-iso (◀.F-map-iso (λ≅ Iso⁻¹))
      sq3 = ≅-path (associator .Isoⁿ.to .is-natural _ _ _)
```

As a consequence, we get that the two unitors $1 \otimes 1 \to 1$ agree:

```agda
  λ≡ρ : λ← {Unit} ≡ ρ← {Unit}
  λ≡ρ = push-eqⁿ (unitor-r ni⁻¹) $
    (λ← ⊗₁ id)            ≡˘⟨ triangle-λ← ⟩
    λ← ∘ α→ _ _ _         ≡⟨ (insertl (λ≅ .invl) ∙∙ refl⟩∘⟨ sym (unitor-l .Isoⁿ.from .is-natural _ _ _) ∙∙ cancell (λ≅ .invl)) ⟩∘⟨refl ⟩
    (id ⊗₁ λ←) ∘ α→ _ _ _ ≡⟨ triangle-α→ ⟩
    (ρ← ⊗₁ id)            ∎
```
