<!--
```agda
open import Cat.Instances.Functor
open import Cat.Instances.Product
open import Cat.Bi.Base
open import Cat.Prelude

import Cat.Functor.Bifunctor as Bifunctor
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
distinguished object $I : \cC$, the **tensor unit**. These take the
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
  λ← : ∀ {X} → Hom (Unit ⊗ X) X
  λ← = unitor-l .Cr._≅_.from .η _

  λ→ : ∀ {X} → Hom X (Unit ⊗ X)
  λ→ = unitor-l .Cr._≅_.to .η _

  ρ← : ∀ {X} → Hom (X ⊗ Unit) X
  ρ← = unitor-r .Cr._≅_.from .η _

  ρ→ : ∀ {X} → Hom X (X ⊗ Unit)
  ρ→ = unitor-r .Cr._≅_.to .η _

  α→ : ∀ A B C → Hom ((A ⊗ B) ⊗ C) (A ⊗ (B ⊗ C))
  α→ _ _ _ = associator .Cr._≅_.to .η _

  α← : ∀ A B C → Hom (A ⊗ (B ⊗ C)) ((A ⊗ B) ⊗ C)
  α← _ _ _ = associator .Cr._≅_.from .η _

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

~~~{.quiver .tall-1}
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
    ni .eta _ = B.α→ _ _ _
    ni .inv _ = B.α← _ _ _
    ni .eta∘inv _ = Cr.invl _ B.associator ηₚ _
    ni .inv∘eta _ = Cr.invr _ B.associator ηₚ _
    ni .natural x y f = sym $ Cr.to B.associator .is-natural _ _ _
  mon .triangle = B.triangle _ _
  mon .pentagon = B.pentagon _ _ _ _
```
